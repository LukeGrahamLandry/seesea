//! IR -> LLVM IR

use crate::ast::{BinaryOp, CType, FuncSignature, ValueType};
use crate::ir;
use crate::ir::{Function, Label, Op, Ssa};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::{Context, ContextRef};
use inkwell::execution_engine::{ExecutionEngine, JitFunction, UnsafeFunctionPointer};
use inkwell::module::Module;
use inkwell::types::{AnyTypeEnum, BasicType, BasicTypeEnum, FunctionType};
use inkwell::values::{
    AnyValue, AnyValueEnum, BasicMetadataValueEnum, BasicValueEnum, FunctionValue, IntValue,
    PointerValue,
};
use inkwell::{AddressSpace, IntPredicate};
use std::collections::HashMap;

pub struct LlvmFuncGen<'ctx: 'module, 'module> {
    context: ContextRef<'ctx>,
    module: &'module Module<'ctx>,
    builder: Builder<'ctx>,
    functions: HashMap<String, FunctionValue<'ctx>>,
    func: Option<FuncContext<'ctx, 'module>>,
}

/// Plain old data that holds the state that must be reset for each function.
struct FuncContext<'ctx: 'module, 'module> {
    local_registers: HashMap<Ssa, AnyValueEnum<'ctx>>,
    blocks: Vec<BasicBlock<'ctx>>,
    func_ir: &'module Function,
}

impl<'ctx: 'module, 'module> LlvmFuncGen<'ctx, 'module> {
    pub fn new(module: &'module Module<'ctx>) -> LlvmFuncGen<'ctx, 'module> {
        LlvmFuncGen {
            context: module.get_context(),
            module,
            builder: module.get_context().create_builder(),
            functions: Default::default(),
            func: None,
        }
    }

    /// To access the results, use an execution engine created on the LLVM Module.
    pub fn compile_all(&mut self, ir: &'module ir::Module) {
        for function in &ir.functions {
            self.emit_function(function);
        }
        self.module.verify().unwrap();
    }

    fn emit_function(&mut self, ir: &'module Function) {
        self.func = Some(FuncContext::new(ir));
        let t = self.get_func_type(&ir.signature);
        let func = self
            .module
            .add_function(ir.signature.name.as_str(), t, None);
        self.functions.insert(ir.signature.name.clone(), func);

        // All the blocks need to exist ahead of time so jumps can reference them.
        self.func_mut().blocks = ir
            .blocks
            .iter()
            .enumerate()
            .map(|(i, _)| self.context.append_basic_block(func, &format!(".b{}", i)))
            .collect();

        // Map the llvm function arguments to our ssa register system.
        for (i, register) in ir.arg_registers.iter().enumerate() {
            let param = func
                .get_nth_param(i as u32)
                .expect("LLVM func arg count must match signature.");
            self.set(register, param);
        }

        // Compile the body of the function.
        for (i, block) in ir.blocks.iter().enumerate() {
            let code = self.func_get().blocks[i];
            self.builder.position_at_end(code);

            // TODO: get rid of garbage blocks before it gets to llvm.
            //       but it crashes with invalid blocks that don't jump anywhere so temp fix.
            //       llvm optimises it out anyway.
            if block.is_empty() {
                println!("Made empty block in LLVM.");
                let garbage = self.context.i64_type().const_int(3141592, false);
                self.builder.build_return(Some(&garbage));
                continue;
            }

            for op in block {
                self.emit_ir_op(op);
            }
        }

        self.func = None;
    }

    fn emit_ir_op(&mut self, op: &Op) {
        match op {
            Op::ConstInt { dest, value } => {
                let number = self.llvm_type(CType::int()).into_int_type();
                let val = number.const_int(*value, false);
                self.set(dest, val);
            }
            Op::Binary { dest, a, b, kind } => self.emit_binary_op(dest, a, b, *kind),
            Op::Return { value } => {
                self.emit_return(value);
            }
            Op::AlwaysJump(target) => {
                // TODO: factor out a FunctionBuilder that gives you type safety over these index -> block conversions.
                self.builder.build_unconditional_branch(self.block(*target));
            }
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => {
                self.builder.build_conditional_branch(
                    self.read_int(condition),
                    self.block(*if_true),
                    self.block(*if_false),
                );
            }
            Op::Phi { dest, a, b } => {
                let phi = self.builder.build_phi(self.reg_basic_type(&a.1), "");
                phi.add_incoming(&[
                    (&self.read_basic_value(&a.1), self.block(a.0)),
                    (&self.read_basic_value(&b.1), self.block(b.0)),
                ]);
                self.set(dest, phi);
            }
            Op::Call {
                func_name,
                args,
                return_value_dest,
            } => {
                let function = *self.functions.get(func_name).expect("Function not found.");
                let args = self.collect_arg_values(args);
                let return_value = self.builder.build_call(function, &args, "");
                self.set(return_value_dest, return_value);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let value =
                    self.build_load(self.reg_basic_type(value_dest), self.read_ptr(addr), "");
                self.set(value_dest, value);
            }
            Op::StoreToPtr { addr, value_source } => {
                self.builder
                    .build_store(self.read_ptr(addr), self.read_basic_value(value_source));
            }
            Op::StackAlloc { dest, ty } => {
                let ptr = self.builder.build_alloca(self.llvm_type(*ty), "");
                self.set(dest, ptr);
            }
            _ => todo!(),
        }
    }

    fn get_func_type(&self, signature: &FuncSignature) -> FunctionType<'ctx> {
        let args: Vec<_> = signature
            .param_types
            .iter()
            .map(|ty| self.llvm_type(*ty).into())
            .collect();
        let returns = self.llvm_type(signature.return_type);
        returns.fn_type(&args, false)
    }

    fn collect_arg_values(&self, args: &[Ssa]) -> Vec<BasicMetadataValueEnum<'ctx>> {
        args.iter()
            .map(|ssa| self.read_basic_value(ssa))
            .map(TryInto::try_into)
            .map(Result::unwrap)
            .collect()
    }

    fn emit_binary_op(&mut self, dest: &Ssa, a: &Ssa, b: &Ssa, kind: BinaryOp) {
        // TODO: support pointer math (but probably be explicit about the casts in my IR).
        assert!(self.type_in_reg(a).is_int_type() && self.type_in_reg(b).is_int_type());
        let result = self.int_bin_op_factory(self.read_int(a), self.read_int(b), kind);
        self.set(dest, result);
    }

    fn int_bin_op_factory(
        &self,
        a: IntValue<'ctx>,
        b: IntValue<'ctx>,
        kind: BinaryOp,
    ) -> IntValue<'ctx> {
        match kind {
            BinaryOp::Add => self.builder.build_int_add(a, b, ""),
            BinaryOp::GreaterThan => self.builder.build_int_compare(IntPredicate::UGT, a, b, ""),
            BinaryOp::LessThan => self.builder.build_int_compare(IntPredicate::ULT, a, b, ""),
            BinaryOp::Assign => unreachable!(
                "IR parser should not emit BinaryOp::Assign. It must be converted into SSA from."
            ),
            BinaryOp::Subtract => self.builder.build_int_sub(a, b, ""),
            _ => todo!(),
        }
    }

    fn set<V>(&mut self, register: &Ssa, value: V)
    where
        V: AnyValue<'ctx>,
    {
        assert!(
            self.func_mut()
                .local_registers
                .insert(*register, value.as_any_value_enum())
                .is_none(),
            "IR must be in SSA form (only set registers once)."
        );
    }

    fn block(&self, label: Label) -> BasicBlock<'ctx> {
        self.func_get().blocks[label.index()]
    }

    fn read_int(&self, ssa: &Ssa) -> IntValue<'ctx> {
        self.func_get()
            .local_registers
            .get(ssa)
            .unwrap()
            .into_int_value()
    }

    fn read_ptr(&self, ssa: &Ssa) -> PointerValue<'ctx> {
        self.func_get()
            .local_registers
            .get(ssa)
            .unwrap()
            .into_pointer_value()
    }

    fn read_basic_value(&self, ssa: &Ssa) -> BasicValueEnum<'ctx> {
        let value = *self.func_get().local_registers.get(ssa).unwrap();
        let value: BasicValueEnum = value.try_into().unwrap();
        value
    }

    fn reg_basic_type(&self, ssa: &Ssa) -> BasicTypeEnum<'ctx> {
        let ty = self.func_get().func_ir.type_of(ssa);
        self.llvm_type(ty)
    }

    fn type_in_reg(&self, ssa: &Ssa) -> AnyTypeEnum<'ctx> {
        self.func_get().local_registers.get(ssa).unwrap().get_type()
    }

    fn emit_return(&self, value: &Option<Ssa>) {
        match value {
            None => self.builder.build_return(None),
            Some(value) => self
                .builder
                .build_return(Some(&self.read_basic_value(value))),
        };
    }

    fn llvm_type(&self, ty: CType) -> BasicTypeEnum<'ctx> {
        assert_eq!(ty.ty, ValueType::U64);

        let mut result = self.context.i64_type().as_basic_type_enum();

        for _ in 0..ty.depth {
            result = result
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum();
        }

        result.into()
    }

    // TODO: CLion can't cope with features and thinks there's an error here even though it compiles fine.
    fn build_load(
        &self,
        pointee_type: BasicTypeEnum<'ctx>,
        pointer_value: PointerValue<'ctx>,
        name: &str,
    ) -> BasicValueEnum<'ctx> {
        self.builder.build_load(pointee_type, pointer_value, name)
    }

    fn func_get(&self) -> &FuncContext<'ctx, 'module> {
        self.func.as_ref().unwrap()
    }

    fn func_mut(&mut self) -> &mut FuncContext<'ctx, 'module> {
        self.func.as_mut().unwrap()
    }
}

impl<'ctx: 'module, 'module> FuncContext<'ctx, 'module> {
    fn new(ir: &'module Function) -> FuncContext<'ctx, 'module> {
        FuncContext {
            local_registers: Default::default(),
            blocks: vec![],
            func_ir: ir,
        }
    }
}
