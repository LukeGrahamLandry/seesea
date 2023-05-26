//! IR -> LLVM IR

use crate::ast::{BinaryOp, FuncSignature, ValueType};
use crate::ir::{Function, Label, Op, Ssa};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::ContextRef;
use inkwell::execution_engine::{ExecutionEngine, JitFunction, UnsafeFunctionPointer};
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, FunctionType};
use inkwell::values::{AnyValue, AnyValueEnum, IntValue};
use inkwell::IntPredicate;
use std::collections::HashMap;

pub struct LlvmFuncGen<'ctx: 'module, 'module> {
    context: ContextRef<'ctx>,
    module: &'module Module<'ctx>,
    builder: Builder<'ctx>,

    // Reset per function
    local_registers: HashMap<Ssa, AnyValueEnum<'ctx>>,
    blocks: Vec<BasicBlock<'ctx>>,
}

impl<'ctx: 'module, 'module> LlvmFuncGen<'ctx, 'module> {
    pub fn new(module: &'module Module<'ctx>) -> LlvmFuncGen<'ctx, 'module> {
        LlvmFuncGen {
            context: module.get_context(),
            module,
            builder: module.get_context().create_builder(),
            local_registers: Default::default(),
            blocks: vec![],
        }
    }

    pub unsafe fn compile_function<F: UnsafeFunctionPointer>(
        mut self,
        ir: Function,
        execution_engine: &ExecutionEngine,
    ) -> F {
        let name = ir.sig.name.clone();
        self.emit_function(ir);
        self.module.verify().unwrap();
        let function: JitFunction<F> = execution_engine.get_function(name.as_str()).unwrap();
        function.as_raw()
    }

    // TODO: the whole program shares one module
    // TODO: module names? dumb to throw away variable names?
    pub fn compile(mut self, ir: Function, execution_engine: &ExecutionEngine) -> u64 {
        type GetInt = unsafe extern "C" fn() -> u64;
        let function = unsafe { self.compile_function::<GetInt>(ir, execution_engine) };
        unsafe { function() }
    }

    fn emit_function(&mut self, ir: Function) {
        let t = self.get_func_type(&ir.sig);
        let func = self.module.add_function(ir.sig.name.as_str(), t, None);
        let number = self.context.i64_type();

        assert!(self.local_registers.is_empty() && self.blocks.is_empty());
        // All the blocks need to exist ahead of time so jumps can reference them.
        self.blocks = ir
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
            self.local_registers
                .insert(*register, param.as_any_value_enum());
        }

        for (i, block) in ir.blocks.iter().enumerate() {
            let code = self.blocks[i];
            self.builder.position_at_end(code);
            let mut has_returned = false;

            if block.is_empty() {
                // TODO: get rid of garbage blocks before it gets to llvm.
                //       but it crashes with invalid blocks that don't jump anywhere so temp fix.
                //       llvm optimises it out anyway.
                let garbage = number.const_int(3141592, false);
                self.builder.build_return(Some(&garbage));
                continue;
            }

            for op in block {
                assert!(!has_returned);
                match op {
                    Op::ConstInt { dest, value } => {
                        let val = number.const_int(*value, false);
                        self.local_registers.insert(*dest, val.as_any_value_enum());
                    }
                    Op::Binary { dest, a, b, kind } => self.emit_binary_op(*dest, *a, *b, *kind),
                    Op::Return { value } => {
                        self.emit_return(value);
                        has_returned = true;
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
                            self.read_int(*condition),
                            self.block(*if_true),
                            self.block(*if_false),
                        );
                    }
                    Op::Phi { dest, a, b } => {
                        let a_reg = self.local_registers.get(&a.1).unwrap();
                        let b_reg = self.local_registers.get(&b.1).unwrap();

                        let ty = a_reg.get_type().into_int_type();
                        let phi = self.builder.build_phi(ty, "");

                        phi.add_incoming(&[
                            (&a_reg.into_int_value(), self.block(a.0)),
                            (&b_reg.into_int_value(), self.block(b.0)),
                        ]);

                        self.local_registers
                            .insert(*dest, AnyValueEnum::from(phi.as_basic_value()));
                    }
                    _ => todo!(),
                }
            }
        }
    }

    fn get_func_type(&self, signature: &FuncSignature) -> FunctionType<'ctx> {
        let args: Vec<_> = signature
            .param_types
            .iter()
            .map(|ty| self.llvm_type(*ty))
            .collect();
        let returns = self.llvm_type(signature.return_type);
        returns.into_int_type().fn_type(&args, false)
    }

    fn emit_binary_op(&mut self, dest: Ssa, a: Ssa, b: Ssa, kind: BinaryOp) {
        let result = self.int_bin_op_factory(self.read_int(a), self.read_int(b), kind);
        self.local_registers
            .insert(dest, result.as_any_value_enum());
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
            _ => todo!(),
        }
    }

    fn block(&self, label: Label) -> BasicBlock<'ctx> {
        self.blocks[label.index()]
    }

    fn read_int(&self, ssa: Ssa) -> IntValue<'ctx> {
        self.local_registers.get(&ssa).unwrap().into_int_value()
    }

    fn emit_return(&self, value: &Option<Ssa>) {
        match value {
            None => self.builder.build_return(None),
            Some(value) => self.builder.build_return(Some(
                &self.local_registers.get(value).unwrap().into_int_value(),
            )),
        };
    }

    fn llvm_type(&self, ty: ValueType) -> BasicMetadataTypeEnum<'ctx> {
        assert_eq!(ty, ValueType::U64);
        self.context.i64_type().into()
    }
}
