//! IR -> LLVM IR

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::ContextRef;
use inkwell::module::Module;
use inkwell::types::{AnyTypeEnum, BasicType, BasicTypeEnum, FloatType, FunctionType, IntType};
use inkwell::values::{
    AnyValue, AnyValueEnum, BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue,
    IntValue, PhiValue, PointerValue,
};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate};

use crate::ast::{BinaryOp, CType, FuncSignature, LiteralValue, ValueType};
use crate::ir;
use crate::ir::{CastType, Function, Label, Op, Ssa};
use crate::macros::llvm::emit_bin_op;

pub struct LlvmFuncGen<'ctx: 'module, 'module> {
    pub(crate) context: ContextRef<'ctx>,
    module: &'module Module<'ctx>,
    pub(crate) builder: Builder<'ctx>,
    functions: HashMap<Rc<str>, FunctionValue<'ctx>>,
    func: Option<FuncContext<'ctx, 'module>>,
    ir: Option<&'module ir::Module>,
}

/// Plain old data that holds the state that must be reset for each function.
struct FuncContext<'ctx: 'module, 'module> {
    local_registers: HashMap<Ssa, AnyValueEnum<'ctx>>,
    blocks: Vec<Option<BasicBlock<'ctx>>>,
    func_ir: &'module Function,
    phi_nodes: HashMap<PhiValue<'ctx>, Vec<(Label, Ssa)>>,
}

impl<'ctx: 'module, 'module> LlvmFuncGen<'ctx, 'module> {
    pub fn new(module: &'module Module<'ctx>) -> LlvmFuncGen<'ctx, 'module> {
        LlvmFuncGen {
            context: module.get_context(),
            module,
            builder: module.get_context().create_builder(),
            functions: Default::default(),
            func: None,
            ir: None,
        }
    }

    /// To access the results, use an execution engine created on the LLVM Module.
    pub fn compile_all(&mut self, ir: &'module ir::Module) {
        self.ir = Some(ir);
        for struct_def in &ir.structs {
            let mut field_types = vec![];
            for (_, ty) in &struct_def.fields {
                field_types.push(self.llvm_type(ty));
            }

            let llvm_struct = self.context.opaque_struct_type(struct_def.name.as_ref());
            llvm_struct.set_body(&field_types, false);
        }
        for function in &ir.forward_declarations {
            let t = self.get_func_type(function);
            let func = self.module.add_function(function.name.as_ref(), t, None);
            self.functions.insert(function.name.clone(), func);
        }
        for function in &ir.functions {
            self.emit_function(function);
        }

        println!("=== LLVM IR ====");
        println!("{}", self.module.to_string());
        println!("=========");

        match self.module.verify() {
            Ok(_) => {}
            Err(e) => println!("Failed llvm verify! \n{}.", e),
        }
    }

    fn emit_function(&mut self, ir: &'module Function) {
        self.func = Some(FuncContext::new(ir));
        let t = self.get_func_type(&ir.signature);
        let func = self
            .module
            .add_function(ir.signature.name.as_ref(), t, None);
        self.functions.insert(ir.signature.name.clone(), func);

        // All the blocks need to exist ahead of time so jumps can reference them.
        self.func_mut().blocks = ir
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| {
                if b.is_none() {
                    None
                } else {
                    Some(self.context.append_basic_block(func, &format!(".b{}", i)))
                }
            })
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
            let block = match block {
                None => continue,
                Some(b) => b,
            };
            let code = self.func_get().blocks[i].unwrap();
            self.builder.position_at_end(code);
            for op in block {
                self.emit_ir_op(op);
            }
        }

        for (phi, options) in &self.func_get().phi_nodes {
            for opt in options {
                phi.add_incoming(&[(&self.read_basic_value(&opt.1), self.block(opt.0))])
            }
        }

        self.func = None;
    }

    fn emit_ir_op(&mut self, op: &Op) {
        match op {
            Op::ConstValue { dest, value, kind } => {
                let val: BasicValueEnum = match value {
                    &LiteralValue::IntNumber(value) => {
                        let number = self.llvm_type(kind).into_int_type();
                        let val = number.const_int(value, false);
                        val.into()
                    }
                    &LiteralValue::FloatNumber(value) => {
                        let number = self.llvm_type(kind).into_float_type();
                        let val = number.const_float(value);
                        val.into()
                    }
                    LiteralValue::StringBytes(value) => {
                        let string = self.context.const_string(value.as_bytes(), true);
                        let ptr = self.builder.build_alloca(string.get_type(), "");
                        self.builder.build_store(ptr, string);
                        ptr.into()
                    }
                };
                self.set(dest, val);
            }
            Op::Binary { dest, a, b, kind } => self.emit_binary_op(dest, a, b, *kind),
            Op::Return { value } => {
                self.emit_return(value);
            }
            Op::AlwaysJump(target) => {
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
                // Emitting these is deferred because the values won't be ready yet when you jump backwards.
                self.func_mut().phi_nodes.insert(phi, vec![*a, *b]);
                self.set(dest, phi);
            }
            Op::Call {
                func_name,
                args,
                return_value_dest,
            } => {
                let function = *self
                    .functions
                    .get(func_name.as_ref())
                    .expect("Function not found.");
                let args = self.collect_arg_values(args);
                let return_value = self.builder.build_call(function, &args, "");
                if let Some(dest) = return_value_dest {
                    // Not returning void
                    self.set(dest, return_value);
                }
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
            Op::StackAlloc { dest, ty, count } => {
                assert_eq!(*count, 1);
                let ptr = self.builder.build_alloca(self.llvm_type(ty), "");
                self.set(dest, ptr);
            }
            Op::GetFieldAddr {
                dest,
                object_addr,
                field_index,
            } => {
                let struct_type = self.func_get().func_ir.type_of(object_addr).deref_type();
                let s_ptr_value = self.read_ptr(object_addr);
                let field_ptr_value = self.const_gep(
                    s_ptr_value,
                    struct_type,
                    &[
                        self.context.i64_type().const_int(0, false),
                        self.context
                            .i32_type()
                            .const_int(*field_index as u64, false),
                    ],
                );

                self.set(dest, field_ptr_value);
            }
            Op::Cast {
                input,
                output,
                kind,
            } => {
                let my_in_ty = self.func_get().func_ir.type_of(input);
                let my_out_ty = self.func_get().func_ir.type_of(input);
                let in_value = self.read_basic_value(input);
                let out_type = self.reg_basic_type(output);
                match kind {
                    CastType::Bits => {
                        assert!(
                            my_in_ty.is_ptr() && my_out_ty.is_ptr(),
                            "todo: non-pointer bit casts"
                        );
                        let result = self.builder.build_pointer_cast(
                            in_value.into_pointer_value(),
                            out_type.into_pointer_type(),
                            "",
                        );
                        self.set(output, result);
                    }
                    CastType::UnsignedIntUp => {
                        let result = self.builder.build_int_cast(
                            in_value.into_int_value(),
                            IntType::try_from(out_type).unwrap(),
                            "",
                        );
                        self.set(output, result);
                    }
                    CastType::IntDown => {
                        let result = self.builder.build_int_cast(
                            in_value.into_int_value(),
                            IntType::try_from(out_type).unwrap(),
                            "",
                        );
                        self.set(output, result);
                    }
                    CastType::FloatUp => todo!(),
                    CastType::FloatDown => todo!(),
                    CastType::FloatToUInt => {
                        let result = self.builder.build_float_to_unsigned_int(
                            in_value.into_float_value(),
                            IntType::try_from(out_type).unwrap(),
                            "",
                        );
                        self.set(output, result);
                    }
                    CastType::UIntToFloat => {
                        let result = self.builder.build_unsigned_int_to_float(
                            in_value.into_int_value(),
                            FloatType::try_from(out_type).unwrap(),
                            "",
                        );
                        self.set(output, result);
                    }
                    CastType::IntToPtr => {
                        let result = self.builder.build_int_to_ptr(
                            in_value.into_int_value(),
                            out_type.into_pointer_type(),
                            "",
                        );
                        self.set(output, result);
                    }
                    CastType::PtrToInt => {
                        let result = self.builder.build_ptr_to_int(
                            in_value.into_pointer_value(),
                            out_type.into_int_type(),
                            "",
                        );
                        self.set(output, result);
                    }
                }
            }
        }
    }

    fn get_func_type(&self, signature: &FuncSignature) -> FunctionType<'ctx> {
        let args: Vec<_> = signature
            .param_types
            .iter()
            .cloned()
            .map(|ty| self.llvm_type(ty).into())
            .collect();
        if signature.return_type.is_raw_void() {
            self.context
                .void_type()
                .fn_type(&args, signature.has_var_args)
        } else {
            self.llvm_type(&signature.return_type)
                .fn_type(&args, signature.has_var_args)
        }
    }

    fn collect_arg_values(&self, args: &[Ssa]) -> Vec<BasicMetadataValueEnum<'ctx>> {
        args.iter()
            .map(|ssa| self.read_basic_value(ssa))
            .map(TryInto::try_into)
            .map(Result::unwrap)
            .collect()
    }

    fn emit_binary_op(&mut self, dest: &Ssa, a: &Ssa, b: &Ssa, kind: BinaryOp) {
        let is_ints = self.type_in_reg(a).is_int_type() && self.type_in_reg(b).is_int_type();
        let is_floats = self.type_in_reg(a).is_float_type() && self.type_in_reg(b).is_float_type();

        if is_ints {
            let result = emit_bin_op!(
                self,
                a,
                b,
                kind,
                read_int,
                IntPredicate,
                build_int_compare,
                build_int_add,
                build_int_sub,
                build_int_mul,
                build_int_unsigned_div // TODO: there are other build_int_div functions
            );
            self.set(dest, result);
        } else if is_floats {
            let result = emit_bin_op!(
                self,
                a,
                b,
                kind,
                read_float,
                FloatPredicate,
                build_float_compare,
                build_float_add,
                build_float_sub,
                build_float_mul,
                build_float_div
            );
            self.set(dest, result);
        } else {
            panic!("Binary op must act on both ints or both floats.");
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
        self.func_get().blocks[label.index()].unwrap()
    }

    fn read_int(&self, ssa: &Ssa) -> IntValue<'ctx> {
        self.func_get()
            .local_registers
            .get(ssa)
            .unwrap()
            .into_int_value()
    }

    fn read_float(&self, ssa: &Ssa) -> FloatValue<'ctx> {
        self.func_get()
            .local_registers
            .get(ssa)
            .unwrap()
            .into_float_value()
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

    pub(crate) fn llvm_type(&self, ty: impl Borrow<CType>) -> BasicTypeEnum<'ctx> {
        let ty = ty.borrow();
        let mut result = match &ty.ty {
            ValueType::U64 => self.context.i64_type().as_basic_type_enum(),
            ValueType::Struct(name) => self.context.get_struct_type(name.as_ref()).unwrap().into(),
            ValueType::U8 => self.context.i8_type().as_basic_type_enum(),
            ValueType::U32 => self.context.i32_type().as_basic_type_enum(),
            ValueType::F32 => self.context.f32_type().as_basic_type_enum(),
            ValueType::F64 => self.context.f64_type().as_basic_type_enum(),
            ValueType::Void => {
                assert_ne!(ty.depth, 0, "void type is a special case.");
                // Using i8 as an untyped pointer.
                self.context.i8_type().as_basic_type_enum()
            }
        };

        for _ in 0..ty.depth {
            result = result
                .ptr_type(AddressSpace::default())
                .as_basic_type_enum();
        }
        result
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
            phi_nodes: HashMap::new(),
        }
    }
}
