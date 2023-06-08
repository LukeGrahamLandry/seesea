//! IR -> LLVM IR

use std::borrow::Borrow;
use std::collections::HashMap;
use std::ffi::{c_char, c_uint, CStr, CString};
use std::mem::MaybeUninit;
use std::num::NonZeroU8;
use std::rc::Rc;

use llvm_sys::analysis::{LLVMVerifierFailureAction, LLVMVerifyModule};
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::{LLVMIntPredicate, LLVMRealPredicate, LLVMTypeKind, LLVMValueKind};

use crate::ast::{BinaryOp, CType, FuncSignature, LiteralValue, ValueType};
use crate::ir::{CastType, Function, Label, Op, Ssa};
use crate::{ir, log};

pub struct RawLlvmFuncGen<'ir> {
    ctx: LLVMContextRef,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    functions: HashMap<Rc<str>, LLVMValueRef>,
    function_types: HashMap<Rc<str>, LLVMTypeRef>,
    func: Option<FuncContext<'ir>>,
    ir: Option<&'ir ir::Module>,
    llvm_structs: HashMap<Rc<str>, LLVMTypeRef>,
}

/// Plain old data that holds the state that must be reset for each function.
struct FuncContext<'ir> {
    local_registers: HashMap<Ssa, LLVMValueRef>,
    blocks: Vec<Option<LLVMBasicBlockRef>>,
    func_ir: &'ir Function,
    phi_nodes: HashMap<LLVMValueRef, Vec<(Label, Ssa)>>,
}

pub struct TheContext {
    pub context: LLVMContextRef,
    pub module: LLVMModuleRef,
}

impl<'ir> RawLlvmFuncGen<'ir> {
    /// # Safety
    /// You must not release the context or the module until after dropping the RawLlvmFuncGen.
    pub unsafe fn new(context: &mut TheContext) -> RawLlvmFuncGen<'ir> {
        RawLlvmFuncGen {
            ctx: context.context,
            module: context.module,
            builder: LLVMCreateBuilderInContext(context.context),
            functions: Default::default(),
            function_types: Default::default(),
            func: None,
            ir: None,
            llvm_structs: Default::default(),
        }
    }

    /// To access the results, use an execution engine created on the LLVM Module.
    /// # Safety
    /// You must not release the context or the module until after dropping the RawLlvmFuncGen.
    pub unsafe fn compile_all(&mut self, ir: &'ir ir::Module) {
        self.ir = Some(ir);
        for struct_def in &ir.structs {
            let mut field_types = vec![];
            for (_, ty) in &struct_def.fields {
                field_types.push(self.llvm_type(ty));
            }

            let name = null_terminate(&struct_def.name);
            let llvm_struct = LLVMStructCreateNamed(self.ctx, name.as_ptr());
            LLVMStructSetBody(
                llvm_struct,
                field_types.as_mut_ptr(),
                field_types.len() as c_uint,
                LLVMBool::from(false),
            );
            self.llvm_structs
                .insert(struct_def.name.clone(), llvm_struct);
        }
        for function in &ir.forward_declarations {
            self.emit_function_definition(function);
        }
        for function in ir.functions.iter() {
            log!("Compiling {:?}", function.signature);
            self.emit_function(function);
        }

        log!("=== LLVM IR ====");
        let ir_str = LLVMPrintModuleToString(self.module);
        log!("{}", CStr::from_ptr(ir_str).to_str().unwrap());
        LLVMDisposeMessage(ir_str);
        log!("=========");

        let mut msg = MaybeUninit::uninit();
        let failed = LLVMVerifyModule(
            self.module,
            LLVMVerifierFailureAction::LLVMPrintMessageAction,
            msg.as_mut_ptr(),
        );
        if failed != 0 {
            let msg = msg.assume_init();
            log!(
                "Failed llvm verify! \n{}.",
                CStr::from_ptr(msg).to_str().unwrap()
            );
            LLVMDisposeMessage(msg);
        }

        // Just make sure the universe still makes sense.
        for s in self.llvm_structs.values() {
            assert_eq!(LLVMGetTypeKind(*s), LLVMTypeKind::LLVMStructTypeKind);
        }
        for s in self.functions.values() {
            assert_eq!(LLVMGetValueKind(*s), LLVMValueKind::LLVMFunctionValueKind);
        }
    }

    unsafe fn emit_function_definition(&mut self, function: &FuncSignature) -> LLVMValueRef {
        let function_type = self.get_func_type(function);
        let name = null_terminate(&function.name);
        let function_value = LLVMAddFunction(self.module, name.as_ptr(), function_type);
        self.functions.insert(function.name.clone(), function_value);
        self.function_types
            .insert(function.name.clone(), function_type);
        function_value
    }

    unsafe fn emit_function(&mut self, ir: &'ir Function) {
        assert!(!ir.signature.has_var_args);
        self.func = Some(FuncContext::new(ir));
        let func = self.emit_function_definition(&ir.signature);

        // All the blocks need to exist ahead of time so jumps can reference them.
        self.func_mut().blocks = ir
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| {
                if b.is_none() {
                    None
                } else {
                    let name = null_terminate(&format!(".b{}", i));
                    let block = LLVMAppendBasicBlock(func, name.as_ptr());
                    Some(block)
                }
            })
            .collect();

        // Map the llvm function arguments to our ssa register system.
        for (i, register) in ir.arg_registers.iter().enumerate() {
            self.set(register, LLVMGetParam(func, i as c_uint));
        }

        // Compile the body of the function.
        for (i, block) in ir.blocks.iter().enumerate() {
            let block = match block {
                None => continue,
                Some(b) => b,
            };
            let code = self.func_get().blocks[i].unwrap();
            LLVMPositionBuilderAtEnd(self.builder, code);
            for op in block {
                self.emit_ir_op(op);
            }
        }

        for (phi, options) in &self.func_get().phi_nodes {
            let mut value_kinds = vec![];
            // TODO: add them all in one call.
            for opt in options {
                let mut block = self.block(opt.0);
                let mut value = self.get_value(&opt.1);
                value_kinds.push(LLVMGetValueKind(value));
                LLVMAddIncoming(*phi, &mut value, &mut block, 1 as c_uint);
            }
        }

        self.func = None;
    }

    unsafe fn emit_ir_op(&mut self, op: &Op) {
        let empty = CString::from(vec![]);
        match op {
            Op::ConstValue { dest, value, kind } => {
                let val = match value {
                    &LiteralValue::IntNumber(value) => {
                        LLVMConstInt(self.llvm_type(kind), value, LLVMBool::from(false))
                    }
                    &LiteralValue::FloatNumber(value) => LLVMConstReal(self.llvm_type(kind), value),
                    LiteralValue::StringBytes(value) => {
                        let string = LLVMConstString(
                            value.as_ptr() as *const c_char,
                            value.len() as c_uint,
                            LLVMBool::from(false),
                        );
                        let byte_array_type = LLVMArrayType(
                            LLVMInt8TypeInContext(self.ctx),
                            (value.len() + 1) as c_uint,
                        );
                        let str_ptr =
                            LLVMBuildAlloca(self.builder, byte_array_type, empty.as_ptr());
                        LLVMBuildStore(self.builder, string, str_ptr);
                        str_ptr
                    }
                    LiteralValue::UninitStruct => {
                        todo!()
                    }
                };
                self.set(dest, val);
            }
            Op::Binary { dest, a, b, kind } => self.emit_binary_op(dest, a, b, *kind),
            Op::Return(value) => {
                self.emit_return(value);
            }
            Op::AlwaysJump(target) => {
                LLVMBuildBr(self.builder, self.block(*target));
            }
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => {
                LLVMBuildCondBr(
                    self.builder,
                    self.get_value(condition),
                    self.block(*if_true),
                    self.block(*if_false),
                );
            }
            Op::Phi { dest, a, b } => {
                let phi = LLVMBuildPhi(self.builder, self.get_type(&a.1), empty.as_ptr());
                // Emitting these is deferred because the values won't be ready yet when you jump backwards.
                self.func_mut().phi_nodes.insert(phi, vec![*a, *b]);
                self.set(dest, phi);
            }
            Op::Call {
                func_name,
                args,
                return_value_dest,
                ..
            } => {
                let function = *self
                    .functions
                    .get(func_name.as_ref())
                    .unwrap_or_else(|| panic!("Function not found {:?}.", func_name));
                assert_eq!(
                    LLVMGetValueKind(function),
                    LLVMValueKind::LLVMFunctionValueKind
                );

                let mut args = args
                    .iter()
                    .map(|ssa| self.get_value(ssa))
                    .collect::<Vec<_>>();

                let return_value = LLVMBuildCall2(
                    self.builder,
                    *self.function_types.get(func_name).unwrap(),
                    function,
                    args.as_mut_ptr(),
                    args.len() as c_uint,
                    empty.as_ptr(),
                );

                if let Some(dest) = return_value_dest {
                    // Not returning void
                    self.set(dest, return_value);
                }
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let value = LLVMBuildLoad2(
                    self.builder,
                    self.get_type(value_dest),
                    self.get_value(addr),
                    empty.as_ptr(),
                );
                self.set(value_dest, value);
            }
            Op::StoreToPtr { addr, value_source } => {
                LLVMBuildStore(
                    self.builder,
                    self.get_value(value_source),
                    self.get_value(addr),
                );
            }
            Op::StackAlloc { dest, ty, count } => {
                assert_eq!(*count, 1);
                let ptr = LLVMBuildAlloca(self.builder, self.llvm_type(ty), empty.as_ptr());
                self.set(dest, ptr);
            }
            Op::GetFieldAddr {
                dest,
                object_addr,
                field_index,
            } => {
                let struct_type = self.func_get().func_ir.type_of(object_addr).deref_type();
                let llvm_struct_type = self.llvm_type(struct_type);
                let s_ptr_value = self.get_value(object_addr);
                let mut index_values = vec![
                    LLVMConstInt(LLVMInt32TypeInContext(self.ctx), 0, LLVMBool::from(false)),
                    LLVMConstInt(
                        LLVMInt32TypeInContext(self.ctx),
                        *field_index as u64,
                        LLVMBool::from(false),
                    ),
                ];
                let field_ptr_value = LLVMBuildGEP2(
                    self.builder,
                    llvm_struct_type,
                    s_ptr_value,
                    index_values.as_mut_ptr(),
                    index_values.len() as c_uint,
                    empty.as_ptr(),
                );
                self.set(dest, field_ptr_value);
            }
            Op::Cast {
                input,
                output,
                kind,
            } => {
                let my_in_ty = self.func_get().func_ir.type_of(input);
                let my_out_ty = self.func_get().func_ir.type_of(output);
                let in_value = self.get_value(input);
                let out_type = self.get_type(output);
                let empty = CString::from(vec![]);
                let result = match kind {
                    CastType::Bits => {
                        if my_in_ty == my_out_ty {
                            self.set(output, in_value);
                            // Could return instead of panicking here but lets give you a chance to reconsider your life choices.
                            panic!("CastType::Bits where input type == output type which is weird but fine I guess");
                        }
                        assert!(
                            my_in_ty.is_ptr() && my_out_ty.is_ptr(),
                            "todo: non-pointer bit casts {:?} to {:?}",
                            my_in_ty,
                            my_out_ty
                        );
                        LLVMBuildPointerCast(self.builder, in_value, out_type, empty.as_ptr())
                    }
                    CastType::UnsignedIntUp | CastType::IntDown => LLVMBuildIntCast2(
                        self.builder,
                        in_value,
                        out_type,
                        LLVMBool::from(false),
                        empty.as_ptr(),
                    ),
                    CastType::FloatUp => todo!(),
                    CastType::FloatDown => todo!(),
                    CastType::FloatToUInt => {
                        LLVMBuildFPToUI(self.builder, in_value, out_type, empty.as_ptr())
                    }
                    CastType::UIntToFloat => {
                        LLVMBuildUIToFP(self.builder, in_value, out_type, empty.as_ptr())
                    }
                    CastType::IntToPtr => {
                        LLVMBuildIntToPtr(self.builder, in_value, out_type, empty.as_ptr())
                    }
                    CastType::PtrToInt => {
                        LLVMBuildPtrToInt(self.builder, in_value, out_type, empty.as_ptr())
                    }
                };
                self.set(output, result);
            }
        }
    }

    unsafe fn get_func_type(&self, signature: &FuncSignature) -> LLVMTypeRef {
        let mut args: Vec<_> = signature
            .param_types
            .iter()
            .cloned()
            .map(|ty| self.llvm_type(ty))
            .collect();
        let returns = if signature.return_type.is_raw_void() {
            LLVMVoidTypeInContext(self.ctx)
        } else {
            self.llvm_type(&signature.return_type)
        };

        LLVMFunctionType(
            returns,
            args.as_mut_ptr(),
            args.len() as c_uint,
            LLVMBool::from(signature.has_var_args),
        )
    }

    fn get_value(&self, ssa: &Ssa) -> LLVMValueRef {
        *self.func_get().local_registers.get(ssa).unwrap()
    }

    unsafe fn get_type(&self, ssa: &Ssa) -> LLVMTypeRef {
        self.llvm_type(self.func_get().func_ir.type_of(ssa))
    }

    unsafe fn emit_binary_op(&mut self, dest: &Ssa, a: &Ssa, b: &Ssa, kind: BinaryOp) {
        let a_type = self.func_get().func_ir.type_of(a);
        let b_type = self.func_get().func_ir.type_of(b);
        let is_ints = a_type.is_raw_int() && b_type.is_raw_int();
        let is_floats = a_type.is_raw_float() && b_type.is_raw_float();
        let a = self.get_value(a);
        let b = self.get_value(b);

        let empty = CString::from(vec![]);
        let name = empty.as_ptr();
        let result = if is_ints {
            match kind {
                BinaryOp::Add => LLVMBuildAdd(self.builder, a, b, name),
                BinaryOp::GreaterThan => {
                    LLVMBuildICmp(self.builder, LLVMIntPredicate::LLVMIntUGT, a, b, name)
                }
                BinaryOp::LessThan => {
                    LLVMBuildICmp(self.builder, LLVMIntPredicate::LLVMIntULT, a, b, name)
                }
                BinaryOp::Subtract => LLVMBuildSub(self.builder, a, b, name),
                BinaryOp::Multiply => LLVMBuildMul(self.builder, a, b, name),
                BinaryOp::Divide => LLVMBuildUDiv(self.builder, a, b, name),
                BinaryOp::GreaterOrEqual => {
                    LLVMBuildICmp(self.builder, LLVMIntPredicate::LLVMIntUGE, a, b, name)
                }
                BinaryOp::LessOrEqual => {
                    LLVMBuildICmp(self.builder, LLVMIntPredicate::LLVMIntULE, a, b, name)
                }
                BinaryOp::Modulo | BinaryOp::Equality => todo!(),
            }
        } else if is_floats {
            match kind {
                BinaryOp::Add => LLVMBuildFAdd(self.builder, a, b, name),
                BinaryOp::GreaterThan => {
                    LLVMBuildFCmp(self.builder, LLVMRealPredicate::LLVMRealUGT, a, b, name)
                }
                BinaryOp::LessThan => {
                    LLVMBuildFCmp(self.builder, LLVMRealPredicate::LLVMRealULT, a, b, name)
                }
                BinaryOp::Subtract => LLVMBuildFSub(self.builder, a, b, name),
                BinaryOp::Multiply => LLVMBuildFMul(self.builder, a, b, name),
                BinaryOp::Divide => LLVMBuildFDiv(self.builder, a, b, name),
                BinaryOp::GreaterOrEqual => {
                    LLVMBuildFCmp(self.builder, LLVMRealPredicate::LLVMRealUGE, a, b, name)
                }
                BinaryOp::LessOrEqual => {
                    LLVMBuildFCmp(self.builder, LLVMRealPredicate::LLVMRealULE, a, b, name)
                }
                BinaryOp::Modulo | BinaryOp::Equality => todo!(),
            }
        } else {
            panic!("Binary op {:?} must act on both ints or both floats.", kind,);
        };

        self.set(dest, result);
    }

    fn set(&mut self, register: &Ssa, value: LLVMValueRef) {
        assert!(
            self.func_mut()
                .local_registers
                .insert(*register, value)
                .is_none(),
            "IR must be in SSA form (only set registers once)."
        );
    }

    fn block(&self, label: Label) -> LLVMBasicBlockRef {
        self.func_get().blocks[label.index()].unwrap()
    }

    unsafe fn emit_return(&self, value: &Option<Ssa>) {
        match value {
            None => LLVMBuildRetVoid(self.builder),
            Some(value) => LLVMBuildRet(self.builder, self.get_value(value)),
        };
    }

    pub(crate) unsafe fn llvm_type(&self, ty: impl Borrow<CType>) -> LLVMTypeRef {
        let ty = ty.borrow();
        let mut result = match &ty.ty {
            ValueType::U64 => LLVMInt64TypeInContext(self.ctx),
            ValueType::Struct(name) => *self.llvm_structs.get(name).unwrap(),
            ValueType::U8 => LLVMInt8TypeInContext(self.ctx),
            ValueType::U32 => LLVMInt32TypeInContext(self.ctx),
            ValueType::F32 => LLVMFloatTypeInContext(self.ctx),
            ValueType::F64 => LLVMDoubleTypeInContext(self.ctx),
            ValueType::Void => {
                assert_ne!(ty.depth, 0, "void type is a special case.");
                // Using i8 as an untyped pointer.
                LLVMInt8TypeInContext(self.ctx)
            }
        };

        for _ in 0..ty.depth {
            result = self.llvm_ref_type(result);
        }
        result
    }

    fn func_get(&self) -> &FuncContext<'ir> {
        self.func.as_ref().unwrap()
    }

    fn func_mut(&mut self) -> &mut FuncContext<'ir> {
        self.func.as_mut().unwrap()
    }

    unsafe fn llvm_ref_type(&self, ty: LLVMTypeRef) -> LLVMTypeRef {
        LLVMPointerType(ty, c_uint::from(0u16))
    }
}

impl<'ir> Drop for RawLlvmFuncGen<'ir> {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeBuilder(self.builder);
        }
    }
}

impl<'module> FuncContext<'module> {
    fn new(ir: &'module Function) -> FuncContext<'module> {
        FuncContext {
            local_registers: Default::default(),
            blocks: vec![],
            func_ir: ir,
            phi_nodes: HashMap::new(),
        }
    }
}

pub fn null_terminate(bytes: &str) -> CString {
    let bytes: Vec<_> = Vec::from(bytes)
        .into_iter()
        .map(|b| NonZeroU8::new(b).unwrap())
        .collect();
    CString::from(bytes)
}
