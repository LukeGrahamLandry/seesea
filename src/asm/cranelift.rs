use crate::ast::{CType, FuncSignature, FuncSource, LiteralValue, ValueType};
use crate::ir::{Label, Op, Ssa};
use crate::util::imap::IndexMap;
use crate::{ir, log};
use cranelift::codegen::ir::{ArgumentExtension, ArgumentPurpose};
use cranelift::codegen::Context;
use cranelift::prelude::types::*;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::ptr;
use std::rc::Rc;

pub struct CraneLiftFuncGen<'ir> {
    ir: &'ir ir::Module,
    module: JITModule,
    ctx: Context,
    builder_ctx: FunctionBuilderContext,
    functions: HashMap<Rc<str>, FuncId>,
}

struct FunctionState<'ir, 'gen> {
    ir: &'ir ir::Module,
    builder: FunctionBuilder<'gen>,
    module: &'gen mut JITModule,
    blocks: IndexMap<Label, Block>,
    local_registers: IndexMap<Ssa, Value>,
    functions: &'gen HashMap<Rc<str>, FuncId>,
}

impl<'ir> CraneLiftFuncGen<'ir> {
    pub fn new(ir: &'ir ir::Module) -> Self {
        let flag_builder = settings::builder();
        let isa_builder = cranelift_native::builder().unwrap();
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let module = JITModule::new(builder);
        assert_eq!(
            module.target_config().pointer_bits(),
            64,
            "i assume this 64 bit in many places before this"
        );

        CraneLiftFuncGen {
            ir,
            ctx: module.make_context(),
            module,
            builder_ctx: FunctionBuilderContext::new(),
            functions: Default::default(),
        }
    }

    pub fn compile_all(&mut self) {
        // Need all functions up front so they can call each-other. Isomorphic with forward declaration.
        // TODO: cope with external functions. probably just the same?
        for f in &self.ir.functions {
            let func = self
                .module
                .declare_function(
                    &f.signature.name,
                    Linkage::Export,
                    &self.make_signature(&f.signature),
                )
                .unwrap();
            self.functions.insert(f.signature.name.clone(), func);
        }

        log!("===== CraneLift IR =====");
        for f in &self.ir.functions {
            let func = *self.functions.get(&f.signature.name).unwrap();

            // TODO: how do i make myself look at the func i declared before
            //       maybe its fine. now it just needs to know its the same sig, later i bind it to the id so references work out.
            let sig = self.make_signature(&f.signature);
            self.ctx.func.signature = sig;

            let builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);
            let mut state = FunctionState {
                ir: self.ir,
                builder,
                module: &mut self.module,
                blocks: Default::default(),
                local_registers: Default::default(),
                functions: &self.functions,
            };

            for (i, code) in f.blocks.iter().enumerate() {
                if code.is_some() {
                    state.blocks.insert(Label(i), state.builder.create_block());
                }
            }

            for (i, code) in f.blocks.iter().enumerate() {
                if let Some(block) = code {
                    state.builder.switch_to_block(state.blocks[Label(i)]);
                    for op in block {
                        state.emit_ir_op(Label(i), op);
                    }
                }
            }

            state.builder.seal_all_blocks();
            log!("{}", self.ctx.func.display());

            self.module.define_function(func, &mut self.ctx).unwrap();
            self.module.clear_context(&mut self.ctx);
        }

        self.module.finalize_definitions().unwrap();
        log!("======");
    }

    fn make_signature(&self, f: &FuncSignature) -> Signature {
        let mut sig = self.module.make_signature();
        for arg in &f.param_types {
            let purpose = if let ValueType::Struct(_) = &arg.ty {
                if arg.is_ptr() {
                    ArgumentPurpose::Normal
                } else {
                    ArgumentPurpose::StructArgument(self.ir.size_of(arg) as u32)
                }
            } else {
                ArgumentPurpose::Normal
            };

            sig.params.push(AbiParam {
                value_type: make_type(arg),
                purpose,
                extension: ArgumentExtension::None,
            });
        }

        if !f.return_type.is_raw_void() {
            assert!(
                !f.return_type.is_struct(),
                "todo: argumentpurpose::structreturn"
            );
            sig.returns.push(AbiParam::new(make_type(&f.return_type)));
        }

        sig
    }

    pub fn get_finalized_function(&self, name: &str) -> Option<*const u8> {
        match self.functions.get(name) {
            None => None,
            Some(func) => {
                let ptr = self.module.get_finalized_function(*func);
                assert!(!ptr.is_null());
                Some(ptr)
            }
        }
    }
}

impl<'ir, 'gen> FunctionState<'ir, 'gen> {
    fn emit_ir_op(&mut self, label: Label, op: &Op) {
        match op {
            Op::ConstValue { dest, value, kind } => {
                let val = match value {
                    LiteralValue::IntNumber(v) => {
                        assert_eq!(kind.ty, ValueType::U64);
                        // TODO: why do you no are have unsigned
                        self.builder.ins().iconst(make_type(kind), *v as i64)
                    }
                    LiteralValue::FloatNumber(v) => {
                        assert_eq!(kind.ty, ValueType::F64);
                        self.builder.ins().iconst(make_type(kind), *v as i64)
                    }
                    LiteralValue::StringBytes(_) => todo!(),
                    LiteralValue::UninitStruct => todo!(),
                    LiteralValue::UninitArray(_, _) => todo!(),
                };
                self.set(dest, val);
            }
            Op::Binary { .. } => todo!(),
            Op::LoadFromPtr { .. } => todo!(),
            Op::StoreToPtr { .. } => todo!(),
            Op::Jump { .. } => todo!(),
            Op::AlwaysJump(_) => todo!(),
            Op::Phi { .. } => todo!(),
            Op::Return(ret_ssa) => match ret_ssa {
                None => {
                    self.builder.ins().return_(&[]);
                }
                Some(ret_ssa) => {
                    let vals = &[self.get(ret_ssa)];
                    self.builder.ins().return_(vals);
                }
            },
            Op::StackAlloc { .. } => todo!(),
            Op::Call {
                kind,
                func_name,
                args,
                return_value_dest,
            } => {
                let args: Vec<_> = args
                    .iter()
                    .map(|s| *self.local_registers.get(s).unwrap())
                    .collect();
                assert_eq!(kind, &FuncSource::Internal);
                let target = *self.functions.get(func_name).unwrap();
                let target = self.module.declare_func_in_func(target, self.builder.func);
                let call = self.builder.ins().call(target, &args);
                let val = self.builder.inst_results(call);
                match return_value_dest {
                    None => assert!(val.is_empty(), "void call returned values"),
                    Some(ret_ssa) => {
                        assert_eq!(val.len(), 1);
                        self.set(ret_ssa, val[0]);
                    }
                }
            }
            Op::GetFieldAddr { .. } => todo!(),
            Op::Cast { .. } => todo!(),
        }
    }

    fn set(&mut self, ssa: impl Borrow<Ssa>, val: Value) {
        assert!(
            self.local_registers.insert(*ssa.borrow(), val).is_none(),
            "tried to mutate ssa value"
        );
    }

    fn get(&self, ssa: impl Borrow<Ssa>) -> Value {
        *self.local_registers.get(ssa.borrow()).unwrap()
    }
}

fn make_type(ty: &CType) -> Type {
    if ty.depth > 0 {
        return R64;
    }

    match ty.ty {
        ValueType::Bool | ValueType::U8 => I8,
        ValueType::U64 => I64,
        ValueType::U32 => I32,
        ValueType::F64 => F64,
        ValueType::F32 => F32,
        ValueType::Struct(_) => R64, // ??
        ValueType::Void => INVALID,
    }
}
