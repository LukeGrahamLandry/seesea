use crate::ast::{BinaryOp, CType, FuncSignature, FuncSource, LiteralValue, ValueType};
use crate::ir::{CastType, Label, Op, Ssa};
use crate::util::imap::IndexMap;
use crate::{ir, log};
use cranelift::codegen::ir::stackslot::StackSize;
use cranelift::codegen::ir::{ArgumentExtension, ArgumentPurpose, UserExternalName};
use cranelift::codegen::Context;
use cranelift::prelude::types::*;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use std::borrow::Borrow;
use std::collections::HashMap;
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
    func: &'ir ir::Function,
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

    fn forward_declare(&mut self, sig: &FuncSignature, linkage: Linkage) {
        let func = self
            .module
            .declare_function(&sig.name, linkage, &self.make_signature(&sig))
            .unwrap();
        self.functions.insert(sig.name.clone(), func);
    }

    pub fn compile_all(&mut self) {
        // Need all functions up front so they can call each-other. Isomorphic with forward declaration.
        for f in &self.ir.functions {
            self.forward_declare(&f.signature, Linkage::Export);
        }

        // Declare external functions (libc, etc)
        for f in &self.ir.forward_declarations {
            // Internal functions are dealt with above. They can still be in forward_declarations depending on the src.
            if self.ir.get_internal_func(&f.name).is_some() {
                continue;
            }
            self.forward_declare(f, Linkage::Import);
        }

        // Now actually emit the internal functions.
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
                func: f,
                builder,
                module: &mut self.module,
                blocks: Default::default(),
                local_registers: Default::default(),
                functions: &self.functions,
            };

            // All blocks must be created early so they can be used as jump targets.
            for (i, code) in f.blocks.iter().enumerate() {
                if code.is_some() {
                    state.blocks.insert(Label(i), state.builder.create_block());
                }
            }

            // Map function argument ssas to block param values.
            // TODO: is this really the only way to access function arguments?
            assert!(!f.signature.has_var_args);
            let entry_block = state.blocks[Label(0)];
            state.builder.switch_to_block(entry_block);
            state
                .builder
                .append_block_params_for_function_params(entry_block);
            let arg_count = f.arg_registers.len();
            for i in 0..arg_count {
                let val = state.builder.block_params(entry_block)[i];
                state.set(f.arg_registers[i], val);
            }

            // Now generate code for all the blocks.
            for (i, code) in f.blocks.iter().enumerate() {
                if let Some(block) = code {
                    state.builder.switch_to_block(state.blocks[Label(i)]);
                    for op in block {
                        state.emit_ir_op(op);
                    }
                }
            }

            state.builder.seal_all_blocks();
            state.builder.finalize();
            log!("{}", self.ctx.func.display());
            self.module.define_function(func, &mut self.ctx).unwrap();
            self.module.clear_context(&mut self.ctx);
        }

        self.module.finalize_definitions().unwrap();
        log!("======");
    }

    fn make_signature(&self, f: &FuncSignature) -> Signature {
        make_signature(&self.module, &self.ir, f)
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
    // The state must already be looking at the right block.
    fn emit_ir_op(&mut self, op: &Op) {
        match op {
            Op::ConstValue { dest, value, kind } => {
                let val = match value {
                    LiteralValue::IntNumber(v) => {
                        assert_eq!(kind.ty, ValueType::U64);
                        // TODO: why do you no are have unsigned
                        self.builder.ins().iconst(make_type(kind), *v as i64)
                    }
                    LiteralValue::FloatNumber(v) => {
                        assert!(!kind.is_ptr());
                        match kind.ty {
                            ValueType::F64 => self.builder.ins().f64const(*v),
                            ValueType::F32 => self.builder.ins().f32const(*v as f32),
                            _ => unreachable!(),
                        }
                    }
                    LiteralValue::StringBytes(_) => todo!(),
                    LiteralValue::UninitStruct => todo!(),
                    LiteralValue::UninitArray(_, _) => todo!(),
                };
                self.set(dest, val);
            }
            Op::Binary { dest, a, b, kind } => {
                let ty = *self.func.type_of(a);
                assert_eq!(ty, *self.func.type_of(b));

                let a = self.get(a);
                let b = self.get(b);

                let val = if ty.is_raw_int() {
                    int_bin(&mut self.builder, *kind, a, b)
                } else if ty.is_raw_float() {
                    float_bin(&mut self.builder, *kind, a, b)
                } else {
                    unreachable!()
                };

                self.set(dest, val);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let ty = self.func.type_of(value_dest);
                let ptr = self.get(addr);
                // TODO: think about what MemFlags pinky promises I can make
                let val = self
                    .builder
                    .ins()
                    .load(make_type(ty), MemFlags::new(), ptr, 0);
                self.set(value_dest, val);
            }
            Op::StoreToPtr { addr, value_source } => {
                let val = self.get(value_source);
                let ptr = self.get(addr);
                self.builder.ins().store(MemFlags::new(), val, ptr, 0);
            }
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
            Op::StackAlloc { dest, ty, count } => {
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    (self.ir.size_of(ty) * *count) as StackSize,
                ));
                // TODO: its dumb that I'm telling it I actually need it on the stack.
                //       but if I was tracking ssa stuff correctly i want to do it when parsing my ir, not rely on the backend.
                let addr = self.builder.ins().stack_addr(R64, slot, 0);
                self.set(dest, addr);
            }
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
                // Different kinds are called the same way now but guard against adding a new one.
                assert!(matches!(kind, FuncSource::Internal | FuncSource::External));
                let target = *self.functions.get(func_name).unwrap();
                // TODO: does do this up front so it doesn't spam when I call the same function multiple times?
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
            Op::Cast {
                input,
                output,
                kind,
            } => match kind {
                CastType::Bits | CastType::IntToPtr | CastType::PtrToInt => {
                    let ty = self.func.type_of(output);
                    let x = self.get(input);
                    let val = self
                        .builder
                        .ins()
                        .bitcast(make_type(ty), MemFlags::new(), x);
                    self.set(output, val);
                }
                CastType::UnsignedIntUp => todo!(),
                CastType::IntDown => todo!(),
                CastType::FloatUp => todo!(),
                CastType::FloatDown => todo!(),
                CastType::FloatToUInt => todo!(),
                CastType::UIntToFloat => todo!(),
                CastType::IntToBool => todo!(),
                CastType::BoolToInt => todo!(),
            },
        }
    }

    fn set(&mut self, ssa: impl Borrow<Ssa>, val: Value) {
        assert!(
            self.local_registers.insert(*ssa.borrow(), val).is_none(),
            "tried to mutate ssa value"
        );
    }

    fn get(&self, ssa: impl Borrow<Ssa>) -> Value {
        *self
            .local_registers
            .get(ssa.borrow())
            .unwrap_or_else(|| panic!("get before set {:?}", ssa.borrow()))
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

fn make_signature(module: &impl Module, ir: &ir::Module, f: &FuncSignature) -> Signature {
    let mut sig = module.make_signature();
    for arg in &f.param_types {
        let purpose = if let ValueType::Struct(_) = &arg.ty {
            if arg.is_ptr() {
                ArgumentPurpose::Normal
            } else {
                ArgumentPurpose::StructArgument(ir.size_of(arg) as u32)
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

// Sad copy paste noises.
fn int_bin(builder: &mut FunctionBuilder, kind: BinaryOp, a: Value, b: Value) -> Value {
    match kind {
        BinaryOp::Add => builder.ins().iadd(a, b),
        BinaryOp::Subtract => builder.ins().isub(a, b),
        BinaryOp::Multiply => builder.ins().imul(a, b),
        // TODO: signed!
        BinaryOp::Divide => builder.ins().udiv(a, b),
        BinaryOp::Modulo => builder.ins().urem(a, b),
        BinaryOp::Equality => builder.ins().icmp(IntCC::Equal, a, b),
        BinaryOp::GreaterThan => builder.ins().icmp(IntCC::UnsignedGreaterThan, a, b),
        BinaryOp::LessThan => builder.ins().icmp(IntCC::UnsignedLessThan, a, b),
        BinaryOp::GreaterOrEqual => builder.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, a, b),
        BinaryOp::LessOrEqual => builder.ins().icmp(IntCC::UnsignedLessThanOrEqual, a, b),
    }
}

fn float_bin(builder: &mut FunctionBuilder, kind: BinaryOp, a: Value, b: Value) -> Value {
    match kind {
        BinaryOp::Add => builder.ins().fadd(a, b),
        BinaryOp::Subtract => builder.ins().fsub(a, b),
        BinaryOp::Multiply => builder.ins().fmul(a, b),
        BinaryOp::Divide => builder.ins().fdiv(a, b),
        BinaryOp::Modulo => panic!("float mod isn't a thing bro"),
        BinaryOp::Equality => builder.ins().fcmp(FloatCC::Equal, a, b),
        BinaryOp::GreaterThan => builder.ins().fcmp(FloatCC::GreaterThan, a, b),
        BinaryOp::LessThan => builder.ins().fcmp(FloatCC::LessThan, a, b),
        BinaryOp::GreaterOrEqual => builder.ins().fcmp(FloatCC::GreaterThanOrEqual, a, b),
        BinaryOp::LessOrEqual => builder.ins().fcmp(FloatCC::LessThanOrEqual, a, b),
    }
}
