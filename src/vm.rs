//! An interpreter for my IR for inspecting the temporary registers while debugging codegen.
//! A GUI that showed where you were in source / tokens / AST / IR side by side and let you step forward would be really cool.
//! For now it just gives me another backend so if it agrees on results with LLVM then I know my IR gen was the problem.
#![allow(unused)]

use crate::ast::{BinaryOp, CType, LiteralValue, ValueType};
use crate::ir::{CastType, Function, Label, Module, Op, Ssa};
use crate::{ir, log};

use crate::ast::FuncSource;
use crate::ir::liveness::{compute_liveness, SsaLiveness};
use crate::util::imap::IndexMap;
use macros::{do_bin_cmp, do_bin_math};
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter};
use std::io::Write;
use std::marker::PhantomData;
use std::mem;
use std::mem::size_of;
use std::ops::Add;
use std::ptr::write;
use std::rc::Rc;

const LOG_VM_TRACE: bool = false;

macro_rules! vmlog {
    ($($arg:tt)*) => {{
        if LOG_VM_TRACE {
            log!($($arg)*);
        }
    }};
}

// TODO: @Speed group allocations and reuse memory (especially for the stack + registers)
pub struct Vm<'ir> {
    module: &'ir Module,
    call_stack: Vec<StackFrame<'ir>>,
    stack_address_counter: usize,
    tick: usize,
    tick_limit: Option<usize>,
    heap: DebugAlloc,
    auto_free: Vec<Ptr>,
}

struct StackFrame<'ir> {
    registers: IndexMap<Ssa, VmValue>,
    function: &'ir Function,
    last_block: Option<Label>,
    block: Label,
    ip: usize,
    return_value_register: Option<Ssa>,
    allocations: Vec<Ptr>,
    entry_location: Location,
    liveness: SsaLiveness<'ir>,
}

pub enum VmResult {
    Continue,
    Done(Option<VmValue>),
}

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum VmValue {
    U64(u64),
    F64(f64),
    Uninit,
    Pointer(Ptr),
}

#[derive(PartialEq, Clone, Debug)]
struct Location {
    tick: usize,
    line: i64,
    instruction: usize,
    block: Label,
    func_name: Rc<str>,
}

#[derive(PartialEq, Clone)]
struct StackTrace {
    data: Vec<Location>,
}

impl<'ir> Vm<'ir> {
    pub fn new(module: &Module) -> Vm {
        Vm {
            module,
            call_stack: vec![],
            stack_address_counter: 0,
            tick: 0,
            tick_limit: None,
            heap: DebugAlloc::default(),
            auto_free: vec![],
        }
    }

    pub fn eval_int_args(module: &Module, function_name: &str, args: &[u64]) -> VmResult {
        Vm::eval(
            module,
            function_name,
            &args.iter().copied().map(VmValue::U64).collect::<Vec<_>>(),
        )
    }

    pub fn eval(module: &Module, function_name: &str, args: &[VmValue]) -> VmResult {
        log!("Start VM Eval.");
        let mut vm = Vm::new(module);
        vm.tick_limit = Some(1250); // TODO: move limit into tests file
        let func = module
            .get_internal_func(function_name)
            .expect("Function not found");
        let frame = StackFrame {
            registers: Default::default(),
            function: func,
            last_block: None,
            block: func.entry_point(),
            ip: 0,
            return_value_register: None,
            allocations: vec![],
            entry_location: Location {
                tick: 0,
                line: -1,
                instruction: 0,
                block: Label(0),
                func_name: "Program_Start".into(),
            },
            liveness: compute_liveness(func),
        };
        vm.call_stack.push(frame);
        vm.init_params(args.iter().copied());

        loop {
            let result = vm.tick();
            if let VmResult::Done(_) = result {
                vm.heap.assert_no_leaks();
                log!("-------");
                return result;
            }
        }
    }

    pub fn tick(&mut self) -> VmResult {
        // CLion doesn't want to show me the output while it hangs on a mistake in my tests that causes an infinite loop.
        if let Some(tick_limit) = self.tick_limit {
            if self.tick > tick_limit {
                panic!(
                    "Damn bro the VM's been running for {} ticks... maybe check for infinite loops or remove the tick_limit",
                    self.tick
                );
            }
        }
        self.tick += 1;

        vmlog!(
            "[{:?}] ip = {}; {} (frame = {})",
            self.get_frame().block,
            self.get_frame().ip,
            self.get_frame().function.signature.name,
            self.call_stack.len()
        );
        let ops = self.get_frame().function.blocks[self.get_frame().block.index()]
            .as_ref()
            .unwrap();
        let op = ops[self.get_frame().ip].clone();
        vmlog!("Op: {}", self.get_frame().function.print(&op));
        match op {
            Op::Binary { dest, a, b, kind } => {
                let result = match kind {
                    BinaryOp::Add => do_bin_math!(self, a, b, +),
                    BinaryOp::Subtract => do_bin_math!(self, a, b, -),
                    BinaryOp::GreaterThan => do_bin_cmp!(self, a, b, >),
                    BinaryOp::LessThan => do_bin_cmp!(self, a, b, <),
                    BinaryOp::Multiply => do_bin_math!(self, a, b, *),
                    BinaryOp::Divide => do_bin_math!(self, a, b, /),
                    BinaryOp::Modulo => do_bin_math!(self, a, b, %),
                    BinaryOp::Equality => do_bin_cmp!(self, a, b, ==),
                    BinaryOp::GreaterOrEqual => do_bin_cmp!(self, a, b, >=),
                    BinaryOp::LessOrEqual => do_bin_cmp!(self, a, b, <=),
                };
                self.set(dest, result);
            }
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => {
                self.mut_frame().last_block = Some(self.get_frame().block);
                if self.get(condition).to_bool() {
                    self.jump(if_true);
                } else {
                    self.jump(if_false);
                }
                return VmResult::Continue;
            }
            Op::AlwaysJump(target) => {
                self.jump(target);
                return VmResult::Continue;
            }
            Op::Phi { dest, a, b } => {
                if self.get_frame().last_block.unwrap() == a.0 {
                    self.set(dest, self.get(a.1));
                } else if self.get_frame().last_block.unwrap() == b.0 {
                    self.set(dest, self.get(b.1));
                } else {
                    panic!("Invalid Phi prev block.");
                }
            }
            Op::Return(value) => {
                let result = value.map(|v| self.get(v));
                for addr in self.get_frame().allocations.clone() {
                    self.heap.free(addr, self.trace());
                }
                if self.call_stack.len() == 1 {
                    for ptr in &self.auto_free {
                        self.heap.free(*ptr, self.trace());
                    }
                }
                self.call_stack.pop().unwrap();
                return if self.call_stack.is_empty() {
                    log!("Vm Says: {:?}", result);
                    VmResult::Done(result)
                } else {
                    vmlog!("--- ret {:?}", result);
                    if let Some(ssa) = self.get_frame().return_value_register {
                        self.set(ssa, result.unwrap());
                    }
                    VmResult::Continue
                };
            }
            Op::Call {
                func_name,
                args,
                return_value_dest,
                kind,
            } => {
                let func = self.module.get_internal_func(&func_name);
                let arg_values = args.iter().map(|ssa| self.get(*ssa)).collect::<Vec<_>>();
                match kind {
                    FuncSource::Internal => {
                        let func = func.expect("Function not found.");
                        assert_eq!(args.len(), func.signature.param_types.len());
                        self.mut_frame().return_value_register = return_value_dest;
                        self.push_frame(func);
                        self.init_params(arg_values.into_iter());
                        return VmResult::Continue;
                    }
                    FuncSource::External => {
                        assert!(func.is_none());
                        let result = self.call_libc_for_tests(&func_name, &arg_values);
                        if let Some(dest) = return_value_dest {
                            self.set(dest, result);
                        }
                    }
                }
            }
            Op::StackAlloc { dest, ty, count } => {
                let size = self.module.size_of(&ty) * count;
                let addr = self.heap.malloc(size, self.trace());
                self.mut_frame().allocations.push(addr);
                self.mut_frame()
                    .registers
                    .insert(dest, VmValue::Pointer(addr));
                vmlog!("--- Stack {:?} = {:?} ZEROED", addr, ty);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let addr = self.get(addr);
                let ty = self.type_of(value_dest);
                let value = self.heap.as_ref(addr.to_ptr(), self.module.size_of(ty));
                vmlog!("--- {:?} = *{:?}", value_dest, addr);
                let value = VmValue::from_bytes(value, ty, self.module);
                self.set(value_dest, value);
            }
            Op::StoreToPtr { addr, value_source } => {
                let addr = self.get(addr);
                let value = self.get(value_source);
                let ty = self.type_of(value_source);
                let source_bytes = value.to_bytes(self, ty, self.module);
                let dest_bytes = self.heap.as_mut(addr.to_ptr(), self.module.size_of(ty));
                assert_eq!(dest_bytes.len(), source_bytes.len());
                dest_bytes.copy_from_slice(&source_bytes);
                vmlog!("--- *{:?} = {:?}", addr, value);
            }
            Op::GetFieldAddr {
                dest,
                object_addr,
                field_index,
            } => {
                let offset = ir::struct_field_offset(
                    self.module,
                    self.get_frame().function,
                    object_addr,
                    field_index,
                );
                let mut result = self.get(object_addr).to_ptr();
                result.offset += offset as u32;
                vmlog!("--- {:?} = {:?} offset {}", dest, object_addr, field_index);
                self.set(dest, VmValue::Pointer(result));
            }
            Op::ConstValue { dest, value, .. } => {
                let val = match value {
                    LiteralValue::IntNumber(value) => VmValue::U64(value),
                    LiteralValue::FloatNumber(value) => VmValue::F64(value),
                    LiteralValue::StringBytes(value) => {
                        // TODO: this is really inefficient. String constants are reallocated each time they get evaluated and all dropped when the vm ends.
                        let the_bytes = value.to_bytes_with_nul();
                        let ptr = self.heap.malloc(the_bytes.len(), self.trace());
                        self.heap
                            .as_mut(ptr, the_bytes.len())
                            .write_all(the_bytes)
                            .unwrap();
                        self.auto_free.push(ptr);
                        VmValue::Pointer(ptr)
                    }
                    LiteralValue::UninitStruct => unreachable!(),
                    LiteralValue::UninitArray(_, _) => unreachable!(),
                };
                self.set(dest, val);
            }
            Op::Cast {
                input,
                output,
                kind,
            } => {
                let in_ty = self.type_of(input);
                let out_ty = self.type_of(output);
                match kind {
                    CastType::UnsignedIntUp => {
                        let mut bytes = self.get(input).to_int().to_be_bytes();
                        match in_ty.ty {
                            ValueType::U64 => {}
                            ValueType::U8 => {
                                bytes[0..7].iter_mut().for_each(|v| *v = 0);
                            }
                            ValueType::U32 => {
                                bytes[0..4].iter_mut().for_each(|v| *v = 0);
                            }
                            _ => unreachable!(),
                        };
                        let v = u64::from_be_bytes(bytes.as_ref().try_into().unwrap());
                        self.set(output, VmValue::U64(v));
                    }
                    CastType::FloatDown => {
                        let val = self.get(input).to_float() as f32;
                        self.set(output, VmValue::F64(val as f64));
                    }
                    CastType::FloatToUInt => {
                        let val = self.get(input).to_float();
                        self.set(output, VmValue::U64(val as u64));
                    }
                    CastType::UIntToFloat => {
                        let val = self.get(input).to_int();
                        self.set(output, VmValue::F64(val as f64));
                    }
                    // TODO: type safe void pointers to structs
                    CastType::IntToPtr | CastType::PtrToInt | CastType::Bits => {
                        let bytes = self.get(input).to_bytes(self, in_ty, self.module);
                        let result = VmValue::from_bytes(&bytes, out_ty, self.module);
                        self.set(output, result);
                    }
                    CastType::IntDown
                    | CastType::FloatUp
                    | CastType::IntToBool
                    | CastType::BoolToInt => {
                        self.set(output, self.get(input));
                    }
                }
            }
        }

        self.mut_frame().ip += 1;
        VmResult::Continue
    }

    fn push_frame(&mut self, func: &'ir Function) {
        let entry_location = self.here();
        self.mut_frame().ip += 1;
        let reg_count = func.register_types.len();
        let frame = StackFrame {
            registers: IndexMap::with_capacity(reg_count),
            function: func,
            last_block: None,
            block: func.entry_point(),
            ip: 0,
            return_value_register: None,
            allocations: vec![],
            entry_location,
            // TODO: this is redundant computation on every function call
            liveness: compute_liveness(func),
        };
        self.call_stack.push(frame);
    }

    fn init_params(&mut self, args: impl Iterator<Item = VmValue>) {
        let arg_reg = self.mut_frame().function.param_registers();
        for (ssa, value) in arg_reg.zip(args) {
            self.set(ssa, value);
        }
    }

    fn jump(&mut self, target: Label) {
        self.mut_frame().last_block = Some(self.get_frame().block);
        self.mut_frame().block = target;
        self.mut_frame().ip = 0;
        vmlog!(
            "--- Jump from {:?} to {:?}",
            self.get_frame().last_block.unwrap(),
            self.get_frame().block
        );
    }

    fn set(&mut self, register: Ssa, value: VmValue) {
        self.mut_frame().registers.insert(register, value);
        vmlog!("--- {:?} = {:?}", register, value);

        let live = &self.get_frame().liveness;
        assert!(
            live.range[register].contains(&self.op_index()),
            "Set {:?} out of live range on op_i={}",
            register,
            self.op_index()
        );
    }

    pub fn get(&self, register: Ssa) -> VmValue {
        let live = &self.get_frame().liveness;
        assert!(
            live.range[register].contains(&self.op_index()),
            "Get {:?} out of live range on op_i={}",
            register,
            self.op_index()
        );
        *self
            .get_frame()
            .registers
            .get(&register)
            .unwrap_or_else(|| panic!("Failed to get register {:?}", register))
    }

    fn get_frame(&self) -> &StackFrame<'ir> {
        self.call_stack.last().unwrap()
    }

    fn mut_frame(&mut self) -> &mut StackFrame<'ir> {
        self.call_stack.last_mut().unwrap()
    }

    fn call_libc_for_tests(&mut self, name: &str, args: &[VmValue]) -> VmValue {
        match name {
            "sin" => {
                assert_eq!(args.len(), 1);
                let angle = args[0].to_float();
                VmValue::F64(angle.sin())
            }
            "printf" => {
                log!("Called printf {:?}", args);
                VmValue::U64(0)
            }
            "puts" => {
                log!("Called puts {:?}", args);
                VmValue::U64(0)
            }
            "malloc" => {
                assert_eq!(args.len(), 1);
                let size = args[0].to_int() as usize;
                let ptr = self.heap.malloc(size, self.trace());
                VmValue::Pointer(ptr)
            }
            "free" => {
                assert_eq!(args.len(), 1);
                let ptr = args[0].to_ptr();
                self.heap.free(ptr, self.trace());
                VmValue::Uninit
            }
            "memcpy" => {
                assert_eq!(args.len(), 3);
                let dest = args[0].to_ptr();
                let src = args[1].to_ptr();
                let size = args[2].to_int();
                VmValue::Uninit
            }
            "print_vm_stack_trace" => {
                vmlog!("{:?}", self.trace());
                VmValue::Uninit
            }
            "exit" => {
                assert_eq!(args.len(), 1);
                let status = args[0].to_int();
                panic!("Vm exit with status code {}", status)
            }
            "abort" => {
                panic!("Vm called abort()")
            }
            _ => {
                panic!("Called unrecognised function {}", name)
            }
        }
    }

    fn trace(&self) -> StackTrace {
        let mut data = vec![];

        for frame in &self.call_stack {
            data.push(frame.entry_location.clone());
        }
        data.push(self.here());

        StackTrace { data }
    }

    fn here(&self) -> Location {
        let lines = self.get_frame().function.blocks_debug_lines[self.get_frame().block.index()]
            .as_ref()
            .unwrap();
        Location {
            tick: self.tick,
            line: lines[self.get_frame().ip],
            instruction: self.get_frame().ip,
            block: self.get_frame().block,
            func_name: self.get_frame().function.signature.name.clone(),
        }
    }

    fn op_index(&self) -> usize {
        self.get_frame().ip
            + 1
            + self.get_frame().liveness.block_start_index[self.get_frame().block]
    }

    fn type_of(&self, ssa: Ssa) -> &CType {
        self.get_frame().function.register_types.get(&ssa).unwrap()
    }
}

fn bool_to_int(b: bool) -> u64 {
    if b {
        1
    } else {
        0
    }
}

impl VmValue {
    fn to_bytes(&self, vm: &Vm, ty: &CType, ir: &Module) -> Box<[u8]> {
        let result = match self {
            VmValue::U64(v) => {
                assert!(!ty.is_ptr());
                match ty.ty {
                    ValueType::U64 => v.to_le_bytes().to_vec().into_boxed_slice(),
                    ValueType::U8 => (*v as u8).to_le_bytes().to_vec().into_boxed_slice(),
                    ValueType::U32 => (*v as u32).to_le_bytes().to_vec().into_boxed_slice(),
                    ValueType::Bool => v.to_le_bytes().to_vec().into_boxed_slice(),
                    _ => unreachable!("to bytes of {:?}", ty.ty),
                }
            }
            VmValue::F64(v) => {
                assert!(!ty.is_ptr());
                match ty.ty {
                    ValueType::F64 => v.to_le_bytes().to_vec().into_boxed_slice(),
                    ValueType::F32 => (*v as f32).to_le_bytes().to_vec().into_boxed_slice(),
                    _ => unreachable!(),
                }
            }
            VmValue::Uninit => todo!(),
            VmValue::Pointer(p) => {
                assert!(ty.is_ptr());
                let mut bytes = p.offset.to_le_bytes().to_vec();
                bytes.extend(p.id.to_le_bytes());
                bytes.into_boxed_slice()
            }
        };
        assert_eq!(
            result.len(),
            ir.size_of(ty),
            "Failed write {:?} to {} bytes",
            ty,
            result.len()
        );

        result
    }

    fn from_bytes(bytes: &[u8], ty: &CType, ir: &Module) -> VmValue {
        assert_eq!(
            bytes.len(),
            ir.size_of(ty),
            "Failed read {:?} from {} bytes ",
            ty,
            bytes.len()
        );
        if ty.is_ptr() {
            let offset = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
            let id = u32::from_le_bytes(bytes[4..].try_into().unwrap());
            let ptr = Ptr { id, offset };
            return VmValue::Pointer(ptr);
        }

        match ty.ty {
            ValueType::U64 | ValueType::Bool => {
                VmValue::U64(u64::from_le_bytes(bytes.try_into().unwrap()))
            }
            ValueType::U8 => VmValue::U64(bytes[0] as u64),
            ValueType::U32 => VmValue::U64(u32::from_le_bytes(bytes.try_into().unwrap()) as u64),
            ValueType::F64 => VmValue::F64(f64::from_le_bytes(bytes.try_into().unwrap())),
            ValueType::F32 => VmValue::F64(f32::from_le_bytes(bytes.try_into().unwrap()) as f64),
            ValueType::U16 => todo!(),
            ValueType::Struct(_) => todo!(),
            ValueType::Void => unreachable!(),
        }
    }

    fn to_int(&self) -> u64 {
        if let &VmValue::U64(value) = self {
            return value;
        }
        panic!("Not an int");
    }

    fn to_float(&self) -> f64 {
        if let &VmValue::F64(value) = self {
            return value;
        }
        panic!("Not a float");
    }

    fn to_ptr(&self) -> Ptr {
        if let &VmValue::Pointer(value) = self {
            return value;
        }
        panic!("Not a pointer");
    }

    fn to_bool(&self) -> bool {
        self.to_int() != 0
    }
}

impl VmResult {
    pub fn to_int(&self) -> u64 {
        match self {
            VmResult::Continue => unreachable!(),
            VmResult::Done(val) => val.unwrap().to_int(),
        }
    }

    pub fn to_float(&self) -> f64 {
        match self {
            VmResult::Continue => unreachable!(),
            VmResult::Done(val) => val.unwrap().to_float(),
        }
    }
}

#[derive(Default)]
struct DebugAlloc {
    count: u32,
    allocations: IndexMap<u32, Allocation>,
}

#[derive(Debug)]
struct Allocation {
    data: Box<[u8]>,
    id: u32,
    alloc_at: StackTrace,
    free_at: Option<StackTrace>,
}

impl Allocation {
    pub(crate) fn debug(&self) -> String {
        format!(
            "ID: {}. Size: {} bytes.\n    Allocated: {{\n{:?}}}. \n    Dropped: {{\n{}}}.",
            self.id,
            self.data.len(),
            self.alloc_at,
            match &self.free_at {
                None => {
                    "Never".to_string()
                }
                Some(loc) => format!("{:?}", loc),
            }
        )
    }
}

impl Debug for StackTrace {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for (i, data) in self.data.iter().enumerate() {
            for _ in 0..i {
                write!(f, "  ")?;
            }
            writeln!(
                f,
                "{} at [line={}, {:?}, ip={}, tick={}]",
                data.func_name, data.line, data.block, data.instruction, data.tick
            )?;
        }
        Ok(())
    }
}

#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
pub struct Ptr {
    id: u32,
    offset: u32,
}

// TODO: since this isn't a real allocator, you can't pass the pointers it produces to external functions.
impl DebugAlloc {
    fn malloc(&mut self, size: usize, alloc_at: StackTrace) -> Ptr {
        assert!(size < u32::MAX as usize);
        self.count += 1;
        self.allocations.insert(
            self.count,
            Allocation {
                data: vec![0; size].into_boxed_slice(),
                id: self.count,
                alloc_at,
                free_at: None,
            },
        );
        Ptr {
            id: self.count,
            offset: 0,
        }
    }

    fn free(&mut self, addr: Ptr, free_at: StackTrace) {
        assert_eq!(addr.offset, 0);
        let allocation = self.allocations.get_mut(&addr.id).unwrap_or_else(|| {
            panic!(
                "Freed pointer that wasn't allocated {:?} {:?}",
                addr, free_at
            )
        });
        assert!(
            allocation.free_at.is_none(),
            "Double free {}",
            allocation.debug()
        );
        allocation.free_at = Some(free_at);
        // Actually release the memory.
        allocation.data = vec![].into_boxed_slice();
    }

    fn assert_no_leaks(&self) {
        // TODO: the vm could even notice when you dropped the last reference to this allocation if i really wanted.
        assert_eq!(
            self.allocations
                .iter()
                .filter(|(_, alloc)| alloc.free_at.is_none())
                .map(|(_, alloc)| {
                    vmlog!("Memory leak {}", alloc.debug());
                })
                .count(),
            0
        );
    }

    fn as_ref(&self, addr: Ptr, size: usize) -> &[u8] {
        let allocation = self.allocations.get(&addr.id).unwrap();
        assert!(
            allocation.free_at.is_none(),
            "Read dropped memory {}",
            allocation.debug()
        );
        let start = addr.offset as usize;
        let end = start + size;
        assert!(
            end <= allocation.data.len(),
            "Tried to read [{}..{}] from length {}. {}",
            start,
            end,
            allocation.data.len(),
            allocation.debug()
        );
        &allocation.data[start..end]
    }

    fn as_mut(&mut self, addr: Ptr, size: usize) -> &mut [u8] {
        let allocation = self.allocations.get_mut(&addr.id).unwrap();
        assert!(
            allocation.free_at.is_none(),
            "Write dropped memory {}",
            allocation.debug()
        );
        let start = addr.offset as usize;
        let end = start + size;
        assert!(
            end <= allocation.data.len(),
            "Tried to read [{}..{}] from length {}. {}",
            start,
            end,
            allocation.data.len(),
            allocation.debug()
        );
        &mut allocation.data[start..end]
    }
}

pub mod macros {
    macro_rules! do_bin_math {
        ($self:ident, $a:ident, $b:ident, $op:tt) => {{
            let ty_a = $self.get_frame().function.type_of(&$a);
            let ty_b = $self.get_frame().function.type_of(&$b);
            if ty_a.is_raw_int() && ty_b.is_raw_int() {
                VmValue::U64($self.get($a).to_int() $op $self.get($b).to_int())
            } else if ty_a.is_raw_float() && ty_b.is_raw_float() {
                VmValue::F64($self.get($a).to_float() $op $self.get($b).to_float())
            } else {
                unreachable!()
            }
        }};
    }

    macro_rules! do_bin_cmp {
        ($self:ident, $a:ident, $b:ident, $op:tt) => {{
            let ty_a = $self.get_frame().function.type_of(&$a);
            let ty_b = $self.get_frame().function.type_of(&$b);
            if ty_a.is_raw_int() && ty_b.is_raw_int() {
                VmValue::U64(bool_to_int($self.get($a).to_int() $op $self.get($b).to_int()))
            } else if ty_a.is_raw_float() && ty_b.is_raw_float() {
                VmValue::U64(bool_to_int($self.get($a).to_float() $op $self.get($b).to_float()))
            } else {
                unreachable!()
            }
        }};
    }

    pub(crate) use do_bin_cmp;
    pub(crate) use do_bin_math;
}
