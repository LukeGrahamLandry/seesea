//! An interpreter for my IR for inspecting the temporary registers while debugging codegen.
//! A GUI that showed where you were in source / tokens / AST / IR side by side and let you step forward would be really cool.
//! For now it just gives me another backend so if it agrees on results with LLVm then I know my IR gen was the problem.
#![allow(unused)]

use crate::ast::{BinaryOp, CType, LiteralValue, ValueType};
use crate::ir;
use crate::ir::{CastType, Function, Label, Module, Op, Ssa};
use crate::macros::vm::{do_bin_cmp, do_bin_math};
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::mem;
use std::mem::size_of;
use std::ops::Add;
use std::rc::Rc;

// TODO: @Speed group allocations and reuse memory (especially for the stack + registers)
pub struct Vm<'ir> {
    module: &'ir Module,
    call_stack: Vec<StackFrame<'ir>>,
    stack_address_counter: usize,
    tick: usize,
    tick_limit: Option<usize>,
    heap: DebugAlloc,
    strings: Vec<String>,
}

struct StackFrame<'ir> {
    registers: HashMap<Ssa, VmValue>,
    function: &'ir Function,
    last_block: Option<Label>,
    block: Label,
    ip: usize,
    return_value_register: Option<Ssa>,
    allocations: Vec<Ptr>,
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
    ConstString(usize),
    Pointer(Ptr),
}

#[derive(PartialEq, Clone, Debug)]
struct Location {
    tick: usize,
    line: usize,
    instruction: usize,
    func_name: Rc<str>,
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
            strings: vec![],
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
        println!("Start VM Eval.");
        let mut vm = Vm::new(module);
        vm.tick_limit = Some(250); // TODO: move limit into tests file
        let func = module.get_func(function_name).expect("Function not found");
        let frame = StackFrame {
            registers: HashMap::new(),
            function: func,
            last_block: None,
            block: func.entry_point(),
            ip: 0,
            return_value_register: None,
            allocations: vec![],
        };
        vm.call_stack.push(frame);
        vm.init_params(args.iter().copied());

        loop {
            let result = vm.tick();
            if let VmResult::Done(_) = result {
                vm.heap.assert_no_leaks();
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

        println!(
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
        println!("Op: {}", self.get_frame().function.print(&op));
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
                    BinaryOp::Equal => do_bin_cmp!(self, a, b, ==),
                    BinaryOp::Assign => {
                        unreachable!("IR must be in SSA form and have no BinaryOp::Assign")
                    }
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
            Op::Return { value } => {
                let result = value.map(|v| self.get(v));
                println!("--- ret {:?}", result);
                for addr in self.get_frame().allocations.clone() {
                    self.heap.free(addr, self.now());
                }
                self.call_stack.pop().unwrap();
                return if self.call_stack.is_empty() {
                    VmResult::Done(result)
                } else {
                    let ssa = self.get_frame().return_value_register.unwrap();
                    self.set(ssa, result.unwrap());
                    VmResult::Continue
                };
            }
            Op::Call {
                func_name,
                args,
                return_value_dest,
            } => {
                let arg_values = args.iter().map(|ssa| self.get(*ssa)).collect::<Vec<_>>();
                let func = match self.module.get_func(&func_name) {
                    Some(f) => f,
                    None => {
                        let result = self.call_libc_for_tests(&func_name, &arg_values);
                        if let Some(dest) = return_value_dest {
                            self.set(dest, result);
                        }
                        self.mut_frame().ip += 1;
                        return VmResult::Continue;
                    }
                };

                self.mut_frame().return_value_register = return_value_dest;
                self.mut_frame().ip += 1;
                let reg_count = self.mut_frame().function.register_types.len();
                let frame = StackFrame {
                    registers: HashMap::with_capacity(reg_count),
                    function: func,
                    last_block: None,
                    block: func.entry_point(),
                    ip: 0,
                    return_value_register: None,
                    allocations: vec![],
                };
                self.call_stack.push(frame);
                self.init_params(arg_values.into_iter());
                return VmResult::Continue;
            }
            Op::StackAlloc { dest, ty, count } => {
                let size = self.module.size_of(&ty) * count;
                let addr = self.heap.malloc(size, self.now());
                self.mut_frame().allocations.push(addr);
                self.mut_frame()
                    .registers
                    .insert(dest, VmValue::Pointer(addr));
                println!("--- Stack {:?} = {:?} ZEROED", addr, ty);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let addr = self.get(addr);
                let ty = self
                    .get_frame()
                    .function
                    .register_types
                    .get(&value_dest)
                    .unwrap();
                let value = self.heap.as_ref(addr.to_ptr(), self.module.size_of(ty));
                println!("--- {:?} = *{:?}", value_dest, addr);
                let value = VmValue::from_bytes(value, ty, self.module);
                self.set(value_dest, value);
            }
            Op::StoreToPtr { addr, value_source } => {
                let addr = self.get(addr);
                let value = self.get(value_source);
                let ty = self
                    .get_frame()
                    .function
                    .register_types
                    .get(&value_source)
                    .unwrap();
                let source_bytes = value.to_bytes(ty, self.module);
                let dest_bytes = self.heap.as_mut(addr.to_ptr(), self.module.size_of(ty));
                assert_eq!(dest_bytes.len(), source_bytes.len());
                dest_bytes.copy_from_slice(&source_bytes);
                println!("--- *{:?} = {:?}", addr, value);
            }
            Op::GetFieldAddr {
                dest,
                object_addr,
                field_index,
            } => {
                let mut offset = 0;
                let ty = self
                    .get_frame()
                    .function
                    .register_types
                    .get(&object_addr)
                    .unwrap()
                    .deref_type();
                let struct_def = self.module.get_struct(ty.struct_name()).unwrap();
                for i in 0..field_index {
                    offset += self.module.size_of(&struct_def.fields[i].1);
                }

                let mut result = self.get(object_addr).to_ptr();
                result.offset += offset as u32;
                println!("--- {:?} = {:?} offset {}", dest, object_addr, field_index);
                self.set(dest, VmValue::Pointer(result));
            }
            Op::ConstValue { dest, value, .. } => {
                let val = match value {
                    LiteralValue::IntNumber(value) => VmValue::U64(value),
                    LiteralValue::FloatNumber(value) => VmValue::F64(value),
                    LiteralValue::StringBytes(value) => {
                        self.strings.push(value.to_string());
                        VmValue::ConstString(self.strings.len() - 1)
                    }
                };
                self.set(dest, val);
            }
            Op::Cast {
                input,
                output,
                kind,
            } => {
                let in_ty = self
                    .get_frame()
                    .function
                    .register_types
                    .get(&input)
                    .unwrap();
                let out_ty = self
                    .get_frame()
                    .function
                    .register_types
                    .get(&output)
                    .unwrap();
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
                    CastType::IntDown => {
                        self.set(output, self.get(input));
                    }
                    CastType::FloatUp => {
                        self.set(output, self.get(input));
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
                    CastType::IntToPtr | CastType::PtrToInt | CastType::Bits => {
                        let bytes = self.get(input).to_bytes(in_ty, self.module);
                        let result = VmValue::from_bytes(&bytes, out_ty, self.module);
                        self.set(output, result);
                    }
                }
            }
        }

        self.mut_frame().ip += 1;
        VmResult::Continue
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
        println!(
            "--- Jump from {:?} to {:?}",
            self.get_frame().last_block.unwrap(),
            self.get_frame().block
        );
    }

    fn set(&mut self, register: Ssa, value: VmValue) {
        self.mut_frame().registers.insert(register, value);
        println!("--- {:?} = {:?}", register, value);
    }

    pub fn get(&self, register: Ssa) -> VmValue {
        *self.get_frame().registers.get(&register).unwrap()
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
                println!("Called printf {:?}", args);
                VmValue::U64(0)
            }
            "malloc" => {
                assert_eq!(args.len(), 1);
                let size = args[0].to_int() as usize;
                let ptr = self.heap.malloc(size, self.now());
                VmValue::Pointer(ptr)
            }
            "free" => {
                assert_eq!(args.len(), 1);
                let ptr = args[0].to_ptr();
                self.heap.free(ptr, self.now());
                VmValue::Uninit
            }
            _ => {
                panic!("Called unrecognised function {}", name)
            }
        }
    }

    fn now(&self) -> Location {
        Location {
            tick: self.tick,
            line: 0,
            instruction: self.get_frame().ip,
            func_name: self.get_frame().function.signature.name.clone(),
        }
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
    fn to_bytes(&self, ty: &CType, ir: &Module) -> Box<[u8]> {
        let result = match self {
            VmValue::U64(v) => {
                assert!(!ty.is_ptr());
                match ty.ty {
                    ValueType::U64 => v.to_le_bytes().to_vec().into_boxed_slice(),
                    ValueType::U8 => (*v as u8).to_le_bytes().to_vec().into_boxed_slice(),
                    ValueType::U32 => (*v as u32).to_le_bytes().to_vec().into_boxed_slice(),
                    _ => unreachable!(),
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
            VmValue::ConstString(_) => todo!(),
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
            ValueType::U64 => VmValue::U64(u64::from_le_bytes(bytes.try_into().unwrap())),
            ValueType::U8 => VmValue::U64(bytes[0] as u64),
            ValueType::U32 => VmValue::U64(u32::from_le_bytes(bytes.try_into().unwrap()) as u64),
            ValueType::F64 => VmValue::F64(f64::from_le_bytes(bytes.try_into().unwrap())),
            ValueType::F32 => VmValue::F64(f32::from_le_bytes(bytes.try_into().unwrap()) as f64),
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
    allocations: HashMap<u32, Allocation>,
}

struct Allocation {
    data: Box<[u8]>,
    id: u32,
    alloc_at: Location,
    free_at: Option<Location>,
}

impl Allocation {
    pub(crate) fn debug(&self) -> String {
        format!(
            "\n    Allocated: [{:?}]. \n    Dropped: [{}].",
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

#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
pub struct Ptr {
    id: u32,
    offset: u32,
}

impl DebugAlloc {
    fn malloc(&mut self, size: usize, alloc_at: Location) -> Ptr {
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

    fn free(&mut self, addr: Ptr, free_at: Location) {
        assert_eq!(addr.offset, 0);
        let allocation = self.allocations.get_mut(&addr.id).unwrap();
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
                    println!("Memory leak {}", alloc.debug());
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
