//! An interpreter for my IR for inspecting the temporary registers while debugging codegen.
//! A GUI that showed where you were in source / tokens / AST / IR side by side and let you step forward would be really cool.
//! For now it just gives me another backend so if it agrees on results with LLVm then I know my IR gen was the problem.
#![allow(unused)]

use crate::ast::{BinaryOp, LiteralValue};
use crate::ir::{Function, Label, Module, Op, Ssa};
use crate::macros::vm::{do_bin_cmp, do_bin_math};
use std::collections::HashMap;

pub struct Vm<'ir> {
    module: &'ir Module,
    call_stack: Vec<StackFrame<'ir>>,
    stack_address_counter: usize,
    tick: usize,
    tick_limit: Option<usize>,
}

struct StackFrame<'ir> {
    registers: HashMap<Ssa, VmValue>,
    function: &'ir Function,
    last_block: Option<Label>,
    block: Label,
    ip: usize,
    return_value_register: Option<Ssa>,
    memory: HashMap<usize, VmValue>,
}

pub enum VmResult {
    Continue,
    Done(Option<VmValue>),
}

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum VmValue {
    U64(u64),
    F64(f64),
    StackAddress(usize),
    Uninit,
    ConstString(&'static str),
}

impl<'ir> Vm<'ir> {
    pub fn new(module: &Module) -> Vm {
        Vm {
            module,
            call_stack: vec![],
            stack_address_counter: 0,
            tick: 0,
            tick_limit: None,
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
            memory: HashMap::new(),
        };
        vm.call_stack.push(frame);
        vm.init_params(args.iter().copied());

        loop {
            let result = vm.tick();
            if let VmResult::Done(_) = result {
                return result;
            }
        }
    }

    pub fn tick(&mut self) -> VmResult {
        // CLion doesn't want to show me the output while it hangs on a mistake in my tests that causes an infinite loop.
        if let Some(tick_limit) = self.tick_limit {
            if self.tick > tick_limit {
                panic!("Damn bro the VM's been running for {} ticks... maybe check for infinite loops or remove the tick_limit", self.tick);
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
        // TODO: while Op contains a string for function name, this clone means function calls are super slow.
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
                self.call_stack.pop();
                println!("--- ret {:?}", result);
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
                let frame = StackFrame {
                    registers: HashMap::new(),
                    function: func,
                    last_block: None,
                    block: func.entry_point(),
                    ip: 0,
                    return_value_register: None,
                    memory: HashMap::new(),
                };
                self.call_stack.push(frame);
                self.init_params(arg_values.into_iter());
                return VmResult::Continue;
            }
            Op::StackAlloc { dest, ty, count } => {
                assert_eq!(count, 1);
                let addr = self.next_address();
                if ty.is_struct() {
                    let struct_def = self.module.get_struct(ty.struct_name()).unwrap();
                    for (i, (_, ty)) in struct_def.fields.iter().enumerate() {
                        if ty.is_struct() {
                            todo!()
                        }
                        self.mut_frame()
                            .memory
                            .insert(addr.offset(i).to_fake_ptr(), VmValue::Uninit);
                    }
                } else {
                    self.mut_frame()
                        .memory
                        .insert(addr.to_fake_ptr(), VmValue::Uninit);
                }
                self.mut_frame().registers.insert(dest, addr);
                println!("--- Stack {:?} = {:?} {:?}", addr, VmValue::Uninit, ty);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let addr = self.get(addr);
                let value = *self.get_stack_address(addr);
                println!("--- {:?} = *{:?}", value_dest, addr);
                self.set(value_dest, value);
            }
            Op::StoreToPtr { addr, value_source } => {
                let addr = self.get(addr);
                let value = self.get(value_source);
                *self.mut_stack_address(addr) = value;
                println!("--- *{:?} = {:?}", addr, value);
            }
            Op::GetFieldAddr {
                dest,
                object_addr,
                field_index,
            } => {
                let result = self.get(object_addr).offset(field_index);
                println!("--- {:?} = {:?} offset {}", dest, object_addr, field_index);
                self.set(dest, result);
            }
            Op::ConstValue { dest, value, .. } => {
                let val = match value {
                    LiteralValue::IntNumber(value) => VmValue::U64(value),
                    LiteralValue::FloatNumber(value) => VmValue::F64(value),
                    LiteralValue::StringBytes(value) => {
                        // TODO: leak! but vm is just for tests so doesn't really matter
                        //       needs to be a pointer to a u8
                        //       for now im just doing enough that the vm can run programs that use printf
                        let val = Box::leak(value);
                        VmValue::ConstString(val)
                    }
                };
                self.set(dest, val);
            }
            _ => todo!(),
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

    fn next_address(&mut self) -> VmValue {
        self.stack_address_counter += 1;
        VmValue::StackAddress(self.stack_address_counter)
    }

    fn get_stack_address(&self, addr: VmValue) -> &VmValue {
        assert!(addr.is_stack_ptr());
        for frame in self.call_stack.iter().rev() {
            if let Some(value) = frame.memory.get(&addr.to_fake_ptr()) {
                return value;
            }
        }
        panic!("Tried to access dropped stack variable");
    }

    fn mut_stack_address(&mut self, addr: VmValue) -> &mut VmValue {
        assert!(addr.is_stack_ptr());
        for frame in self.call_stack.iter_mut().rev() {
            if let Some(value) = frame.memory.get_mut(&addr.to_fake_ptr()) {
                return value;
            }
        }
        panic!("Tried to access dropped stack variable");
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
            _ => {
                panic!("Called unrecognised function {}", name)
            }
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

    fn to_fake_ptr(&self) -> usize {
        if let &VmValue::StackAddress(value) = self {
            return value;
        }
        panic!("Not a StackAddress");
    }

    fn to_bool(&self) -> bool {
        self.to_int() != 0
    }

    fn is_stack_ptr(&self) -> bool {
        matches!(self, VmValue::StackAddress(_))
    }

    fn offset(&self, offset: usize) -> VmValue {
        match self {
            VmValue::StackAddress(addr) => VmValue::StackAddress(addr + offset),
            _ => unreachable!(),
        }
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
