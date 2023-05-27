//! An interpreter for my IR for inspecting the temporary registers while debugging codegen.
//! A GUI that showed where you were in source / tokens / AST / IR side by side and let you step forward would be really cool.
//! For now it just gives me another backend so if it agrees on results with LLVm then I know my IR gen was the problem.

use crate::ast::BinaryOp;
use crate::ir::{Function, Label, Module, Op, Ssa};
use std::collections::HashMap;

pub struct Vm<'ir> {
    module: &'ir Module,
    call_stack: Vec<StackFrame<'ir>>,
}

struct StackFrame<'ir> {
    registers: HashMap<Ssa, u64>,
    function: &'ir Function,
    last_block: Option<Label>,
    block: Label,
    ip: usize,
    return_value_register: Option<Ssa>,
}

pub enum VmResult {
    Continue,
    Done(Option<u64>),
}

impl<'ir> Vm<'ir> {
    pub fn new(module: &Module) -> Vm {
        Vm {
            module,
            call_stack: vec![],
        }
    }

    pub fn eval(module: &Module, function_name: &str, args: &[u64]) -> Option<u64> {
        println!("Start VM Eval.");
        let mut vm = Vm::new(module);
        let func = module.get_func(function_name).expect("Function not found");
        let frame = StackFrame {
            registers: HashMap::new(),
            function: func,
            last_block: None,
            block: func.entry_point(),
            ip: 0,
            return_value_register: None,
        };
        vm.call_stack.push(frame);
        vm.init_params(args.iter().copied());

        loop {
            if let VmResult::Done(result) = vm.tick() {
                return result;
            }
        }
    }

    pub fn tick(&mut self) -> VmResult {
        println!(
            "[{:?}] ip = {}; {} (frame = {})",
            self.get_frame().block,
            self.get_frame().ip,
            self.get_frame().function.sig.name,
            self.call_stack.len()
        );
        // let mut dbg_reg = self.registers.iter().collect::<Vec<_>>();
        // dbg_reg.sort_by(|a, b| a.0 .0.cmp(&b.0 .0));
        // println!("Registers: {:?}", dbg_reg);
        let ops = &self.get_frame().function.blocks[self.get_frame().block.index()];
        // TODO: while Op contains a string for function name, this clone means function calls are super slow.
        let op = ops[self.get_frame().ip].clone();
        println!("Op: {}", self.get_frame().function.print(&op));
        match op {
            Op::ConstInt { dest, value } => {
                self.set(dest, value);
            }
            Op::Binary { dest, a, b, kind } => {
                let result = match kind {
                    BinaryOp::Add => self.get(a) + self.get(b),
                    BinaryOp::Subtract => self.get(a) - self.get(b),
                    BinaryOp::GreaterThan => int_cast(self.get(a) > self.get(b)),
                    BinaryOp::LessThan => int_cast(self.get(a) < self.get(b)),
                    BinaryOp::Assign => {
                        unreachable!("IR must be in SSA form and have no BinaryOp::Assign")
                    }
                    _ => todo!(),
                };
                self.set(dest, result);
            }
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => {
                self.mut_frame().last_block = Some(self.get_frame().block);
                if self.get(condition) != 0 {
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
                let func = self
                    .module
                    .get_func(&func_name)
                    .expect("Function not found.");
                self.mut_frame().return_value_register = Some(return_value_dest);
                self.mut_frame().ip += 1;
                let arg_values = args.iter().map(|ssa| self.get(*ssa)).collect::<Vec<_>>();
                let frame = StackFrame {
                    registers: HashMap::new(),
                    function: func,
                    last_block: None,
                    block: func.entry_point(),
                    ip: 0,
                    return_value_register: None,
                };
                self.call_stack.push(frame);
                self.init_params(arg_values.into_iter());
                return VmResult::Continue;
            }
            Op::StackAlloc { .. } | Op::LoadFromPtr { .. } | Op::StoreToPtr { .. } | Op::Move { .. } => {
                todo!()
            }
        }

        self.mut_frame().ip += 1;
        VmResult::Continue
    }

    fn init_params(&mut self, args: impl Iterator<Item = u64>) {
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

    fn set(&mut self, register: Ssa, value: u64) {
        self.mut_frame().registers.insert(register, value);
        println!("--- {:?} = {}", register, value);
    }

    pub fn get(&self, register: Ssa) -> u64 {
        *self.get_frame().registers.get(&register).unwrap()
    }

    fn get_frame(&self) -> &StackFrame<'ir> {
        self.call_stack.last().unwrap()
    }

    fn mut_frame(&mut self) -> &mut StackFrame<'ir> {
        self.call_stack.last_mut().unwrap()
    }
}

fn int_cast(b: bool) -> u64 {
    if b {
        1
    } else {
        0
    }
}
