//! An interpreter for my IR for inspecting the temporary registers while debugging codegen.
//! A GUI that showed where you were in source / tokens / AST / IR side by side and let you step forward would be really cool.
//! For now it just gives me another backend so if it agrees on results with LLVm then I know my IR gen was the problem.

use crate::ast::BinaryOp;
use crate::ir::{Function, Label, Op, Ssa};
use std::collections::HashMap;

pub struct Vm<'ir> {
    registers: HashMap<Ssa, u64>,
    function: &'ir Function,
    block: Label,
    last_block: Option<Label>,
    ip: usize,
}

pub enum VmResult {
    Continue,
    Done(Option<u64>),
}

impl<'ir> Vm<'ir> {
    pub fn eval(function: &Function, args: &[u64]) -> Option<u64> {
        println!("Start VM Eval.");
        let mut vm = Vm {
            registers: HashMap::new(),
            function,
            block: function.entry_point(),
            last_block: None,
            ip: 0,
        };

        for (ssa, value) in function.param_registers().zip(args.iter()) {
            vm.set(ssa, *value);
        }

        loop {
            if let VmResult::Done(result) = vm.tick() {
                return result;
            }
        }
    }

    pub fn tick(&mut self) -> VmResult {
        println!("[{:?}]: {}", self.block, self.ip);
        let mut dbg_reg = self.registers.iter().collect::<Vec<_>>();
        dbg_reg.sort_by(|a, b| a.0 .0.cmp(&b.0 .0));
        println!("Registers: {:?}", dbg_reg);
        let ops = &self.function.blocks[self.block.index()];
        let op = ops[self.ip];
        println!("Op: {}", self.function.print(&op));
        println!("---");
        match op {
            Op::ConstInt { dest, value } => {
                self.set(dest, value);
            }
            Op::Binary { dest, a, b, kind } => {
                let result = match kind {
                    BinaryOp::Add => self.get(a) + self.get(b),
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
                self.last_block = Some(self.block);
                if self.get(condition) != 0 {
                    self.block = if_true;
                } else {
                    self.block = if_false;
                }
                self.ip = 0;
                return VmResult::Continue;
            }
            Op::AlwaysJump(target) => {
                self.last_block = Some(self.block);
                self.block = target;
                self.ip = 0;
                return VmResult::Continue;
            }
            Op::Phi { dest, a, b } => {
                if self.last_block.unwrap() == a.0 {
                    self.set(dest, self.get(a.1));
                } else if self.last_block.unwrap() == b.0 {
                    self.set(dest, self.get(b.1));
                } else {
                    panic!("Invalid Phi prev block.");
                }
            }
            Op::Return { value } => {
                let result = value.map(|v| self.get(v));
                self.registers.clear();
                return VmResult::Done(result);
            }
            Op::StackAlloc { .. } | Op::Load { .. } | Op::Store { .. } | Op::Move { .. } => {
                todo!()
            }
        }

        self.ip += 1;
        VmResult::Continue
    }

    fn set(&mut self, register: Ssa, value: u64) {
        self.registers.insert(register, value);
    }

    pub fn get(&self, register: Ssa) -> u64 {
        *self.registers.get(&register).unwrap()
    }
}

fn int_cast(b: bool) -> u64 {
    if b {
        1
    } else {
        0
    }
}
