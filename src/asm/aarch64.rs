use crate::asm::aarch64_out::{AsmOp, EmitAarch64, RegKind, Register};
use crate::ast::{BinaryOp, LiteralValue, ValueType};
use crate::ir::{Function, Label, Module, Op, Ssa};
use std::collections::{HashMap, HashSet, VecDeque};

struct Aarch64Builder<'ir, Emitter: EmitAarch64> {
    emitter: Emitter,
    ir: Option<&'ir Module>,
    func: Option<&'ir Function>,
    stack_remaining: isize,
    total_stack_size: usize,
    ssa_offsets: HashMap<Ssa, usize>,
    active_registers: Vec<Register>,
    unused_registers: Vec<Register>,
}

// TODO: how do we know when an ssa is no longer live? do i need to have an Op::Free(Ssa) when all reads are over?

pub fn build_asm<Emitter: EmitAarch64>(ir: &Module) -> Emitter {
    let mut builder = Aarch64Builder {
        emitter: Emitter::default(),
        ir: None,
        func: None,
        stack_remaining: 0,
        total_stack_size: 0,
        ssa_offsets: Default::default(),
        active_registers: Default::default(),
        unused_registers: Default::default(),
    };
    builder.run(ir);
    builder.emitter
}

const SP: Register = Register(RegKind::Int64, 31);

impl<'ir, Emitter: EmitAarch64> Aarch64Builder<'ir, Emitter> {
    fn run(&mut self, ir: &'ir Module) {
        self.ir = Some(ir);
        for function in &ir.functions {
            self.emit_function(function);
        }
    }

    fn emit_function(&mut self, function: &'ir Function) {
        self.emitter.start_func(&function.signature.name);
        // Reserve stack space (stack grows downwards).
        // TODO: needs to be 16 byte aligned?
        self.func = Some(function);
        self.total_stack_size = function.required_stack_bytes + (function.register_types.len() * 8);
        self.stack_remaining = function.required_stack_bytes as isize;
        self.emitter
            .simple_with_const(AsmOp::SUB, SP, SP, self.total_stack_size);
        self.unused_registers = vec![
            Register(RegKind::Int64, 9),
            Register(RegKind::Int64, 10),
            Register(RegKind::Int64, 11),
            Register(RegKind::Int64, 12),
        ];

        assert_eq!(function.signature.param_names.len(), 1);
        let first_arg = self.next_reg();
        self.emitter
            .pair(AsmOp::MOV, first_arg, Register(RegKind::Int64, 0));
        self.set_ssa(&Ssa(0), first_arg);

        self.emitter.jump_to(function.entry_point());
        for (i, code) in function.blocks.iter().enumerate() {
            if let Some(code) = code {
                self.emitter.start_block(Label(i));
                for op in code {
                    self.emit_op(op);
                }
            }
        }

        assert!(self.stack_remaining >= 0);
        assert!(self.active_registers.is_empty());
    }

    fn emit_op(&mut self, op: &Op) {
        match op {
            Op::ConstValue { dest, value, kind } => {
                assert!(kind.is_raw_int());
                match value {
                    LiteralValue::IntNumber(n) => {
                        let accumulator = self.next_reg();
                        // Produce a zero
                        self.emitter
                            .simple_op(AsmOp::SUB, accumulator, accumulator, accumulator);
                        // Produce the constant
                        // assert value in range
                        self.emitter.simple_with_const(
                            AsmOp::ADD,
                            accumulator,
                            accumulator,
                            *n as usize,
                        );
                        self.set_ssa(dest, accumulator);
                    }
                    _ => todo!(),
                }
            }
            Op::Binary { dest, a, b, kind } => {
                let a_value = self.get_ssa(a);
                let b_value = self.get_ssa(b);
                let result_temp = self.next_reg();

                match kind {
                    BinaryOp::Add => {
                        self.emitter
                            .simple_op(AsmOp::ADD, result_temp, a_value, b_value);
                    }
                    _ => todo!(),
                };

                self.drop_reg(a_value);
                self.drop_reg(b_value);
                self.set_ssa(dest, result_temp);
            }
            Op::Jump { .. } => {
                todo!()
            }
            Op::AlwaysJump(target_block) => {
                self.emitter.jump_to(*target_block);
            }
            Op::Phi { .. } => {
                todo!()
            }
            Op::Return(value) => {
                if let Some(value) = value {
                    let return_value = self.get_ssa(value);
                    self.emitter
                        .pair(AsmOp::MOV, Register(RegKind::Int64, 0), return_value);
                    self.drop_reg(return_value);
                }
                self.emitter
                    .simple_with_const(AsmOp::ADD, SP, SP, self.total_stack_size);
                self.emitter.single(AsmOp::RET);
            }
            Op::StackAlloc { dest, ty, count } => {
                assert_eq!(*count, 1);
                let bytes = self.ir.unwrap().size_of(ty);
                self.stack_remaining -= bytes as isize;
                let dest_ptr = self.next_reg();
                self.emitter.simple_with_const(
                    AsmOp::ADD,
                    dest_ptr,
                    SP,
                    self.stack_remaining as usize,
                );
                self.set_ssa(dest, dest_ptr);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let address = self.get_ssa(addr);
                let dest_temp = self.next_reg();
                self.emitter.load(dest_temp, address, 0);
                self.set_ssa(value_dest, dest_temp);
                self.drop_reg(address);
            }
            Op::StoreToPtr { addr, value_source } => {
                let address = self.get_ssa(addr);
                let value = self.get_ssa(value_source);
                self.emitter.store(value, address, 0);
                self.drop_reg(address);
                self.drop_reg(value);
            }
            Op::Call { .. } => {
                todo!()
            }
            Op::GetFieldAddr { .. } => {
                todo!()
            }
            Op::Cast { .. } => {
                todo!()
            }
        }
    }

    // Loads the value of an ssa from the stack into a register.
    // You need to return this to the queue.
    #[must_use]
    fn get_ssa(&mut self, ssa: &Ssa) -> Register {
        let reg = self.next_reg();
        self.emitter.load(reg, SP, self.offset_of(ssa));
        reg
    }

    // Stores a value from a register into the stack slot of an ssa.
    fn set_ssa(&mut self, ssa: &Ssa, value: Register) {
        self.emitter.store(value, SP, self.offset_of(ssa));
        self.drop_reg(value);
    }

    // You need to return this to the queue.
    fn next_reg(&mut self) -> Register {
        let reg = self.unused_registers.pop().expect("Need more registers.");
        self.active_registers.push(reg);
        reg
    }

    fn drop_reg(&mut self, register: Register) {
        let index = self
            .active_registers
            .iter()
            .position(|r| *r == register)
            .unwrap();
        self.active_registers.swap_remove(index);
        self.unused_registers.push(register);
    }

    fn offset_of(&self, ssa: &Ssa) -> usize {
        self.func.unwrap().required_stack_bytes + (ssa.index() * 8)
    }
}
