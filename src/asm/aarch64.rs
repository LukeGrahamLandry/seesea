use crate::ast::{BinaryOp, FuncSignature, LiteralValue, ValueType};
use crate::ir::{CastType, Function, Label, Module, Op, Ssa};
use crate::log;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Formatter, Write};

struct Aarch64Builder<'ir> {
    ir: Option<&'ir Module>,
    func: Option<&'ir Function>,
    stack_remaining: isize,
    total_stack_size: usize,
    // TODO: this will be useful again when i have more sophisticated spilling so calculating them is non-trivial. should be a Vec<Option<usize>> tho
    ssa_offsets: HashMap<Ssa, usize>,
    active_registers: Vec<Register>,
    unused_registers: Vec<Register>,
    current: Label,
    text: Vec<Option<[String; 3]>>,
    current_index: usize,
    ssa_registers: Vec<Option<Register>>,
    cursor: CursorPos,
    // TODO: instead of ssa_registers + ssa_offsets have an enum SsaLocation { Register(x), Stack(x), Uninit }
}

// These break a block's code into three chunks you can append to separately so phi moves can go after all code but before the jump away.
enum CursorPos {
    CodeEnd,
    PhiTail,
    JmpEnd,
}

// TODO: liveness pass so i can know when the last read of each ssa is.
//       Vec(Ssa -> OpIndex) and then whenever i run out of registers i can go through ssa_registers + ssa_offsets and clear out any that are done
//       need to think about how that interacts with loops. you dont count as done until you get past the jump that might go back to the top.
//       to test this without more complicated code i could artificially limit the number of allowed to like args+3.

macro_rules! output {
    ($self:ident, $($arg:tt)*) => {{
        let i = match $self.cursor {
            CursorPos::CodeEnd => 0,
            CursorPos::PhiTail => 1,
            CursorPos::JmpEnd => 2,
        };
        writeln!(&mut $self.text[$self.current_index].as_mut().unwrap()[i], $($arg)*).unwrap();
    }};
}

// Should we start functions by filling any corruptible with meaningless sentinel values to help debugging?
const FILL_REGISTERS_WITH_GARBAGE: bool = false;

pub fn build_asm(ir: &Module) -> String {
    let mut builder = Aarch64Builder {
        ir: None,
        func: None,
        stack_remaining: 0,
        total_stack_size: 0,
        ssa_offsets: Default::default(),
        active_registers: Default::default(),
        unused_registers: Default::default(),
        current: Label(0),
        text: vec![],
        current_index: 0,
        ssa_registers: vec![],
        cursor: CursorPos::CodeEnd,
    };
    builder.run(ir);
    builder.get_text()
}

const SP: Register = Register(RegKind::Int64, 31);

impl<'ir> Aarch64Builder<'ir> {
    fn run(&mut self, ir: &'ir Module) {
        self.ir = Some(ir);
        for function in &ir.functions {
            self.emit_function(function);
        }
    }

    fn emit_function(&mut self, function: &'ir Function) {
        self.text.push(Some(Default::default()));
        for code in &function.blocks {
            match code {
                None => self.text.push(None),
                Some(_) => self.text.push(Some(Default::default())),
            }
        }
        output!(
            self,
            "_{}_{}:",
            self.ir.unwrap().name,
            function.signature.name
        );

        self.unused_registers = vec![];
        // Order matters because function params start at X0 and next_reg pops from the end
        let scratch_register_count = 16;
        for i in (0..scratch_register_count).rev() {
            let reg = Register(RegKind::Int64, i);
            self.unused_registers.push(reg);
        }

        let has_enough_registers = function.register_types.len() <= self.unused_registers.len();

        // Reserve stack space (stack grows downwards).
        // TODO: option to fill it in with garbage numbers for debugging?
        self.func = Some(function);
        self.total_stack_size = function.required_stack_bytes;
        if !has_enough_registers {
            self.total_stack_size += function.register_types.len() * 8;
        }

        self.stack_remaining = function.required_stack_bytes as isize;

        let extra = self.total_stack_size - ((self.total_stack_size / 16) * 16);
        self.total_stack_size += extra;
        assert_eq!(
            self.total_stack_size % 16,
            0,
            "aarch64 requires the stack pointer to be 16 byte aligned."
        );

        output!(
            self,
            "{:?} {:?}, {:?}, #{}",
            AsmOp::SUB,
            SP,
            SP,
            self.total_stack_size
        );

        self.ssa_registers = vec![None; function.register_types.len()];
        if has_enough_registers {
            // We have enough corruptible registers for all our SSAs.
            // But when we call someone, they're allowed to write over them all so remember to save them.

            // First 8 arguments are passed in X0-X7
            let arg_count = function.arg_registers.len();
            let reg_count = function.register_types.len();
            assert!(arg_count < 8, "todo");
            for (i, arg_ssa) in function.arg_registers.iter().enumerate() {
                let ty = function.register_types.get(arg_ssa).unwrap();
                assert!(ty.is_raw_int() || ty.is_ptr());
                assert_eq!(i, arg_ssa.0);
                let r = self.next_reg();
                self.ssa_registers[arg_ssa.index()] = Some(r);
            }

            // TODO: X8 is special if we're returning a struct
            for (_, ty) in &function.register_types {
                assert!(ty.is_raw_int() || ty.is_ptr());
            }

            for i in arg_count..reg_count {
                let r = self.next_reg();
                self.ssa_registers[i] = Some(r);
            }

            if FILL_REGISTERS_WITH_GARBAGE {
                // Skip the registers used to pass arguments.
                for i in (arg_count as u8)..scratch_register_count {
                    let reg = Register(RegKind::Int64, i);
                    output!(self, "{:?} {:?}, #{}", AsmOp::MOVZ, reg, 12345);
                }
            }
        } else {
            self.save_arguments_to_stack(&function.signature);
        }

        self.jump_to(function.entry_point());
        for (i, code) in function.blocks.iter().enumerate() {
            if let Some(code) = code {
                self.current = Label(i);
                self.move_cursor(self.current, CursorPos::CodeEnd);
                output!(self, "{}:", self.current.index());
                for (i, op) in code.iter().enumerate() {
                    if i == (code.len() - 1) {
                        assert!(op.is_jump(), "last op of basic block must be jump.");
                        self.move_cursor(self.current, CursorPos::JmpEnd);
                    }
                    self.emit_op(op);
                }
            }
        }

        assert!(self.stack_remaining >= 0);
        if function.register_types.len() > scratch_register_count as usize {
            assert!(self.active_registers.is_empty());
        }
    }

    fn save_arguments_to_stack(&mut self, signature: &'ir FuncSignature) {
        assert!(!signature.has_var_args);
        let count = signature.param_types.len();
        if count == 0 {
            return;
        }

        assert_eq!(count, 1);
        let first_arg = self.next_reg();
        output!(
            self,
            "{:?} {:?}, {:?}",
            AsmOp::MOV,
            first_arg,
            Register(RegKind::Int64, 0)
        );
        self.set_ssa(&Ssa(0), first_arg);
    }

    fn emit_op(&mut self, op: &Op) {
        match op {
            Op::ConstValue { dest, value, kind } => {
                assert!(kind.is_raw_int());
                match value {
                    LiteralValue::IntNumber(n) => {
                        // TODO assert value in range. For larger constants we could use several MOVK with shift.
                        let result = self.reg_for(dest);
                        // (MOVZ X, #n;) == (MOV X, XZR; MOVK X, #n;) == (SUB X, X, X; ADD X, X, X, #n;)
                        output!(self, "{:?} {:?}, #{}", AsmOp::MOVZ, result, *n);
                        self.set_ssa(dest, result);
                    }
                    _ => todo!(),
                }
            }
            Op::Binary { dest, a, b, kind } => {
                let a_value = self.get_ssa(a);
                let b_value = self.get_ssa(b);
                let result_temp = self.reg_for(dest);

                match kind {
                    BinaryOp::Add => {
                        self.simple_op(AsmOp::ADD, result_temp, a_value, b_value);
                    }
                    BinaryOp::Subtract => {
                        self.simple_op(AsmOp::SUB, result_temp, a_value, b_value);
                    }
                    // TODO: different flags for signed comparisons
                    BinaryOp::GreaterThan => {
                        self.binary_compare(a_value, b_value, result_temp, AsmOp::BLS);
                    }
                    BinaryOp::LessThan => {
                        self.binary_compare(a_value, b_value, result_temp, AsmOp::BHS);
                    }
                    BinaryOp::GreaterOrEqual => {
                        self.binary_compare(a_value, b_value, result_temp, AsmOp::BLO);
                    }
                    BinaryOp::LessOrEqual => {
                        self.binary_compare(a_value, b_value, result_temp, AsmOp::BHI);
                    }
                    _ => todo!(),
                };

                self.drop_reg(a_value);
                self.drop_reg(b_value);
                self.set_ssa(dest, result_temp);
            }
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => {
                let cond_temp = self.get_ssa(condition);
                // if <condition == zero>, branch to <else block>
                let b = self.get_label(*if_false);
                output!(self, "{:?} {:?}, {}", AsmOp::CBZ, cond_temp, b);
                // otherwise fall through and branch to <then block>
                self.jump_to(*if_true);
                self.drop_reg(cond_temp);
            }
            Op::AlwaysJump(target_block) => {
                self.jump_to(*target_block);
            }
            Op::Phi { dest, a, b } => {
                self.emit_phi(dest, a.0, a.1);
                self.emit_phi(dest, b.0, b.1);
            }
            Op::Return(value) => {
                if let Some(value) = value {
                    let return_value = self.get_ssa(value);
                    // This clobbers self.ssa_registers[0] but we're immediately returning so it's fine.
                    self.pair(AsmOp::MOV, Register(RegKind::Int64, 0), return_value);
                    self.drop_reg(return_value);
                }
                self.simple_with_const(AsmOp::ADD, SP, SP, self.total_stack_size);
                output!(self, "{:?}", AsmOp::RET);
            }
            Op::StackAlloc { dest, ty, count } => {
                assert_eq!(*count, 1);
                let bytes = self.ir.unwrap().size_of(ty);
                self.stack_remaining -= bytes as isize;
                let dest_ptr = self.reg_for(dest);
                self.simple_with_const(AsmOp::ADD, dest_ptr, SP, self.stack_remaining as usize);
                self.set_ssa(dest, dest_ptr);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let address = self.get_ssa(addr);
                let dest_temp = self.reg_for(value_dest);
                self.load(dest_temp, address, 0);
                self.set_ssa(value_dest, dest_temp);
                self.drop_reg(address);
            }
            Op::StoreToPtr { addr, value_source } => {
                let address = self.get_ssa(addr);
                let value = self.get_ssa(value_source);
                self.store(value, address, 0);
                self.drop_reg(address);
                self.drop_reg(value);
            }
            Op::Call { .. } => {
                todo!()
            }
            Op::GetFieldAddr { .. } => {
                todo!()
            }
            Op::Cast {
                input,
                output,
                kind,
            } => {
                assert_eq!(*kind, CastType::Bits);
                let temp = self.get_ssa(input);
                self.set_ssa(output, temp);
            }
        }
    }

    fn emit_phi(&mut self, dest: &Ssa, prev_block: Label, prev_value: Ssa) {
        let current = self.current;
        self.move_cursor(prev_block, CursorPos::PhiTail);
        let value = self.get_ssa(&prev_value);
        self.set_ssa(dest, value);
        self.move_cursor(current, CursorPos::CodeEnd);
    }

    // Loads the value of an ssa from the stack into a register.
    // You need to return this to the queue.
    #[must_use]
    fn get_ssa(&mut self, ssa: &Ssa) -> Register {
        match self.ssa_registers[ssa.index()] {
            None => {
                // We don't have the value in a register yet.
                let reg = self.next_reg();
                self.load(reg, SP, self.offset_of(ssa));
                self.ssa_registers[ssa.index()] = Some(reg);
                reg
            }
            Some(active_reg) => active_reg,
        }
    }

    // Stores a value from a register into the stack slot of an ssa.
    // The caller may not use this register again (they must get a new one from the queue because we might have chosen to reuse this one).
    fn set_ssa(&mut self, ssa: &Ssa, value: Register) {
        match self.ssa_registers[ssa.index()] {
            None => {
                // We haven't assigned a register to represent this SSA yet.
                self.store(value, SP, self.offset_of(ssa));
                self.drop_reg(value);
            }
            Some(active_reg) => {
                if value == active_reg {
                    // NO-OP, the value is already in the right place.
                } else {
                    // For example, phi nodes will always hit this because they're the only ones that are reusing an existing value.
                    // We can't just steal the register from it because could be coming from either branch at runtime.
                    output!(self, "{:?} {:?}, {:?}", AsmOp::MOV, active_reg, value);
                    // We know this call would be a no-op since we already have the right register.
                    // self.set_ssa(ssa, active_reg);
                }
            }
        }
    }

    // Get an unused register with an undefined value but hint that we want to store the new value of <ssa> in it.
    // If you want to read the value of an ssa, you must call get_ssa instead.
    // You need to return this to the queue.
    #[must_use]
    fn reg_for(&mut self, ssa: &Ssa) -> Register {
        match self.ssa_registers[ssa.index()] {
            None => self.next_reg(),
            Some(active_reg) => {
                // We've already allocated a register for this SSA, so let's give you that
                // so we don't have to move the value in set_ssa.
                active_reg
            }
        }
    }

    // You need to return this to the queue.
    #[must_use]
    fn next_reg(&mut self) -> Register {
        let reg = self.unused_registers.pop().expect("Need more registers.");
        self.active_registers.push(reg);
        reg
    }

    // TODO: maybe make Register not copy so i can enforce passing it to the allocator. drop impl that panics if not returned to queue properly.
    fn drop_reg(&mut self, register: Register) {
        if self
            .ssa_registers
            .iter()
            .any(|s| matches!(s, Some(register)))
        {
            // This register is allocated for an ssa so we'll just leave it there so we can read it later
            // TODO: some other hook for signalling that we're never doing to need this value again so we can release the register
            return;
        }

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

    fn move_cursor(&mut self, block: Label, pos: CursorPos) {
        self.current = block;
        self.current_index = block.index() + 1;
        self.cursor = pos;
        assert!(self.text[self.current_index].is_some());
    }

    fn simple_op(&mut self, op: AsmOp, destination: Register, arg1: Register, arg2: Register) {
        output!(self, "{:?} {:?}, {:?}, {:?}", op, destination, arg1, arg2);
    }

    fn jump_to(&mut self, block: Label) {
        let b = self.get_label(block);
        output!(self, "B {}", b);
    }

    fn pair(&mut self, op: AsmOp, destination: Register, arg1: Register) {
        output!(self, "{:?} {:?}, {:?}", op, destination, arg1);
    }

    fn simple_with_const(
        &mut self,
        op: AsmOp,
        destination: Register,
        arg1: Register,
        arg2_constant: usize,
    ) {
        // assert arg2_constant in the right range
        output!(
            self,
            "{:?} {:?}, {:?}, #{}",
            op,
            destination,
            arg1,
            arg2_constant
        );
    }

    fn load(&mut self, destination: Register, addr: Register, offset: usize) {
        output!(self, "LDR {:?}, [{:?}, #{}]", destination, addr, offset);
    }

    fn store(&mut self, value: Register, addr: Register, offset: usize) {
        output!(self, "STR {:?}, [{:?}, #{}]", value, addr, offset);
    }

    fn get_label(&self, block: Label) -> String {
        if self.current_index < (block.index() + 1) {
            format!("{}f", block.index())
        } else {
            format!("{}b", block.index())
        }
    }

    pub fn get_text(self) -> String {
        let mut result = String::new();
        self.text
            .into_iter()
            .filter(|s| s.is_some())
            .map(|s| s.unwrap())
            .for_each(|s| {
                result.push_str(&*s.concat());
            });
        log!("==== Direct Aarch64 =====");
        log!("{}", result);
        log!("============");
        result
    }

    // false_flags is the inverse of the condition this evaluates
    fn binary_compare(
        &mut self,
        a_value: Register,
        b_value: Register,
        result_temp: Register,
        false_flags: AsmOp,
    ) {
        // Set the magic flags in the sky based on the relationship between these numbers.
        self.pair(AsmOp::CMP, a_value, b_value);

        // Set the destination to zero.
        output!(self, "{:?} {:?}, XZR", AsmOp::MOV, result_temp);

        // Skip one instruction if the condition we care about was false
        output!(self, "{:?} #{}", false_flags, 8);

        // Add one to the result.
        self.simple_with_const(AsmOp::ADD, result_temp, result_temp, 1);
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AsmOp {
    ADD,
    SUB,
    RET,
    MOV,
    MOVZ,
    CMP,
    BGT,
    CBZ,
    BLS,
    BHS,
    BLO,
    BHI,
}

// The different sizes of each type actually refer to the same register. It just changes how accessing them works.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RegKind {
    Int32,
    Int64,
    Float32,
    Float64,
}

// TODO: this eq is wrong
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct Register(pub RegKind, pub u8);

impl Debug for Register {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.1 == 31 {
            return write!(f, "sp");
        }
        let prefix = match self.0 {
            RegKind::Int32 => "W",
            RegKind::Int64 => "X",
            RegKind::Float32 => {
                todo!()
            }
            RegKind::Float64 => {
                todo!()
            }
        };
        write!(f, "{}{}", prefix, self.1)
    }
}
