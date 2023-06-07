use crate::ast::{BinaryOp, CType, FuncSignature, LiteralValue, ValueType};
use crate::ir::liveness::{compute_liveness, SsaLiveness};
use crate::ir::{CastType, Function, Label, Module, Op, Ssa};
use crate::log;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Formatter, Write};

struct Aarch64Builder<'ir> {
    ir: &'ir Module,
    func: &'ir Function,
    stack_remaining: isize,
    total_stack_size: usize,
    // TODO: this will be useful again when i have more sophisticated spilling so calculating them is non-trivial. should be a Vec<Option<usize>> tho
    ssa_offsets: HashMap<Ssa, usize>,
    active_registers: Vec<Reg>,
    unused_registers: VecDeque<Reg>,
    current: Label,
    text: Vec<Option<[String; 3]>>,
    current_index: usize,
    ssa_registers: Vec<Option<Reg>>,
    cursor: CursorPos,
    // for asserts
    on_last: bool, // TODO: instead of ssa_registers + ssa_offsets have an enum SsaLocation { Register(x), Stack(x), Uninit }
    liveness: SsaLiveness<'ir>,
}

// These break a block's code into three chunks you can append to separately so phi moves can go after all code but before the jump away.
#[derive(Default)]
enum CursorPos {
    #[default]
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
    let mut text = String::new();
    for function in &ir.functions {
        let builder = Aarch64Builder::new(ir, function);
        text += &builder.run();
    }
    text
}

impl<'ir> Aarch64Builder<'ir> {
    fn new(ir: &'ir Module, function: &'ir Function) -> Aarch64Builder<'ir> {
        Aarch64Builder {
            ir,
            func: function,
            stack_remaining: 0,
            total_stack_size: 0,
            ssa_offsets: Default::default(),
            active_registers: vec![],
            unused_registers: Default::default(),
            current: Default::default(),
            text: vec![],
            current_index: 0,
            ssa_registers: vec![],
            cursor: Default::default(),
            on_last: false,
            liveness: compute_liveness(function),
        }
    }

    fn run(mut self) -> String {
        self.text.push(Some(Default::default()));
        for code in &self.func.blocks {
            match code {
                None => self.text.push(None),
                Some(_) => self.text.push(Some(Default::default())),
            }
        }
        output!(self, "_{}_{}:", self.ir.name, self.func.signature.name);

        self.init_args_and_stack(self.func);

        self.on_last = true;
        self.jump_to(self.func.entry_point());
        self.on_last = false;

        self.emit_func_code();

        assert!(self.stack_remaining >= 0);
        self.get_text()
    }

    fn init_args_and_stack(&mut self, function: &Function) {
        // Order matters because function params start at X0 and next_reg pops from the end
        let scratch_register_count = 16;
        let float_register_count = 8;
        for i in 0..scratch_register_count {
            let reg = Reg(RegKind::Int, Bits::B64, i);
            self.unused_registers.push_back(reg);
        }

        for i in 0..float_register_count {
            let reg = Reg(RegKind::Float, Bits::B64, i);
            self.unused_registers.push_back(reg);
        }

        // TODO: account for floats
        let has_enough_registers = function.register_types.len() <= self.unused_registers.len();

        // Reserve stack space (stack grows downwards).
        // TODO: option to fill it in with garbage numbers for debugging?
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
                let r = self.next_reg(ty);
                self.ssa_registers[arg_ssa.index()] = Some(r);
            }

            // TODO: X8 is special if we're returning a struct
            for i in arg_count..reg_count {
                let ty = function.register_types.get(&Ssa(i)).unwrap();
                let r = self.next_reg(ty);
                self.ssa_registers[i] = Some(r);
            }

            if FILL_REGISTERS_WITH_GARBAGE {
                // TODO: do this in an evil() function so I can call it randomly to test my saving registers.
                //       do the float registers as well. and set the flags to something random.
                // Skip the registers used to pass arguments.
                for i in (arg_count as u8)..scratch_register_count {
                    let reg = Reg(RegKind::Int, Bits::B64, i);
                    output!(self, "{:?} {:?}, #{}", AsmOp::MOVZ, reg, 12345);
                }
            }

            assert_eq!(self.ssa_registers[0].unwrap().2, 0);
        } else {
            todo!();
            self.save_arguments_to_stack(&function.signature);
        }
    }

    fn emit_func_code(&mut self) {
        let blocks = self.func.blocks.iter().enumerate();
        for (i, code) in blocks {
            if let Some(code) = code {
                self.current = Label(i);
                self.move_cursor(self.current, CursorPos::CodeEnd);
                output!(self, "{}:", self.current.index());
                for (i, op) in code.iter().enumerate() {
                    if i == (code.len() - 1) {
                        assert!(op.is_jump(), "last op of basic block must be jump.");
                        self.move_cursor(self.current, CursorPos::JmpEnd);
                        self.on_last = true;
                    }
                    self.emit_op(op);
                }
                self.on_last = false;
            }
        }
    }

    fn save_arguments_to_stack(&mut self, signature: &'ir FuncSignature) {
        assert!(!signature.has_var_args);
        let count = signature.param_types.len();
        if count == 0 {
            return;
        }

        let ty = signature.param_types.get(0).unwrap();
        assert_eq!(count, 1);
        let first_arg = self.next_reg(ty);
        output!(
            self,
            "{:?} {:?}, {:?}",
            AsmOp::MOV,
            first_arg,
            Reg(RegKind::Int, Bits::B64, 0)
        );
        self.set_ssa(&Ssa(0), first_arg);
    }

    fn emit_op(&mut self, op: &Op) {
        match op {
            Op::ConstValue { dest, value, kind } => {
                match value {
                    LiteralValue::IntNumber(n) => {
                        // TODO assert value in range. For larger constants we could use several MOVK with shift.
                        let result = self.reg_for(dest);
                        // (MOVZ X, #n;) == (MOV X, XZR; MOVK X, #n;) == (SUB X, X, X; ADD X, X, X, #n;)
                        output!(self, "{:?} {:?}, #{}", AsmOp::MOVZ, result, *n);
                        self.set_ssa(dest, result);
                    }
                    LiteralValue::FloatNumber(n) => {
                        // TODO assert value in range.
                        let result = self.reg_for(dest);
                        output!(self, "{:?} {:?}, #{}", AsmOp::FMOV, result, *n);
                        self.set_ssa(dest, result);
                    }
                    _ => todo!(),
                }
            }
            Op::Binary { dest, a, b, kind } => {
                let a_value = self.get_ssa(a);
                let b_value = self.get_ssa(b);
                let result_temp = self.reg_for(dest);

                let is_int = a_value.0 == RegKind::Int && b_value.0 == RegKind::Int;
                let is_float = a_value.0 == RegKind::Float && b_value.0 == RegKind::Float;
                assert!(is_int || is_float);

                match kind {
                    // Signed/Unsigned Add/Sub are the same because two's complement
                    BinaryOp::Add => {
                        self.simple_op(AsmOp::ADD, result_temp, a_value, b_value);
                    }
                    BinaryOp::Subtract => {
                        self.simple_op(AsmOp::SUB, result_temp, a_value, b_value);
                    }
                    BinaryOp::Multiply => {
                        self.simple_op(AsmOp::MUL, result_temp, a_value, b_value);
                    }
                    // TODO: manual trap for int divide by zero.
                    BinaryOp::Divide => {
                        // SDIV
                        self.simple_op(AsmOp::UDIV, result_temp, a_value, b_value);
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
                    self.pair(AsmOp::MOV, Reg(RegKind::Int, Bits::B64, 0), return_value);
                    self.drop_reg(return_value);
                }
                self.simple_with_const(AsmOp::ADD, SP, SP, self.total_stack_size);
                output!(self, "{:?}", AsmOp::RET);
            }
            Op::StackAlloc { dest, ty, count } => {
                assert_eq!(*count, 1);
                let bytes = self.ir.size_of(ty);
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
                let in_ty = self.func.register_types.get(input).unwrap();
                let out_ty = self.func.register_types.get(output).unwrap();
                match kind {
                    CastType::UnsignedIntUp
                    | CastType::IntDown
                    | CastType::FloatUp
                    | CastType::FloatDown
                    | CastType::FloatToUInt
                    | CastType::UIntToFloat => {
                        //
                        todo!()
                    }
                    CastType::IntToPtr | CastType::PtrToInt | CastType::Bits => {
                        // TODO: make sure bits of float->int or int->float needs to swaps register types properly
                        assert_eq!(register_kind(in_ty), register_kind(out_ty));
                        let temp = self.get_ssa(input);
                        self.set_ssa(output, temp);
                    }
                }
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
    fn get_ssa(&mut self, ssa: &Ssa) -> Reg {
        let ty = self.func.register_types.get(ssa).unwrap();
        match self.ssa_registers[ssa.index()] {
            None => {
                // We don't have the value in a register yet.
                let reg = self.next_reg(ty);
                self.load(reg, SP, self.offset_of(ssa));
                // TODO: bring this back when i do proper spilling
                // self.ssa_registers[ssa.index()] = Some(reg);
                reg
            }
            Some(active_reg) => {
                assert_eq!(register_kind(ty), (active_reg.0, active_reg.1));
                active_reg
            }
        }
    }

    // Stores a value from a register into the stack slot of an ssa.
    // The caller may not use this register again (they must get a new one from the queue because we might have chosen to reuse this one).
    fn set_ssa(&mut self, ssa: &Ssa, value: Reg) {
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
    fn reg_for(&mut self, ssa: &Ssa) -> Reg {
        let ty = self.func.register_types.get(ssa).unwrap();
        match self.ssa_registers[ssa.index()] {
            None => self.next_reg(ty),
            Some(active_reg) => {
                // We've already allocated a register for this SSA, so let's give you that
                // so we don't have to move the value in set_ssa.
                assert_eq!(register_kind(ty), (active_reg.0, active_reg.1));
                active_reg
            }
        }
    }

    // You need to return this to the queue.
    #[must_use]
    fn next_reg(&mut self, ty: &CType) -> Reg {
        let (kind, bits) = register_kind(ty);

        let index = self
            .unused_registers
            .iter()
            .position(|s| s.0 == kind)
            .expect("Need more registers.");

        // TODO: order matters for arguments so can't blindly swap_remove
        let mut reg = self.unused_registers.remove(index).unwrap();
        reg.1 = bits;
        self.active_registers.push(reg);
        reg
    }

    // TODO: maybe make Register not copy so i can enforce passing it to the allocator. drop impl that panics if not returned to queue properly.
    fn drop_reg(&mut self, register: Reg) {
        if self
            .ssa_registers
            .iter()
            .filter(|s| s.is_some())
            .map(|s| s.unwrap())
            .any(|s| s == register)
        {
            // This register is allocated for an ssa so we'll just leave it there so we can read it later
            // TODO: some other hook for signalling that we're never doing to need this value again so we can release the register
            //       things that dont have enough space for all registers dont work right now
            return;
        }

        let index = self
            .active_registers
            .iter()
            .position(|r| *r == register)
            .unwrap();
        // TODO: order matters for arguments so can't blindly swap_remove
        self.active_registers.remove(index);
        self.unused_registers.push_back(register);
    }

    fn offset_of(&self, ssa: &Ssa) -> usize {
        self.func.required_stack_bytes + (ssa.index() * 8)
    }

    fn move_cursor(&mut self, block: Label, pos: CursorPos) {
        self.current = block;
        self.current_index = block.index() + 1;
        self.cursor = pos;
        assert!(self.text[self.current_index].is_some());
    }

    fn simple_op(&mut self, op: AsmOp, destination: Reg, arg1: Reg, arg2: Reg) {
        output!(self, "{:?} {:?}, {:?}, {:?}", op, destination, arg1, arg2);
    }

    fn jump_to(&mut self, block: Label) {
        // If we're jumping to the next block, just fall through since we know this is the last instruction in the block.
        // (current_index == current.index + 1) because there's an extra header block to setup the stack.
        assert!(self.on_last);
        if block.index() != self.current_index {
            let b = self.get_label(block);
            output!(self, "B {}", b);
        }
    }

    fn pair(&mut self, op: AsmOp, destination: Reg, arg1: Reg) {
        output!(self, "{:?} {:?}, {:?}", op, destination, arg1);
    }

    fn simple_with_const(&mut self, op: AsmOp, destination: Reg, arg1: Reg, arg2_constant: usize) {
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

    fn load(&mut self, destination: Reg, addr: Reg, offset: usize) {
        output!(self, "LDR {:?}, [{:?}, #{}]", destination, addr, offset);
    }

    fn store(&mut self, value: Reg, addr: Reg, offset: usize) {
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
    fn binary_compare(&mut self, a_value: Reg, b_value: Reg, result_temp: Reg, false_flags: AsmOp) {
        let cmp = if a_value.0 == RegKind::Int {
            AsmOp::CMP
        } else {
            AsmOp::FCMP
        };

        // Set the magic flags in the sky based on the relationship between these numbers.
        self.pair(cmp, a_value, b_value);

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
    MUL,
    UDIV,
    FCMP,
    FMOV,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Bits {
    B32,
    B64,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum RegKind {
    Int,
    Float,
    IntStackPointer,
    IntZero,
}

#[derive(Copy, Clone)]
struct Reg(RegKind, Bits, u8);

const SP: Reg = Reg(RegKind::IntStackPointer, Bits::B64, 31);
const ZERO: Reg = Reg(RegKind::IntZero, Bits::B64, 31);

impl PartialEq<Self> for Reg {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.2 == other.2
    }
}

fn register_kind(ty: &CType) -> (RegKind, Bits) {
    if ty.is_ptr() {
        return (RegKind::Int, Bits::B64);
    } else {
        match ty.ty {
            ValueType::U64 => (RegKind::Int, Bits::B64),
            ValueType::U32 => (RegKind::Int, Bits::B32),
            ValueType::U8 => todo!(),
            ValueType::F64 => (RegKind::Float, Bits::B64),
            ValueType::F32 => (RegKind::Float, Bits::B32),
            ValueType::Struct(_) | ValueType::Void => unreachable!(),
        }
    }
}

impl Debug for Reg {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Reg(RegKind::Int, bits, i) => {
                let prefix = match bits {
                    Bits::B32 => "W",
                    Bits::B64 => "X",
                };
                write!(f, "{}{}", prefix, i)
            }
            Reg(RegKind::Float, bits, i) => {
                let prefix = match bits {
                    Bits::B32 => "S",
                    Bits::B64 => "D",
                };
                write!(f, "{}{}", prefix, i)
            }
            Reg(RegKind::IntStackPointer, _, _) => {
                write!(f, "SP")
            }
            Reg(RegKind::IntZero, _, _) => {
                write!(f, "XZR")
            }
        }
    }
}
