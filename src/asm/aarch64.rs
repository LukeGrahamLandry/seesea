use crate::ast::FuncSource;
use crate::ast::{BinaryOp, CType, LiteralValue, ValueType};
use crate::ir::liveness::{compute_liveness, SsaLiveness};
use crate::ir::{CastType, Function, Label, Module, Op, Ssa};
use crate::log;
use crate::util::imap::IndexMap;
use std::collections::VecDeque;
use std::fmt::{Debug, Formatter, Write};

struct Aarch64Builder<'ir> {
    ir: &'ir Module,
    func: &'ir Function,
    stack_remaining: isize,
    total_stack_size: usize,
    // TODO: this will be useful again when i have more sophisticated spilling so calculating them is non-trivial. should be a Vec<Option<usize>> tho
    ssa_offsets: IndexMap<Ssa, usize>,
    active_registers: Vec<Reg>,
    unused_registers: VecDeque<Reg>,
    current: Label,
    text: Vec<Option<[String; 3]>>, // TODO IndexMap<Label ?
    current_index: usize,
    ssa_registers: IndexMap<usize, Reg>, // TODO: key should be Ssa. this used to be a Vec and I'm lazy rn.
    cursor: CursorPos,
    // for asserts
    on_last: bool, // TODO: instead of ssa_registers + ssa_offsets have an enum SsaLocation { Register(x), Stack(x), Uninit }
    liveness: SsaLiveness<'ir>,
    op_index: usize,
    constants: String,
}

// These break a block's code into three chunks you can append to separately so phi moves can go after all code but before the jump away.
#[derive(Default)]
enum CursorPos {
    #[default]
    CodeEnd,
    PhiTail,
    JmpEnd,
}

macro_rules! output {
    ($self:ident, $($arg:tt)*) => {{
        let i = match $self.cursor {
            CursorPos::CodeEnd => 0,
            CursorPos::PhiTail => 1,
            CursorPos::JmpEnd => 2,
        };
        log!($($arg)*);
        writeln!(&mut $self.text[$self.current_index].as_mut().unwrap()[i], $($arg)*).unwrap();
    }};
}

// Should we start functions by filling any corruptible with meaningless sentinel values to help debugging?
const DEBUG_CORRUPT_REGISTERS: bool = false; // TODO: this breaks loops that work by coincidence. need to fix liveness.
const EMIT_DEBUG_IR_COMMENTS: bool = true;
const ZERO_THE_STACK: bool = false; // TODO: option to debug corrupt

// Hardware magic numbers.
const CORRUPTIBLE_INTS: usize = 16;
const CORRUPTIBLE_FLOATS: usize = 8;
const SP_ALIGNMENT: usize = 16;
const CC_REG_ARGS: usize = 8; // how many arguments of each type are passed in registers when calling a function.

// TODO: liveness is the problem.
// it drops things at last usage even if you loop back up.
// need to only drop things at the end of blocks?

// TODO: add `.global _main` if not using rust inline asm as entry point.
pub fn build_asm(ir: &Module) -> String {
    let mut text = String::new();
    for function in &ir.functions {
        let builder = Aarch64Builder::new(ir, function);
        text += &builder.run();
    }
    text
}

// TODO: builder api for instructions: self.op(AsmOp::Add).r(reg_out).r(reg_a).r(reg_b).imm(90).build();
//       then swap it out to create string or direct bytes
impl<'ir> Aarch64Builder<'ir> {
    fn new(ir: &'ir Module, function: &'ir Function) -> Aarch64Builder<'ir> {
        let ssa_count = function.register_types.len();
        Aarch64Builder {
            ir,
            func: function,
            stack_remaining: 0,
            total_stack_size: 0,
            ssa_offsets: IndexMap::with_capacity(ssa_count),
            active_registers: vec![],
            unused_registers: Default::default(),
            current: Default::default(),
            text: vec![],
            current_index: 0,
            ssa_registers: IndexMap::with_capacity(ssa_count),
            cursor: Default::default(),
            on_last: false,
            liveness: compute_liveness(function),
            op_index: 0,
            constants: "".to_string(),
        }
    }

    fn run(mut self) -> String {
        log!("----------");
        self.text.push(Some(Default::default()));
        for code in &self.func.blocks {
            match code {
                None => self.text.push(None),
                Some(_) => self.text.push(Some(Default::default())),
            }
        }
        output!(self, "_{}:", self.func.signature.name);

        self.reserve_stack_space();
        self.init_arg_registers();

        self.on_last = true;
        self.jump_to(self.func.entry_point());
        self.on_last = false;

        self.emit_func_code();

        // Less than zero means we calculated wrong, up to 16 could be padding for SP alignment.
        assert!((0..16).contains(&self.stack_remaining));
        self.get_text()
    }

    fn init_arg_registers(&mut self) {
        self.unused_registers.extend(all_registers());

        // First 8 arguments of each int/float are passed in _0-_7
        let mut ints = 0;
        let mut floats = 0;
        for arg_ssa in self.func.arg_registers.iter() {
            let ty = self.func.register_types.get(arg_ssa).unwrap();
            if ty.is_ptr() || ty.is_raw_int() {
                ints += 1;
            } else if ty.is_raw_float() {
                floats += 1;
            } else {
                unreachable!();
            }
            let r = self.next_reg(ty);
            if self.ssa_offsets.get(arg_ssa).is_some() {
                // The argument was passed in a register but we want to store it on the stack because it gets held across a function call.
                self.set_ssa(arg_ssa, r);
            } else {
                self.ssa_registers.insert(arg_ssa.index(), r);
            }
            log!("[{}] arg {:?} in {:?}", self.op_index, arg_ssa, r);
        }
        assert!(
            ints <= 8 && floats <= 8,
            "We don't support passing arguments on the stack yet."
        );

        // Skip the registers used to pass arguments.
        for reg in self.unused_registers.clone().into_iter() {
            self.corrupt(reg);
        }
    }

    fn reserve_stack_space(&mut self) {
        // TODO: option to fill it in with garbage numbers for debugging?
        // structs and addressed variables.
        self.total_stack_size = self.func.required_stack_bytes;
        // TODO: this ignores live-ness! Anything ever held across a call gets a dedicated stack slot.
        // TODO: work out the spacing similar to struct padding. ie. two u32s don't need 16 bytes.
        //       could make a fake struct for them and just call the function.
        self.total_stack_size += 8 * self
            .liveness
            .held_across_call
            .values()
            .filter(|p| **p)
            .count();
        // TODO: I think im allowing too many ssas to be held in registers. need to leave some free for doing work with the stack, etc.
        if self.liveness.max_ints_alive > CORRUPTIBLE_INTS {
            self.total_stack_size += (self.liveness.max_ints_alive - CORRUPTIBLE_INTS) * 8;
            todo!("need to set ssa_offsets for ssa")
        }
        if self.liveness.max_floats_alive > CORRUPTIBLE_FLOATS {
            self.total_stack_size += (self.liveness.max_floats_alive - CORRUPTIBLE_FLOATS) * 8;
            todo!("need to set ssa_offsets for ssa")
        }

        if self.liveness.has_any_calls {
            // For FP & LR
            self.total_stack_size += 16;
        }

        let extra = self.total_stack_size % SP_ALIGNMENT;
        if extra > 0 {
            self.total_stack_size += SP_ALIGNMENT - extra;
        }

        assert_eq!(
            self.total_stack_size % SP_ALIGNMENT,
            0,
            "aarch64 requires the stack pointer to be {} byte aligned.",
            SP_ALIGNMENT
        );
        self.stack_remaining = self.total_stack_size as isize;

        output!(
            self,
            "{:?} {:?}, {:?}, #{}",
            AsmOp::SUB,
            SP,
            SP,
            self.total_stack_size
        );

        if ZERO_THE_STACK {
            for i in 0..(self.stack_remaining / 8) {
                output!(
                    self,
                    "{:?} {:?}, [{:?}, #{}]",
                    AsmOp::STR,
                    ZERO,
                    SP,
                    i as usize * 8
                );
            }
        }

        // If we ever call a function, we need to save the previous return address on the stack so we have it when we want to return ourselves.
        if self.liveness.has_any_calls {
            self.stack_remaining -= 16;
            output!(
                self,
                "{:?} {:?}, {:?}, [{:?}, #{}]",
                AsmOp::STP,
                FP,
                LR,
                SP,
                self.stack_remaining
            );
            log!("LR/FP at [SP, #{}]", self.stack_remaining);
            self.corrupt(LR);
            self.corrupt(FP);
        }

        // Any SSAs that are held across calls are assigned a slot on the stack so I don't need to deal with loading and storing them.
        for (i, held) in self.liveness.held_across_call.values().enumerate() {
            if !held {
                continue;
            }
            self.stack_remaining -= 8;
            self.ssa_offsets
                .insert(Ssa(i), self.stack_remaining as usize);
            log!("Ssa({}) at [SP, #{}]", i, self.stack_remaining);
        }
    }

    fn emit_func_code(&mut self) {
        let blocks = self.func.blocks.iter().enumerate();
        let mut total = 0;
        for (i, code) in blocks {
            if let Some(code) = code {
                self.current = Label(i);
                self.move_cursor(self.current, CursorPos::CodeEnd);
                output!(self, "{}:", self.current.index());
                for (i, op) in code.iter().enumerate() {
                    self.op_index += 1;
                    if i == (code.len() - 1) {
                        assert!(op.is_jump(), "last op of basic block must be jump.");
                        self.move_cursor(self.current, CursorPos::JmpEnd);
                        self.on_last = true;
                    }
                    if EMIT_DEBUG_IR_COMMENTS {
                        total += 1;
                        output!(self, "// {}. {}", total, self.func.print(op));
                    }
                    self.emit_op(op);
                    self.clean_registers();
                }
                self.on_last = false;
            }
        }

        // Sanity check.
        self.op_index += 1;
        self.clean_registers();
        for (i, reg) in self.ssa_registers.iter() {
            panic!("Ssa({}) = {:?} was allocated at end of function.", i, reg);
        }
        assert!(
            self.active_registers.is_empty(),
            "registers taken at end {:?}",
            self.active_registers
        );
    }

    fn emit_op(&mut self, op: &Op) {
        match op {
            Op::ConstValue { dest, value, .. } => {
                let result = self.reg_for(dest);
                match value {
                    LiteralValue::IntNumber(n) => {
                        self.build_const_u64(result, *n);
                    }
                    LiteralValue::FloatNumber(n) => {
                        // Load the bits as an integer
                        let temp = self.next_reg(&CType::int());
                        self.build_const_u64(temp, n.to_bits());
                        // Then copy it to a float register.
                        output!(self, "{:?} {:?}, {:?}", AsmOp::FMOV, result, temp);
                        self.drop_reg(temp);
                    }
                    LiteralValue::StringBytes(s) => {
                        let name = format!(
                            "str_{}_b{}s{}",
                            self.func.signature.name, self.current.0, dest.0
                        );
                        self.constants +=
                            &format!("{}: .asciz \"{}\"\n", name, s.to_string_lossy());
                        output!(self, "adrp {:?}, {}@PAGE", result, name);
                        output!(self, "add {:?}, {:?}, {}@PAGEOFF", result, result, name);
                    }
                    LiteralValue::UninitStruct | LiteralValue::UninitArray(_, _) => unreachable!(),
                }
                self.set_ssa(dest, result);
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
                        let op = if is_int { AsmOp::ADD } else { AsmOp::FADD };
                        self.simple_op(op, result_temp, a_value, b_value);
                    }
                    BinaryOp::Subtract => {
                        let op = if is_int { AsmOp::SUB } else { AsmOp::FSUB };
                        self.simple_op(op, result_temp, a_value, b_value);
                    }
                    BinaryOp::Multiply => {
                        let op = if is_int { AsmOp::MUL } else { AsmOp::FMUL };
                        self.simple_op(op, result_temp, a_value, b_value);
                    }
                    // TODO: manual trap for int divide by zero.
                    BinaryOp::Divide => {
                        // TODO: SDIV for ints
                        let op = if is_int { AsmOp::UDIV } else { AsmOp::FDIV };
                        self.simple_op(op, result_temp, a_value, b_value);
                    }
                    // TODO: different flags for signed comparisons
                    // Float comparisons set the same flags as normal.
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
                    BinaryOp::Equality => {
                        self.binary_compare(a_value, b_value, result_temp, AsmOp::BNE);
                    }
                    BinaryOp::Modulo => {
                        todo!("https://stackoverflow.com/questions/35351470/obtaining-remainder-using-single-aarch64-instruction")
                    }
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
                    // TODO: I think returning structs by value is done in the caller's stack space.
                    let return_value = self.get_ssa(value);
                    // This clobbers whatever is in _0 but we're immediately returning so it's fine.
                    let reg = get_reg_num(self.func.type_of(value), 0);
                    self.pair(reg.mov_kind(), reg, return_value);
                    self.drop_reg(return_value);
                }

                // If we called a function, make sure to fix the return address so we're going to the right place instead of infinity returning to ourself.
                if self.liveness.has_any_calls {
                    output!(
                        self,
                        "{:?} {:?}, {:?}, [{:?}, #{}]",
                        AsmOp::LDP,
                        FP,
                        LR,
                        SP,
                        self.total_stack_size - 16
                    );
                }

                self.simple_with_const(AsmOp::ADD, SP, SP, self.total_stack_size);
                output!(self, "{:?}", AsmOp::RET);
            }
            Op::StackAlloc { dest, ty, count } => {
                let bytes = self.ir.size_of(ty) * *count;
                self.stack_remaining -= bytes as isize;
                let dest_ptr = self.reg_for(dest);
                self.simple_with_const(AsmOp::ADD, dest_ptr, SP, self.stack_remaining as usize);
                self.set_ssa(dest, dest_ptr);
                // TODO: alignment?
                // assert_eq!(self.stack_remaining as usize % self.ir.size_of(ty), 0);
            }
            Op::LoadFromPtr { value_dest, addr } => {
                let address = self.get_ssa(addr);
                let dest_temp = self.reg_for(value_dest);
                let ty = self.func.type_of(value_dest);
                if ty.is_raw_char() {
                    self.load_byte(dest_temp, address, 0);
                } else {
                    self.load(dest_temp, address, 0);
                }
                self.set_ssa(value_dest, dest_temp);
                self.drop_reg(address);
            }
            Op::StoreToPtr { addr, value_source } => {
                let address = self.get_ssa(addr);
                let value = self.get_ssa(value_source);
                if self.func.type_of(value_source).is_raw_char() {
                    self.store_byte(value, address, 0);
                } else {
                    self.store(value, address, 0);
                }
                self.drop_reg(address);
                self.drop_reg(value);
            }
            Op::Call {
                func_name,
                args,
                return_value_dest,
                kind,
            } => {
                self.do_func_call(func_name, args, return_value_dest, kind);
            }
            Op::GetFieldAddr {
                dest,
                object_addr,
                field_index,
            } => {
                let base_address = self.get_ssa(object_addr);
                let offset = self.calc_field_offset(object_addr, *field_index);
                let field_addr = self.reg_for(dest);
                self.build_const_u64(field_addr, offset);
                output!(
                    self,
                    "{:?} {:?}, {:?}, {:?}",
                    AsmOp::ADD,
                    field_addr,
                    field_addr,
                    base_address
                );
                self.drop_reg(base_address);
                self.set_ssa(dest, field_addr);
            }
            Op::Cast {
                input,
                output,
                kind,
            } => {
                let in_ty = &self.func.register_types[input];
                let out_ty = &self.func.register_types[output];
                let input_reg = self.get_ssa(input);
                let mut output_reg = self.reg_for(output);

                let op = match kind {
                    CastType::FloatToUInt => Some(AsmOp::FCVTAU),
                    CastType::UIntToFloat => Some(AsmOp::UCVTF),
                    CastType::FloatUp | CastType::FloatDown => Some(AsmOp::FCVT),
                    CastType::UnsignedIntUp | CastType::BoolToInt => {
                        // TODO: this relies on chars having their upper bytes zeroed. make sure that's always done somewhere else.
                        // ex. u32 -> u64. it wants the instruction to use the same size view for both operands.
                        // mov-ing with 32 bit registers zeroes the top bits.
                        // TODO: this could be a no-op i think
                        output_reg.1 = input_reg.1;
                        Some(AsmOp::MOV)
                    }
                    CastType::IntToBool
                    | CastType::IntToPtr
                    | CastType::PtrToInt
                    | CastType::Bits => {
                        assert_eq!(self.ir.size_of(in_ty), self.ir.size_of(out_ty));
                        assert_eq!(input_reg.1, output_reg.1);
                        if register_kind(in_ty).0 == register_kind(out_ty).0 {
                            // TODO: make sure this reuses the same register for the new ssa since we know its a NO-OP
                            Some(AsmOp::MOV)
                        } else {
                            // Changing between int and float. TODO: test this.
                            Some(AsmOp::FMOV)
                        }
                    }
                    CastType::IntDown => {
                        // AND off the top bits
                        // ie. down cast (long x) to char is (x AND 255)
                        // TODO: this does redundant work. like loading a byte constant zeros it twice.
                        output_reg.1 = input_reg.1;
                        let bits = self.ir.size_of(out_ty) * 8;
                        let imm: u64 = (1 << bits) - 1;
                        assert_eq!(imm.count_ones(), bits as u32);
                        output!(
                            self,
                            "{:?} {:?}, {:?}, #{}",
                            AsmOp::AND,
                            output_reg,
                            input_reg,
                            imm
                        );
                        self.set_ssa(output, output_reg);
                        self.drop_reg(input_reg);
                        return;
                    }
                };

                if let Some(op) = op {
                    output!(self, "{:?} {:?}, {:?}", op, output_reg, input_reg);
                    self.set_ssa(output, output_reg);
                    self.drop_reg(input_reg);
                    return;
                }

                unreachable!()
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

    fn do_func_call(
        &mut self,
        name: &str,
        args: &[Ssa],
        return_dest: &Option<Ssa>,
        kind: &FuncSource,
    ) {
        // We know any values that need to be held across the call are already on the stack.
        // Any currently active registers are either garbage or an argument to this function.

        // We need to arrange the arguments according to the calling convention.
        let mut ints = 0;
        let mut floats = 0;
        for arg_ssa in args {
            let ty = self.func.register_types.get(arg_ssa).unwrap();
            let current_reg = self.get_ssa(arg_ssa);
            // TODO: this not updating ssa_registers might work by coincidence because their life time always ends immediately after the function call
            if ty.is_ptr() || ty.is_raw_int() {
                let target_reg = get_reg_num(ty, ints);
                if current_reg != target_reg {
                    // TODO: if current_reg isn't an argument, dont bother preserving it and if it is, swap it to the right register for the call instead.
                    self.swap(ty, target_reg, current_reg);
                    self.drop_reg(current_reg);
                }
                ints += 1;
            } else if ty.is_raw_float() {
                let target_reg = get_reg_num(ty, floats);
                if current_reg != target_reg {
                    self.swap(ty, target_reg, current_reg);
                    self.drop_reg(current_reg);
                }
                floats += 1;
            } else {
                unreachable!();
            }
        }

        let is_variadic = self.ir.get_func_signature(name).unwrap().has_var_args;
        assert!(
            ints <= CC_REG_ARGS && floats <= CC_REG_ARGS && !is_variadic,
            "todo: support stack args"
        );

        match kind {
            FuncSource::Internal | FuncSource::External => {
                output!(self, "BL _{}", name);
            }
        }

        if let Some(dest) = return_dest {
            let ty = self.func.register_types.get(dest).unwrap();
            let current_reg = get_reg_num(ty, 0);
            for r in all_registers().filter(|r| *r != current_reg) {
                self.corrupt(r);
            }

            if !self.active_registers.contains(&current_reg) {
                // TODO: hack
                self.take(current_reg);
            }
            self.set_ssa(dest, current_reg);
        }
    }

    fn take(&mut self, reg: Reg) {
        assert!(!self.active_registers.contains(&reg));
        self.active_registers.push(reg);
        self.unused_registers.retain(|r| *r != reg);
    }

    fn swap(&mut self, ty: &CType, a: Reg, b: Reg) {
        assert_eq!(a.0, b.0);
        let scratch = self.next_reg(ty);
        let op = a.mov_kind();
        output!(self, "{:?} {:?}, {:?}", op, scratch, a);
        output!(self, "{:?} {:?}, {:?}", op, a, b);
        output!(self, "{:?} {:?}, {:?}", op, b, scratch);
        self.drop_reg(scratch);
        println!("{:?}", self.ssa_registers);
    }

    // TODO: only call this as needed
    fn clean_registers(&mut self) {
        // TODO: cant use iter() cause rust is stressed out. need a mut iter that shows you the options.
        // Note this isn't using self.ssa_registers.len() because that might not be filled out all the way yet.
        for i in 0..self.func.register_types.len() {
            let reg = self.ssa_registers.get(&i);
            if let Some(&reg) = reg {
                assert!(!self.unused_registers.contains(&reg));
                assert!(self.active_registers.contains(&reg));
                if !self.liveness.range[Ssa(i)].contains(&self.op_index) {
                    log!("[{}] free Ssa({}) in {:?}", self.op_index, i, reg);
                    // The ssa is dead so we can return the register.
                    self.active_registers.retain(|r| *r != reg);
                    self.unused_registers.push_back(reg);
                    self.ssa_registers.remove(&i);
                    self.corrupt(reg);
                }
            }
        }
    }

    // Loads the value of an ssa from the stack into a register.
    // You need to return this to the queue.
    #[must_use]
    fn get_ssa(&mut self, ssa: &Ssa) -> Reg {
        self.assert_live(ssa);
        let ty = self.func.register_types.get(ssa).unwrap();
        if let Some(stack_offset) = self.ssa_offsets.get(ssa).cloned() {
            // The value lives on the stack, so load it.
            let reg = self.next_reg(ty);
            if ty.is_raw_char() {
                self.store_byte(reg, SP, stack_offset);
            } else {
                self.load(reg, SP, stack_offset);
            }
            return reg;
        }

        if let Some(&active_reg) = self.ssa_registers.get(&ssa.index()) {
            // The value is already in a live register, so return it.
            assert_eq!(register_kind(ty), (active_reg.0, active_reg.1));
            return active_reg;
        }

        // This is, lexically, a read before write. We must be emitting a MOV for a phi node of a loop.
        assert!(
            self.liveness.block_start_index[self.current] > self.op_index,
            "Read before write but not looking ahead."
        );

        // Allocate the register now and trust that the phi is correct and won't actually read until it's set inside the loop.
        self.reg_for(ssa)
        // TODO: assert(ssa is second branch of phi node)
    }

    // Stores a value from a register into the stack slot of an ssa.
    // The caller may not use this register again (they must get a new one from the queue because we might have chosen to reuse this one).
    fn set_ssa(&mut self, ssa: &Ssa, value: Reg) {
        self.assert_live(ssa);
        let ty = *self.func.type_of(ssa);
        if let Some(stack_offset) = self.ssa_offsets.get(ssa) {
            // The value lives on the stack, so save it.
            if ty.is_raw_char() {
                self.store_byte(value, SP, *stack_offset);
            } else {
                self.store(value, SP, *stack_offset);
            }
            self.drop_reg(value);
            return;
        }

        let active_reg = if let Some(&active_reg) = self.ssa_registers.get(&ssa.index()) {
            if value == active_reg {
                // NO-OP, the value is already in the right place.
                return;
            }

            // Second branch of phi node.
            active_reg
        } else {
            // First branch of phi node, allocate a register.
            self.reg_for(ssa)
        };

        // The value lives in a register but it's currently in the wrong one.
        // For example, phi nodes will always hit this because they're the only ones that are reusing an existing value.
        // We can't just steal the register from it because could be coming from either branch at runtime.
        // TODO: bit casts probably hit this currently
        output!(
            self,
            "{:?} {:?}, {:?}",
            active_reg.mov_kind(),
            active_reg,
            value
        );
        // We know this call would be a no-op since we already have the right register.
        // self.set_ssa(ssa, active_reg);
        assert!(value.same_kind(active_reg));
        self.drop_reg(value);
        // TODO: assert(ssa is dest of phi node)
    }

    // Get an unused register with an undefined value but hint that we want to store the new value of <ssa> in it.
    // If you want to read the value of an ssa, you must call get_ssa instead.
    // You need to return this to the queue.
    #[must_use]
    fn reg_for(&mut self, ssa: &Ssa) -> Reg {
        self.assert_live(ssa);
        let ty = self.func.register_types.get(ssa).unwrap();
        if let Some(_) = self.ssa_offsets.get(&ssa) {
            // The value lives on the stack, so just give an extra register and we'll save it later in set_ssa.
            return self.next_reg(ty);
        }

        if let Some(&active_reg) = self.ssa_registers.get(&ssa.index()) {
            // We've already allocated a register for this SSA, so let's give you that
            // so we don't have to move the value in set_ssa.
            // Note: Since it's single assignment, this means either this is an argument or a phi node.
            assert_eq!(register_kind(ty), (active_reg.0, active_reg.1));
            return active_reg;
        }

        // This is the first write of the ssa and we should have room to store it in a register the whole time.
        let reg = self.next_reg(ty);
        self.ssa_registers.insert(ssa.index(), reg);
        // log!("[{}] take {:?} in {:?}", self.op_index, ssa, reg);
        reg
    }

    // You need to return this to the queue.
    #[must_use]
    fn next_reg(&mut self, ty: &CType) -> Reg {
        let (kind, bits) = register_kind(ty);

        let index = self
            .unused_registers
            .iter()
            .position(|s| s.0 == kind)
            .expect("unreachable: Need more registers.");

        // TODO: order matters for arguments so can't blindly swap_remove
        let mut reg = self.unused_registers.remove(index).unwrap();
        reg.1 = bits;
        self.active_registers.push(reg);
        reg
    }

    // TODO: maybe make Register not copy so i can enforce passing it to the allocator. drop impl that panics if not returned to queue properly.
    fn drop_reg(&mut self, register: Reg) {
        if self.ssa_registers.values().any(|&s| s == register) {
            // This register is allocated for an ssa so we'll just leave it there so we can read it later.
            // TODO: liveness check here instead of garbage collecting every tick but need to use op_index+1.
            return;
        }

        log!("DROP {:?}", register);
        let index = self
            .active_registers
            .iter()
            .position(|r| *r == register)
            .unwrap();
        self.active_registers.swap_remove(index);
        // Needs to go on the back because of how im doing arguments.
        self.unused_registers.push_back(register);
        self.corrupt(register);
    }

    // TODO: this is clunky because sometimes it ends up after you jump away. But its for debugging not correctness so its better than nothing.
    fn corrupt(&mut self, mut reg: Reg) {
        if DEBUG_CORRUPT_REGISTERS && reg.2 != 0 {
            // TODO hack              ^ (because X0 is used for return value)
            match reg.0 {
                RegKind::Int => {
                    output!(self, "{:?} {:?}, #{}", AsmOp::MOVZ, reg, 0xABCD);
                }
                RegKind::Float => {
                    reg.1 = Bits::B64;
                    output!(self, "{:?} {:?}, {:?}", AsmOp::FMOV, reg, ZERO);
                }
                RegKind::IntStackPointer | RegKind::IntZero => unreachable!(),
            }
        }
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

    // It's fine that the block names alias across functions because I'm using local labels. That's why I need to specify direction.
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

    // TODO: need to combine these as something that needs you to pass type since its annoying to do every time
    // TODO: need one for shorts
    /// Load one byte and zero extend
    fn load_byte(&mut self, destination: Reg, addr: Reg, offset: usize) {
        output!(self, "LDRB {:?}, [{:?}, #{}]", destination, addr, offset);
    }

    fn store_byte(&mut self, value: Reg, addr: Reg, offset: usize) {
        output!(self, "STRB {:?}, [{:?}, #{}]", value, addr, offset);
    }

    fn get_label(&self, block: Label) -> String {
        if self.current_index < (block.index() + 1) {
            format!("{}f", block.index())
        } else {
            format!("{}b", block.index())
        }
    }

    pub fn get_text(self) -> String {
        let mut result = format!(".data\n{}\n.text\n", self.constants);
        self.text.into_iter().flatten().for_each(|s| {
            result.push_str(&s.concat());
        });
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
        // TODO: we know the next thing is almost always a conditional jump based on this,
        //       so there should be a fast path to use the flags directly instead of adding an extra jump and cmp.

        // Set the destination to zero.
        output!(self, "{:?} {:?}, {:?}", AsmOp::MOV, result_temp, ZERO);

        // Skip one instruction if the condition we care about was false
        output!(self, "{:?} #{}", false_flags, 8);

        // Add one to the result.
        self.simple_with_const(AsmOp::ADD, result_temp, result_temp, 1);
    }

    fn assert_live(&self, ssa: &Ssa) {
        // The vm checks this as well so the IR is probably correct and I messed up and argument in this file.
        assert!(self.liveness.range[ssa].contains(&self.op_index));
    }

    fn build_const_u64(&mut self, result: Reg, n: u64) {
        const OOOI: u64 = u16::MAX as u64;

        // (MOVZ X, #n;) == (MOV X, XZR; MOVK X, #n;) == (SUB X, X, X; ADD X, X, X, #n;)
        output!(self, "{:?} {:?}, #{}", AsmOp::MOVZ, result, n & OOOI);

        // Build the rest of the number in 16 bit chunks.
        for shift in [16, 32, 48] {
            let mask = OOOI << shift;
            let last_max = mask >> 16;
            if n > last_max {
                let chunk = (n & mask) >> shift;
                output!(
                    self,
                    "{:?} {:?}, #{:?}, lsl {}",
                    AsmOp::MOVK,
                    result,
                    chunk,
                    shift
                );
            }
        }
    }

    fn calc_field_offset(&self, object_ptr_addr: &Ssa, field_index: usize) -> u64 {
        let ty = self.func.type_of(object_ptr_addr).deref_type();
        let s = self.ir.get_struct(ty);
        let offset = self.ir.get_field_offset(s, field_index);
        offset as u64
    }
}

// Order matters because function params start at X0 and next_reg pops from the end
fn all_registers() -> impl Iterator<Item = Reg> {
    (0..CORRUPTIBLE_INTS)
        .map(|i| Reg(RegKind::Int, Bits::B64, i))
        .chain((0..CORRUPTIBLE_FLOATS).map(|i| Reg(RegKind::Float, Bits::B64, i)))
}

#[derive(Debug, Copy, Clone)]
pub enum AsmOp {
    // Math
    ADD,
    FADD,
    SUB,
    FSUB,
    MUL,
    FMUL,
    UDIV,
    FDIV,

    // Branch based on flags previously set by cmp/fcmp.
    // https://developer.arm.com/documentation/100076/0100/A32-T32-Instruction-Set-Reference/Condition-Codes/Condition-code-suffixes-and-related-flags?lang=en
    BGT, // signed greater than
    BLS, // unsigned less than or equal
    BHS, // unsigned greater than or equal
    BLO, // unsigned less than
    BHI, // unsigned greater than
    BEQ, // equal
    BNE, // not equal

    /// Compare two int registers and set the magic flags.
    CMP,
    /// Compare two float registers and set the magic flags.
    FCMP,

    /// Branch if zero (without setting flags)
    CBZ,
    /// Return from the function. You must have the right values in LR & FP before using this.
    RET,

    /// Move a value from one int register into another.
    MOV,
    /// Load an immediate and zero the extra bits of the register.
    MOVZ,
    /// Load a shifted immediate without changing other bits of the register.
    MOVK,
    /// Move between float registers OR move raw bits between int<->float without value cast.
    FMOV,

    /// Load from sequential stack slots to a pair of registers
    LDP,
    /// Store a pair of registers to sequential stack slots.
    STP,

    STR,
    LDR,

    /// Unsigned int to float
    UCVTF,
    /// Float to unsigned int. TODO: which rounding mode?
    FCVTAU,
    /// Convert between sizes of float
    FCVT,

    AND,
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
struct Reg(RegKind, Bits, usize);

const SP: Reg = Reg(RegKind::IntStackPointer, Bits::B64, 31);
const ZERO: Reg = Reg(RegKind::IntZero, Bits::B64, 31);
const FP: Reg = Reg(RegKind::Int, Bits::B64, 29);
const LR: Reg = Reg(RegKind::Int, Bits::B64, 30);

/// Checks that these are the same physical register (doesn't care about bit count).
impl PartialEq<Self> for Reg {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.2 == other.2
    }
}

impl Reg {
    fn same_kind(&self, other: Reg) -> bool {
        self.0 == other.0 && self.1 == other.1
    }

    fn mov_kind(&self) -> AsmOp {
        match self.0 {
            RegKind::Int => AsmOp::MOV,
            RegKind::Float => AsmOp::FMOV,
            _ => unreachable!(),
        }
    }
}

fn register_kind(ty: &CType) -> (RegKind, Bits) {
    if ty.is_ptr() {
        return (RegKind::Int, Bits::B64);
    } else {
        match ty.ty {
            ValueType::U64 | ValueType::Bool => (RegKind::Int, Bits::B64),
            ValueType::U32 => (RegKind::Int, Bits::B32),
            ValueType::U8 => (RegKind::Int, Bits::B32), // TODO
            ValueType::F64 => (RegKind::Float, Bits::B64),
            ValueType::F32 => (RegKind::Float, Bits::B32),
            ValueType::U16 => todo!(),
            ValueType::Struct(_) | ValueType::Void=> unreachable!(),
        }
    }
}

fn get_reg_num(ty: &CType, n: usize) -> Reg {
    let info = register_kind(ty);
    Reg(info.0, info.1, n)
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
