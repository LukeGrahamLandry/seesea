use crate::ir::{Label, Ssa};
use std::fmt::{Debug, Formatter, Write};
use std::rc::Rc;

// Abstraction over the ASM format so we can emit human readable text or direct to binary.
pub trait EmitAarch64: Default {
    fn start_block(&mut self, block: Label);
    fn start_func(&mut self, name: &Rc<str>);
    fn simple_op(&mut self, op: AsmOp, destination: Register, arg1: Register, arg2: Register);
    fn jump_to(&mut self, block: Label);
    fn single(&mut self, op: AsmOp);
    fn pair(&mut self, op: AsmOp, destination: Register, arg1: Register);
    fn simple_with_const(
        &mut self,
        op: AsmOp,
        destination: Register,
        arg1: Register,
        arg2_constant: usize,
    );
    fn load(&mut self, destination: Register, addr: Register, offset: usize);
    fn store(&mut self, value: Register, addr: Register, offset: usize);
}

#[derive(Default)]
pub struct TextAsm {
    pub text: String,
    func_name: Option<Rc<str>>,
}

macro_rules! output {
    ($self:ident, $($arg:tt)*) => {
        writeln!($self.text, $($arg)*).unwrap()
    };
}

impl EmitAarch64 for TextAsm {
    fn start_block(&mut self, block: Label) {
        output!(self, ".{}_b{}:", self.func_name.as_ref().unwrap(), block.0);
    }

    fn start_func(&mut self, name: &Rc<str>) {
        output!(self, "{}:", name);
        self.func_name = Some(name.clone());
    }

    fn simple_op(&mut self, op: AsmOp, destination: Register, arg1: Register, arg2: Register) {
        output!(self, "  {:?} {:?}, {:?}, {:?}", op, destination, arg1, arg2);
    }

    fn jump_to(&mut self, block: Label) {
        output!(
            self,
            "    B .{}_b{}",
            self.func_name.as_ref().unwrap(),
            block.0
        );
    }

    fn single(&mut self, op: AsmOp) {
        output!(self, "  {:?}", op);
    }

    fn pair(&mut self, op: AsmOp, destination: Register, arg1: Register) {
        output!(self, "  {:?} {:?}, {:?}", op, destination, arg1);
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
            "  {:?} {:?}, {:?}, #{}",
            op,
            destination,
            arg1,
            arg2_constant
        );
    }

    fn load(&mut self, destination: Register, addr: Register, offset: usize) {
        output!(self, "  LDR {:?}, [{:?}, #{}]", destination, addr, offset);
    }

    fn store(&mut self, value: Register, addr: Register, offset: usize) {
        output!(self, "  STR {:?}, [{:?}, #{}]", value, addr, offset);
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AsmOp {
    ADD,
    SUB,
    RET,
    MOV,
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
