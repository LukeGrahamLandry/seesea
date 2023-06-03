// Abstraction over the ASM format so we can emit human readable text or direct to binary.
pub trait EmitAarch64 {
    fn simple_op(&mut self, op: OpName, destination: Register, arg1: Register, arg2: Register);
}

pub struct TextAsm {}

impl EmitAarch64 for TextAsm {
    fn simple_op(&mut self, op: OpName, destination: Register, arg1: Register, arg2: Register) {
        todo!()
    }
}

pub enum OpName {
    ADD,
}

pub struct Register(u8);
