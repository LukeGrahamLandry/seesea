use crate::ir::{Function, Label, Ssa};
use crate::{ir, log};
use std::fmt::{Debug, Formatter, Write};
use std::rc::Rc;

// Abstraction over the ASM format so we can emit human readable text or direct to binary.
pub trait EmitAarch64: Default {
    fn set_prefix(&mut self, prefix: &Rc<str>);
    fn start_block(&mut self, block: Label);
    fn move_cursor(&mut self, block: Label);
    fn start_func(&mut self, function: &Function);
    fn simple_op(&mut self, op: AsmOp, destination: Register, arg1: Register, arg2: Register);
    fn jump_to(&mut self, block: Label);
    fn single_const(&mut self, op: AsmOp, constant: usize);
    fn single(&mut self, op: AsmOp);
    fn arg_label(&mut self, op: AsmOp, arg: Register, block: Label);
    fn single_label(&mut self, op: AsmOp, block: Label);
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
    fn temp_block(&mut self);
}

#[derive(Default)]
pub struct TextAsm {
    pub text: Vec<Option<String>>,
    func_name: Option<Rc<str>>,
    prefix: Option<Rc<str>>,
    current: usize,
}

macro_rules! output {
    ($self:ident, $($arg:tt)*) => {
        writeln!($self.text[$self.current].as_mut().unwrap(), $($arg)*).unwrap()
    };
}

impl EmitAarch64 for TextAsm {
    fn set_prefix(&mut self, prefix: &Rc<str>) {
        self.prefix = Some(prefix.clone());
    }

    fn start_block(&mut self, block: Label) {
        self.move_cursor(block);
        output!(self, "{}:", block.0);
    }

    fn temp_block(&mut self) {
        output!(self, "80:");
    }

    fn move_cursor(&mut self, block: Label) {
        self.current = block.index() + 1;
        assert!(self.text[self.current].is_some());
    }

    fn start_func(&mut self, function: &ir::Function) {
        self.text.push(Some(String::new()));
        for code in &function.blocks {
            match code {
                None => self.text.push(None),
                Some(_) => self.text.push(Some(String::new())),
            }
        }
        output!(
            self,
            "_{}_{}:",
            self.prefix.as_ref().unwrap(),
            function.signature.name
        );
        self.func_name = Some(function.signature.name.clone());
    }

    fn simple_op(&mut self, op: AsmOp, destination: Register, arg1: Register, arg2: Register) {
        output!(self, "  {:?} {:?}, {:?}, {:?}", op, destination, arg1, arg2);
    }

    fn jump_to(&mut self, block: Label) {
        let b = self.get_label(block);
        output!(self, "    B {}", b);
    }

    fn single_const(&mut self, op: AsmOp, constant: usize) {
        // assert constant in the right range
        output!(self, "  {:?} #{}", op, constant);
    }

    fn single(&mut self, op: AsmOp) {
        output!(self, "  {:?}", op);
    }

    fn arg_label(&mut self, op: AsmOp, arg: Register, block: Label) {
        let b = self.get_label(block);
        output!(self, "  {:?} {:?}, {}", op, arg, b);
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

    fn single_label(&mut self, op: AsmOp, block: Label) {
        let b = self.get_label(block);
        output!(self, "  {:?} {}", op, b);
    }
}

impl TextAsm {
    fn get_label(&self, block: Label) -> String {
        if self.current < (block.index() + 1) {
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
            .for_each(|s| result.push_str(&s));
        log!("==== Direct Aarch64 =====");
        log!("{}", result);
        log!("============");
        result
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AsmOp {
    ADD,
    SUB,
    RET,
    MOV,
    CMP,
    BGT,
    CBZ,
    BLS,
    BHS,
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
