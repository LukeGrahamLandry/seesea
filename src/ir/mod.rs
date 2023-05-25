use crate::ast::{BinaryOp, FuncSignature, ValueType};
use std::fmt::{write, Display, Formatter};
use std::ops::Index;

mod parse;
mod print;

// bytecode type thing with ssa so every variable assignment is unique
// then i can keep track of what variable each register holds throughout the program.
// this separates the register colouring problem from the simplifying ast nodes.
// other than that, try to have the same semantics as assembly.
// need a way to know the last time a ssa thing is used.
// ref counting and a drop impl feels really clever but would just be an upper bound.
// if i make this close enough to the llvm ir then i can always bail out and use that for other backends.
// represent the concept of a basic block (has no branches or loops except for last op).
// be able to execute the ir?
// test assertion that each Ssa is used in a `dest` exactly once.
// output this as c

/// Identifier of a static single-assignment register.
// TODO: should know its type?
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Ssa(usize);

/// Identifier of a basic block that you can jump to.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Label(usize);

#[derive(Copy, Clone, PartialEq)]
pub enum Op {
    ConstInt {
        dest: Ssa,
        value: u64,
    },
    Binary {
        dest: Ssa,
        a: Ssa,
        b: Ssa,
        kind: BinaryOp, // TODO: should this be a different type than used in the AST?
    },
    Load {
        dest: Ssa,
        addr: Ssa,
    },
    Store {
        dest: Ssa,
        addr: Ssa,
    },

    // dont need? was going to use for expressing phi but no
    Move {
        dest: Ssa,
        source: Ssa,
    },

    /// Conditional jump to another block.
    Jump {
        condition: Ssa,
        if_true: Label,
        if_false: Label,
    },

    AlwaysJump(Label),

    /// Choose which value to use based on which block we were in last.
    Phi {
        dest: Ssa,
        a: (Label, Ssa),
        b: (Label, Ssa),
    },
    Return {
        value: Option<Ssa>,
    },

    /// Allocate enough space on the stack to hold a specific type and put a pointer to it in a register.
    StackAlloc {
        dest: Ssa,
        ty: ValueType,
    },
}

#[derive(Clone)]
pub struct Function {
    pub blocks: Vec<Vec<Op>>, // in the final codegen these will flatten out and labels will become offsets
    var_counter: usize,
    pub sig: FuncSignature,
}

#[derive(Default)]
pub struct Module {
    pub functions: Vec<Function>,
}

impl Function {
    pub fn new(sig: FuncSignature) -> Self {
        Function {
            blocks: vec![],
            var_counter: 0,
            sig,
        }
    }

    #[must_use]
    pub fn new_block(&mut self) -> Label {
        self.blocks.push(vec![]);
        Label(self.blocks.len() - 1)
    }

    pub fn push(&mut self, block: Label, op: Op) {
        self.blocks[block.0].push(op);
    }

    pub fn next_var(&mut self) -> Ssa {
        self.var_counter += 1;
        Ssa(self.var_counter - 1)
    }

    pub fn constant_int(&mut self, block: Label, value: u64) -> Ssa {
        let var = self.next_var();
        let op = Op::ConstInt { dest: var, value };
        self.push(block, op);
        var
    }

    fn ends_with_jump(&self, block: Label) -> bool {
        let last = self.blocks[block.0].last();
        last.is_some() && last.unwrap().is_jump()
    }

    fn assert_valid(&self) {
        // TODO: assert all paths reach a return statement.
        //       c lets you just fall through and return a default value but my ir must fill that in at parse time.
        for block in &self.blocks {
            // TODO: assert no other jumps or returns in the block;
            let last = block.last(); // TODO .expect("No empty blocks");
            assert!(last.is_none() || last.unwrap().is_jump());
        }
    }
}

impl Display for Ssa {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}

impl Label {
    pub fn index(self) -> usize {
        self.0
    }
}

impl Op {
    pub fn is_jump(&self) -> bool {
        matches!(
            self,
            Op::Return { .. } | Op::Jump { .. } | Op::AlwaysJump(_)
        )
    }
}
