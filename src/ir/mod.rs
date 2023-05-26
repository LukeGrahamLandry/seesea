use crate::ast::{BinaryOp, FuncSignature, ValueType};
use crate::KEEP_IR_DEBUG_NAMES;
use std::fmt::{write, Display, Formatter};

mod debug;
mod flow_stack;
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

/// Identifier of a static single-assignment register.
// TODO: should know its type? easy to change since its opaque to other modules.
// TODO: could have a lifetime tied to the function? that would be such a pain in the ass to use tho.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Ssa(pub(crate) usize);

/// Identifier of a basic block that you can jump to.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Label(usize);

#[derive(Clone, PartialEq)]
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

    Call {
        func_name: String, // TODO: allow function pointers.
        args: Vec<Ssa>,
        return_value_dest: Ssa,
    },
}

#[derive(Clone)]
pub struct Function {
    pub blocks: Vec<Vec<Op>>, // in the final codegen these will flatten out and labels will become offsets
    var_counter: usize,
    pub sig: FuncSignature,
    pub arg_registers: Vec<Ssa>,
    pub debug_register_names: Vec<Option<String>>,
}

#[derive(Default)]
pub struct Module {
    pub functions: Vec<Function>,
    pub name: String,
}

impl Module {
    pub fn get_func(&self, name: &str) -> Option<&Function> {
        self.functions.iter().find(|&func| func.sig.name == name)
    }
}

impl Function {
    pub fn new(sig: FuncSignature) -> Self {
        Function {
            blocks: vec![],
            var_counter: 0,
            sig,
            arg_registers: vec![],
            debug_register_names: vec![],
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
        self.debug_register_names.push(None);
        self.var_counter += 1;
        Ssa(self.var_counter - 1)
    }

    /// This taking a closure makes the api uglier but means it won't do the
    /// the heap allocations etc if the flag is off (even if i make the flag a runtime thing instead of a const).
    fn set_debug<S: Into<String>>(&mut self, ssa: Ssa, get_name: impl FnOnce() -> S) {
        if KEEP_IR_DEBUG_NAMES {
            self.debug_register_names[ssa.0] = Some(get_name().into());
        }
    }

    pub fn constant_int(&mut self, block: Label, value: u64) -> Ssa {
        let var = self.next_var();
        self.set_debug(var, || format!("const_{}", value));
        let op = Op::ConstInt { dest: var, value };
        self.push(block, op);
        var
    }

    fn ends_with_jump(&self, block: Label) -> bool {
        let last = self.blocks[block.0].last();
        last.is_some() && last.unwrap().is_jump()
    }

    fn assert_valid(&self) {
        for block in &self.blocks {
            if block.is_empty() {
                // TODO: assert!(false);
                //      cant have this because it implies you could fall out of the function.
                //      llvm catches that in its own validation pass but i put in a garbage return because i dont want top deal with it rn
                return;
            }

            // Check Phi placement.
            let mut phi_over = false;
            for op in block {
                if phi_over {
                    if let Op::Phi { .. } = op {
                        panic!("All phi nodes must be at the beginning of the block.");
                    }
                } else if let Op::Phi { .. } = op {
                } else {
                    phi_over = true;
                }
            }

            // Exactly one jump op as the last instruction.
            let jumps = block.iter().filter(|op| op.is_jump()).count();
            assert_eq!(jumps, 1);
            assert!(block.last().unwrap().is_jump());
        }
    }

    pub fn entry_point(&self) -> Label {
        Label(0)
    }

    pub fn param_registers(&self) -> impl Iterator<Item = Ssa> {
        self.arg_registers.clone().into_iter()
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

impl Ssa {
    pub fn index(&self) -> usize {
        self.0
    }
}
