use crate::ast::{BinaryOp, CType, FuncSignature, ValueType};
use crate::KEEP_IR_DEBUG_NAMES;
use std::collections::HashMap;
use std::fmt::{write, Display, Formatter};

mod allocs;
mod debug;
mod flow_stack;
mod parse;
mod print;

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
    LoadFromPtr {
        value_dest: Ssa,
        addr: Ssa,
    },
    StoreToPtr {
        addr: Ssa,
        value_source: Ssa,
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
        ty: CType,
        count: usize,
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
    pub signature: FuncSignature,
    pub arg_registers: Vec<Ssa>,
    pub debug_register_names: Vec<Option<String>>,
    pub register_types: HashMap<Ssa, CType>,
}

#[derive(Default)]
pub struct Module {
    pub functions: Vec<Function>,
    pub name: String,
}

impl Module {
    pub fn get_func(&self, name: &str) -> Option<&Function> {
        self.functions
            .iter()
            .find(|&func| func.signature.name == name)
    }
}

impl Function {
    pub fn new(sig: FuncSignature) -> Self {
        Function {
            blocks: vec![],
            var_counter: 0,
            signature: sig,
            arg_registers: vec![],
            debug_register_names: vec![],
            register_types: Default::default(),
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

    #[must_use]
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
                        panic!("All phi nodes must be at the beginning of the block (llvm requires this).");
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

        assert_eq!(
            self.register_types.len(),
            self.var_counter,
            "All registers must know their type."
        );
    }

    pub fn entry_point(&self) -> Label {
        Label(0)
    }

    pub fn param_registers(&self) -> impl Iterator<Item = Ssa> {
        self.arg_registers.clone().into_iter()
    }

    pub fn type_of(&self, ssa: &Ssa) -> CType {
        *self
            .register_types
            .get(ssa)
            .expect("Register must have type.")
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
