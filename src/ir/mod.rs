use crate::ast::{BinaryOp, CType, FuncSignature, LiteralValue, StructSignature, ValueType};
use crate::KEEP_IR_DEBUG_NAMES;
use std::collections::{BTreeSet, HashMap};
use std::fmt::{Display, Formatter};

mod allocs;
mod debug;
mod flow_stack;
mod parse;
mod print;

/// Identifier of a static single-assignment register.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Ssa(usize);

/// Identifier of a basic block that you can jump to.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Label(usize); // sequential indexes into the blocks array

// @Memory u16 would be plenty for those ^ if i care about how big this enum is
#[derive(Clone, PartialEq)]
pub enum Op {
    ConstValue {
        dest: Ssa,
        value: LiteralValue,
        kind: CType,
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
        func_name: Box<str>, // TODO: allow function pointers.
        args: Box<[Ssa]>,
        return_value_dest: Option<Ssa>,
    },

    GetFieldAddr {
        dest: Ssa,
        object_addr: Ssa,
        field_index: usize,
    },

    Cast {
        input: Ssa,
        output: Ssa,
        kind: CastType,
    },
}

#[derive(Clone)]
pub struct Function {
    pub blocks: Vec<Option<Vec<Op>>>, // in the final codegen these will flatten out and labels will become offsets
    var_counter: usize,
    pub signature: FuncSignature,
    pub arg_registers: Vec<Ssa>,
    pub debug_register_names: Vec<Option<String>>,
    pub register_types: HashMap<Ssa, CType>,
}

#[derive(Default)]
pub struct Module {
    pub functions: Vec<Function>,
    pub structs: Vec<StructSignature>,
    pub name: String,
    pub forward_declarations: Vec<FuncSignature>,
}

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum CastType {
    // Does not change the raw bits (void* -> int*). Must be the same size?
    Bits,

    // Extends with leading zeros (u32 -> u64)
    UnsignedIntUp,

    // Cuts off the first bits (u64 -> u32)
    IntDown,

    // (float -> double)
    FloatUp,

    // (double -> float)
    FloatDown,

    FloatToUInt,
    UIntToFloat,

    // For pointer arithmetic, llvm wants it explicit
    IntToPtr,
    PtrToInt,
}

impl Module {
    pub fn get_func(&self, name: &str) -> Option<&Function> {
        self.functions
            .iter()
            .find(|&func| func.signature.name == name)
    }

    pub fn get_struct(&self, name: &str) -> Option<&StructSignature> {
        self.structs.iter().find(|&func| func.name == name)
    }

    pub fn size_of(&self, ty: CType) -> usize {
        if ty.depth > 0 {
            return 8;
        }

        match ty.ty {
            ValueType::U64 => 8,
            ValueType::U8 => 1,
            ValueType::U32 => 4,
            ValueType::F64 => 8,
            ValueType::F32 => 4,
            ValueType::Void => 0,
            ValueType::Struct(name) => {
                let def = self.get_struct(name).unwrap();
                let mut size = 0;
                for (_, field) in &def.fields {
                    size += self.size_of(*field);
                }
                size
            }
        }
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
        self.blocks.push(Some(vec![]));
        Label(self.blocks.len() - 1)
    }

    pub fn push(&mut self, block: Label, op: Op) {
        self.blocks[block.0].as_mut().unwrap().push(op);
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
        let last = self.blocks[block.0].as_ref().unwrap();
        let last = last.last();
        last.is_some() && last.unwrap().is_jump()
    }

    fn finish(&mut self) {
        let mut empty_blocks = Vec::new();
        let mut jump_targets = BTreeSet::new();
        jump_targets.insert(Label(0)); // entry point
        for (i, block) in self.blocks.iter().enumerate() {
            let block = match block {
                None => panic!("Label({}) was none. Probably called func.finish() twice which is not allowed currently.", i),
                Some(b) => b,
            };

            if block.is_empty() {
                empty_blocks.push(Label(i));
                continue;
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
            assert_eq!(jumps, 1, "Label({}) must have exactly one jump", i);

            match block.last().unwrap() {
                &Op::Jump {
                    if_true, if_false, ..
                } => {
                    jump_targets.insert(if_true);
                    jump_targets.insert(if_false);
                }
                &Op::AlwaysJump(target) => {
                    jump_targets.insert(target);
                }
                Op::Return { .. } => {}
                _ => panic!("Label({}) must end with a jump", i),
            }
        }

        // Replace empty blocks with Nones so the backend knows to skip them.
        for block in &empty_blocks {
            assert!(
                !jump_targets.contains(block),
                "Empty block is a jump target."
            );
            self.blocks[block.0] = None;
        }

        for (i, block) in self.blocks.iter().enumerate() {
            match block {
                None => {}
                Some(_) => {
                    assert!(
                        jump_targets.contains(&Label(i)),
                        "Label({}) is not empty but never jumped to.",
                        i
                    );
                }
            }
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
    pub(crate) fn index(&self) -> usize {
        self.0
    }
}
