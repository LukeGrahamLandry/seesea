use crate::ast::FuncSource;
use crate::ast::{AnyModule, BinaryOp, CType, FuncRepr, FuncSignature, LiteralValue, OpDebugInfo};
use crate::util::imap::IndexMap;
use crate::KEEP_IR_DEBUG_NAMES;
use std::borrow::Borrow;
use std::collections::BTreeSet;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

pub mod flow_stack;
pub mod liveness;
mod parse;
mod print;

/// Identifier of a static single-assignment register.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Ssa(pub usize);

/// Identifier of a basic block that you can jump to.
#[derive(Default, Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Label(pub usize); // sequential indexes into the blocks array

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
    Return(Option<Ssa>),

    /// Allocate enough space on the stack to hold a specific type and put a pointer to it in a register.
    StackAlloc {
        dest: Ssa,
        ty: CType,
        count: usize,
    },

    Call {
        // TODO: allow function pointers.
        //       instead of names, normal functions could have indexes into an array of signatures on the module
        kind: FuncSource,
        func_name: Rc<str>,
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
    // TODO: use IndexMap?
    pub blocks: Vec<Option<Vec<Op>>>, // in the final codegen these will flatten out and labels will become offsets
    pub blocks_debug_lines: Vec<Option<Vec<OpDebugInfo>>>, // in the final codegen these will flatten out and labels will become offsets
    var_counter: usize,
    pub signature: FuncSignature,
    pub arg_registers: Vec<Ssa>,
    pub debug_register_names: Vec<Option<String>>, // TODO: use IndexMap?
    pub register_types: IndexMap<Ssa, CType>,
    pub required_stack_bytes: usize,
}

pub type Module = AnyModule<Function>;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum CastType {
    // Does not change the raw bits (void* -> int*). Must be the same size.
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

    // For conditions, llvm wants the types to be i1
    // TODO: i might be implementing these wrong because llvm loses info but others dont. but these casts are only inserted by compiler so i think it doesnt matter.
    IntToBool,
    BoolToInt,
}

impl Function {
    pub fn new(sig: FuncSignature) -> Self {
        Function {
            blocks: vec![],
            blocks_debug_lines: vec![],
            var_counter: 0,
            signature: sig,
            arg_registers: vec![],
            debug_register_names: vec![],
            register_types: Default::default(),
            required_stack_bytes: 0,
        }
    }

    #[must_use]
    pub fn new_block(&mut self) -> Label {
        self.blocks.push(Some(vec![]));
        self.blocks_debug_lines.push(Some(vec![]));
        Label(self.blocks.len() - 1)
    }

    pub fn push(&mut self, block: Label, op: Op, line: OpDebugInfo) {
        self.blocks[block.0].as_mut().unwrap().push(op);
        self.blocks_debug_lines[block.0]
            .as_mut()
            .unwrap()
            .push(line);
    }

    pub fn push_no_debug(&mut self, block: Label, op: Op) {
        self.blocks[block.0].as_mut().unwrap().push(op);
        self.blocks_debug_lines[block.0].as_mut().unwrap().push(-1);
    }

    #[must_use]
    pub fn next_var(&mut self) -> Ssa {
        self.debug_register_names.push(None);
        self.var_counter += 1;
        Ssa(self.var_counter - 1)
    }

    /// This taking a closure makes the api uglier but means it won't do the
    /// the heap allocations etc if the flag is off (even if i make the flag a runtime thing instead of a const).
    // TODO: this should take more meaningful metadata so I can do things like print name without scope suffix if its unambiguous
    //       and let the backends generate some standard debug info format.
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
                None => panic!(
                    "Label({}) was none. Probably called func.finish() twice which is not allowed currently.",
                    i
                ),
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

        for ty in self.register_types.values() {
            assert!(!ty.is_struct());
        }
    }

    // Only meaningful after calling finish()
    pub fn full_blocks(&self) -> impl Iterator<Item = (Label, &[Op])> {
        self.blocks
            .iter()
            .enumerate()
            .filter(|(_, b)| b.is_some())
            .map(|(i, b)| (Label(i), b.as_ref().unwrap().as_slice()))
    }

    pub fn entry_point(&self) -> Label {
        Label(0)
    }

    pub fn param_registers(&self) -> impl Iterator<Item = Ssa> {
        self.arg_registers.clone().into_iter()
    }

    pub fn type_of(&self, ssa: impl Borrow<Ssa>) -> &CType {
        self.register_types
            .get(ssa.borrow())
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

impl FuncRepr for Function {
    fn get_signature(&self) -> &FuncSignature {
        &self.signature
    }
}

pub fn struct_field_offset(
    ir: &Module,
    func: &Function,
    object_addr: impl Borrow<Ssa>,
    field_index: usize,
) -> usize {
    let ty = func.type_of(object_addr).deref_type();
    let struct_def = ir.get_struct(ty);
    ir.get_field_offset(struct_def, field_index)
}

#[test]
fn zero_cost_typed_indexes() {
    use std::mem::size_of;
    assert_eq!(size_of::<usize>(), size_of::<Label>());
    assert_eq!(size_of::<usize>(), size_of::<Ssa>());
}
