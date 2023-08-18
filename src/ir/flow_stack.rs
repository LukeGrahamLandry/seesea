use crate::ast::CType;
use crate::ast::{LexScope, Variable, VariableRef};
use crate::ir::{Label, Op, Ssa};
use crate::util::imap::IndexMap;
use std::collections::{HashMap, HashSet};

/// Collects the list of Ssa nodes that are written to in the statement.
/// This is used to generate Phi nodes when control flow diverges.
/// Needs to be a stack because ifs can be nested, etc.
/// The spans over which you need to track branches are not always the same as the lexical scopes used for variable declaration.
/// For example a single statement if would be its own basic block in the IR but would not have a lexical scope.
#[derive(Default, Debug)]
pub struct ControlFlowStack {
    /// Tracks which variables mutate in each IR block.
    flow: Vec<FlowStackFrame>,

    pub register_types: IndexMap<Ssa, CType>,

    /// Lexical scopes that effect name resolution
    scopes: Vec<LexScope>,
    stack_allocated: Vec<HashSet<VariableRef>>,
    total_scope_count: usize,
    dead_scopes: HashSet<LexScope>,

    // Tracked for assertions
    prev_blocks: HashSet<Label>,
    // prev_ssa: HashSet<Ssa>,
}

#[derive(Debug)]
pub struct FlowStackFrame {
    pub block: Label,
    pub mutations: HashMap<VariableRef, Ssa>,
}

// this is doing redundant tracking of scopes that the resolver handles but I like being able to have the assertions.
// that means it relies on the total_scope_count here being the same as in the resolver
impl ControlFlowStack {
    pub fn push_flow_frame(&mut self, block: Label) {
        assert!(
            self.prev_blocks.insert(block),
            "{:?} was used twice.",
            block
        );
        self.flow.push(FlowStackFrame {
            block,
            mutations: HashMap::new(),
        });
    }

    // You need to use this to update other variables and emit phi nodes
    #[must_use]
    pub fn pop_flow_frame(&mut self) -> FlowStackFrame {
        self.flow.pop().expect("Can't pop empty ControlFlowStack")
    }

    pub fn get(&self, variable: &VariableRef) -> Option<Ssa> {
        for frame in self.flow.iter().rev() {
            if let Some(register) = frame.mutations.get(variable) {
                return Some(*register);
            }
        }
        None
    }

    pub fn get_if_in_scope(&self, variable: &VariableRef) -> Option<Ssa> {
        match self.get(variable) {
            None => {
                // the variable was declared in a scope inside the flow frame, it doesn't exist anymore as we try to bubble up.
                // TODO: make sure `if (1) long x = 10;` is not valid.
                // dont care anymore because resolver handles it
                assert!(
                    self.is_out_of_scope(variable),
                    "{:?} register not found in control stack but is still in scope.",
                    variable
                );
                None
            }
            Some(ssa) => Some(ssa),
        }
    }

    pub fn ssa_type(&self, ssa: Ssa) -> CType {
        self.register_types
            .get(&ssa)
            .expect("Can't type check unused register.")
            .clone()
    }

    pub fn set_stack_alloc(&mut self, variable: VariableRef, addr_register: Ssa) {
        // dont care any more because resolver handles it
        // assert_eq!(variable.scope, self.current_scope());
        self.register_types
            .insert(addr_register, variable.ty.ref_type());
        assert!(self.stack_allocated.last_mut().unwrap().insert(variable));
    }

    pub fn clear(&mut self) {
        let no_scopes =
            self.flow.is_empty() && self.scopes.is_empty() && self.stack_allocated.is_empty();
        assert!(no_scopes);
        self.total_scope_count = 0;
        self.prev_blocks.clear();
        // self.prev_ssa.clear();
    }

    pub fn push_scope(&mut self) {
        self.total_scope_count += 1;
        self.scopes.push(LexScope(self.total_scope_count));
        self.stack_allocated.push(HashSet::new());
    }

    pub fn pop_scope(&mut self) {
        let old_scope = self.scopes.pop().expect("You should always be in a scope.");
        let _ = self
            .stack_allocated
            .pop()
            .expect("You should always be in a scope.");
        // dont care anymore because resolver handles it
        // @Speed
        // assert!(
        //     !stack_alloc.iter().any(|var| var.scope != old_scope),
        //     "Popped scope contained a stack variable from a different scope."
        // );
        self.dead_scopes.insert(old_scope);
    }

    pub fn is_out_of_scope(&self, variable: &Variable) -> bool {
        self.dead_scopes.contains(&variable.scope)
    }

    pub fn current_scope(&self) -> LexScope {
        *self.scopes.last().unwrap()
    }
}

/// Checks that you don't try to patch a write because that doesn't make sense given the SSA format.
// The situation is you have a loop and you need to parse the body to see if it modifies the condition variables
// and then replace all those reads with phi nodes. So you need to be patching below where the phi nodes get created
// so you know there can never be writes to them because it's single assignment.
pub fn patch_reads(op: &mut Op, changes: &HashMap<Ssa, Ssa>) {
    match op {
        Op::ConstValue { dest, .. } => {
            assert!(!changes.contains_key(dest));
        }
        Op::Binary { dest, a, b, .. } => {
            assert!(!changes.contains_key(dest));
            swap(a, changes);
            swap(b, changes);
        }
        Op::LoadFromPtr { value_dest, addr } => {
            assert!(!changes.contains_key(value_dest));
            swap(addr, changes);
        }
        Op::StoreToPtr { addr, value_source } => {
            swap(addr, changes);
            swap(value_source, changes);
        }
        Op::Jump { condition, .. } => {
            swap(condition, changes);
        }
        Op::AlwaysJump(_) => {}
        Op::Phi { dest, a, b } => {
            assert!(!changes.contains_key(dest));
            swap(&mut a.1, changes);
            swap(&mut b.1, changes);
        }
        Op::Return(value) => {
            if let Some(value) = value {
                swap(value, changes);
            }
        }
        Op::StackAlloc { dest, .. } => {
            assert!(!changes.contains_key(dest));
        }
        Op::Call {
            args,
            return_value_dest,
            ..
        } => {
            if let Some(dest) = return_value_dest {
                assert!(!changes.contains_key(dest));
            }

            for arg in args.iter_mut() {
                swap(arg, changes);
            }
        }
        Op::GetFieldAddr {
            dest, object_addr, ..
        } => {
            assert!(!changes.contains_key(dest));
            swap(object_addr, changes);
        }
        Op::Cast { input, output, .. } => {
            assert!(!changes.contains_key(output));
            swap(input, changes);
        }
    }
}

pub fn swap(ssa: &mut Ssa, changes: &HashMap<Ssa, Ssa>) {
    if changes.contains_key(ssa) {
        *ssa = *changes.get(ssa).unwrap();
    }
}
