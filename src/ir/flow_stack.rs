use crate::ir::{Label, Ssa};
use std::collections::{HashMap, HashSet};

/// Collects the list of Ssa nodes that are written to in the statement.
/// This is used to generate Phi nodes when control flow diverges.
/// Needs to be a stack because ifs can be nested, etc.
/// The spans over which you need to track branches are not always the same as the lexical scopes used for variable declaration.
/// For example a single statement if would be its own basic block in the IR but would not have a lexical scope.
#[derive(Default)]
pub struct ControlFlowStack<'ast> {
    /// Tracks which variables mutate in each IR block.
    flow: Vec<FlowStackFrame<'ast>>,

    // Tracked for an assertion that the Labels are only pushed once.
    prev_blocks: HashSet<Label>,

    /// Lexical scopes that effect name resolution
    scopes: Vec<LexScope>,
    total_scope_count: usize,
}

pub struct FlowStackFrame<'ast> {
    pub block: Label,
    pub mutations: HashMap<Var<'ast>, Ssa>,
}

/// Uniquely identifies a lexical scope. These DO NOT correspond to depth of nesting (they are never reused).
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct LexScope(pub(crate) usize);

/// Uniquely identifies a variable declaration in the source code by noting which block it came from.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Var<'ast>(pub &'ast str, pub LexScope);

impl<'ast> ControlFlowStack<'ast> {
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
    pub fn pop_flow_frame(&mut self) -> FlowStackFrame<'ast> {
        self.flow.pop().expect("Can't pop empty ControlFlowStack")
    }

    pub fn set(&mut self, variable: Var<'ast>, new_register: Ssa) {
        match self.flow.last_mut() {
            None => {
                // Nobody pushed a frame so we don't care about tracking yet.
            }
            Some(frame) => {
                frame.mutations.insert(variable, new_register);
            }
        }
    }

    pub fn get(&self, variable: Var) -> Option<Ssa> {
        for frame in self.flow.iter().rev() {
            if let Some(register) = frame.mutations.get(&variable) {
                return Some(*register);
            }
        }
        None
    }

    pub fn is_empty(&self) -> bool {
        self.flow.is_empty() && self.scopes.is_empty()
    }

    pub fn clear(&mut self) {
        let no_scopes = self.flow.is_empty() && self.scopes.is_empty();
        assert!(no_scopes);
        self.total_scope_count = 0;
        self.prev_blocks.clear();
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(LexScope(self.total_scope_count));
        self.total_scope_count += 1;
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop().expect("You should always be in a scope.");
    }

    pub fn current_scope(&self) -> LexScope {
        *self.scopes.last().unwrap()
    }

    pub fn resolve_name(&self, name: &'ast str) -> Var<'ast> {
        for scope in self.scopes.iter().rev() {
            let var = Var(name, *scope);
            if self.get(var).is_some() {
                return var;
            }
        }
        panic!("Cannot access undefined variable {}", name);
    }
}
