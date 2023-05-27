use crate::ast::CType;
use crate::ir::{Label, Ssa};
use std::collections::{HashMap, HashSet};

/// Collects the list of Ssa nodes that are written to in the statement.
/// This is used to generate Phi nodes when control flow diverges.
/// Needs to be a stack because ifs can be nested, etc.
/// The spans over which you need to track branches are not always the same as the lexical scopes used for variable declaration.
/// For example a single statement if would be its own basic block in the IR but would not have a lexical scope.
#[derive(Default, Debug)]
pub struct ControlFlowStack<'ast> {
    /// Tracks which variables mutate in each IR block.
    flow: Vec<FlowStackFrame<'ast>>,

    // Tracked for an assertion that the Labels are only pushed once.
    prev_blocks: HashSet<Label>,
    pub register_types: HashMap<Ssa, CType>,
    stack_var_types: HashMap<Var<'ast>, CType>,

    /// Lexical scopes that effect name resolution
    scopes: Vec<LexScope>,
    stack_allocated: Vec<HashSet<Var<'ast>>>,
    total_scope_count: usize,
}

#[derive(Debug)]
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
        // @Speed
        assert!(
            !self.is_stack_alloc(variable),
            "{:?} is stack allocated. Can't set it's register.",
            variable
        );
        // TODO: assert Ssa is unique? but that would mess with allocs.rs making up fake ones that it never read. that should be a special method self.fake_declare(Var). llvm emit checks anyway

        match self.flow.last_mut() {
            None => {
                panic!("There must always be a FlowStackFrame for tracking registers.")
            }
            Some(frame) => {
                frame.mutations.insert(variable, new_register);
            }
        }
    }

    pub fn get(&self, variable: Var<'ast>) -> Option<Ssa> {
        for frame in self.flow.iter().rev() {
            if let Some(register) = frame.mutations.get(&variable) {
                return Some(*register);
            }
        }
        None
    }

    pub fn ssa_type(&self, ssa: Ssa) -> &CType {
        self.register_types
            .get(&ssa)
            .expect("Can't type check unused register.")
    }

    pub fn var_type(&self, var: Var<'ast>) -> &CType {
        let ssa = self.get(var);
        match ssa {
            None => {
                assert!(self.is_stack_alloc(var)); // @Speed
                self.stack_var_types
                    .get(&var)
                    .expect("Can't type check unused variable.")
            }
            Some(ssa) => self.ssa_type(ssa),
        }
    }

    pub fn set_stack_alloc(&mut self, variable: Var<'ast>, value_ty: &CType, addr_register: Ssa) {
        assert_eq!(variable.1, self.current_scope());
        assert!(self.stack_allocated.last_mut().unwrap().insert(variable));
        self.stack_var_types.insert(variable, *value_ty);
        self.register_types
            .insert(addr_register, value_ty.ref_type());
    }

    pub fn is_stack_alloc(&self, variable: Var<'ast>) -> bool {
        for scope in self.stack_allocated.iter().rev() {
            if scope.contains(&variable) {
                return true;
            }
        }
        false
    }

    pub fn is_empty(&self) -> bool {
        self.flow.is_empty() && self.scopes.is_empty()
    }

    pub fn clear(&mut self) {
        let no_scopes =
            self.flow.is_empty() && self.scopes.is_empty() && self.stack_allocated.is_empty();
        assert!(no_scopes);
        self.total_scope_count = 0;
        self.prev_blocks.clear();
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(LexScope(self.total_scope_count));
        self.stack_allocated.push(HashSet::new());
        self.total_scope_count += 1;
    }

    pub fn pop_scope(&mut self) {
        let old_scope = self.scopes.pop().expect("You should always be in a scope.");
        let stack_alloc = self
            .stack_allocated
            .pop()
            .expect("You should always be in a scope.");
        debug_assert!(!stack_alloc.iter().any(|var| var.1 != old_scope));
    }

    pub fn current_scope(&self) -> LexScope {
        *self.scopes.last().unwrap()
    }

    pub fn resolve_name(&self, name: &'ast str) -> Option<Var<'ast>> {
        for (i, scope) in self.scopes.iter().enumerate().rev() {
            let var = Var(name, *scope);
            if self.get(var).is_some() {
                return Some(var);
            }
            if self.stack_allocated[i].contains(&var) {
                return Some(var);
            }
        }
        None
    }
}
