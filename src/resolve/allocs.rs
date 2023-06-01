use crate::ast::{RawExpr, Stmt};
use crate::ir::flow_stack::{ControlFlowStack, Var};
use crate::ir::{Label, Ssa};
use std::collections::HashSet;
use std::ops::Deref;

// If I keep this, it would be a good place to put other things I want to do in a pre-pass.
// Idk if keeping this distinction is silly. Does clang just use alloca everywhere? Looks like it in Compiler Explorer.
pub fn collect_stack_allocs<'ast>(root: &'ast Stmt, results: &mut HashSet<Var<'ast>>) {
    let mut stack = ControlFlowStack::default();
    stack.push_flow_frame(Label(0));
    stack.push_scope();
    // TODO: function arguments live here.
    stack.push_scope();
    walk_stmt(&mut stack, root, results);
}

fn walk_stmt<'ast>(
    control: &mut ControlFlowStack<'ast>,
    stmt: &'ast Stmt,
    results: &mut HashSet<Var<'ast>>,
) {
    match stmt {
        Stmt::Block { body, .. } => {
            control.push_scope();
            for stmt in body {
                walk_stmt(control, stmt, results);
            }
            control.pop_scope();
        }
        Stmt::Expression { expr } => {
            walk_expr(control, expr, results);
        }
        Stmt::DeclareVar { name, value, .. } => {
            let new_results = Var(name.as_ref(), control.current_scope());
            control.set(new_results, Ssa(0)); // don't actually care about the ssas being unique/correct

            walk_expr(control, value, results);
        }
        Stmt::If {
            condition,
            else_body,
            then_body,
        } => {
            walk_expr(control, condition, results);
            walk_stmt(control, then_body, results);
            walk_stmt(control, else_body, results);
        }
        Stmt::Return { value } => {
            if let Some(value) = value {
                walk_expr(control, value, results);
            }
        }
        Stmt::While { condition, body } => {
            walk_expr(control, condition, results);
            walk_stmt(control, body, results);
        }
        Stmt::For {
            initializer,
            condition,
            increment,
            body,
        } => {
            walk_stmt(control, initializer, results);
            walk_expr(control, condition, results);
            walk_expr(control, increment, results);
            walk_stmt(control, body, results);
        }
        Stmt::Nothing => {}
    }
}

fn walk_expr<'ast>(
    control: &ControlFlowStack<'ast>,
    expr: &'ast RawExpr,
    results: &mut HashSet<Var<'ast>>,
) {
    match expr {
        RawExpr::Binary { left, right, .. } => {
            walk_expr(control, left, results);
            walk_expr(control, right, results);
        }
        RawExpr::Unary(_, value) => {
            walk_expr(control, value, results);
        }
        RawExpr::Call { func, args } => {
            walk_expr(control, func, results);
            for arg in args {
                walk_expr(control, arg, results);
            }
        }
        RawExpr::GetVar { .. } | RawExpr::Literal { .. } | RawExpr::Default(_) => {}
        RawExpr::GetField(object, _) => {
            walk_expr(control, object, results);
        }
        RawExpr::LooseCast(value, _) => {
            walk_expr(control, value, results);
        }
        RawExpr::SizeOfType(_) => {}
        RawExpr::DerefPtr(value) => {
            walk_expr(control, value, results);
        }
        RawExpr::AddressOf(value) => {
            if let RawExpr::GetVar(name) = value.as_ref().deref() {
                let variable = control
                    .resolve_name(name)
                    .unwrap_or_else(|| panic!("Cannot access undeclared variable {}", name));
                results.insert(variable);
            }
            // TODO: make sure address of more complex expressions doesn't need more work
        }
        RawExpr::Assign(place, value) => {
            walk_expr(control, place, results);
            walk_expr(control, value, results);
        }
    }
}
