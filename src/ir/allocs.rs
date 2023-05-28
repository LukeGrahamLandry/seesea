use crate::ast::{Expr, Stmt, UnaryOp};
use crate::ir::flow_stack::{ControlFlowStack, Var};
use crate::ir::{Label, Ssa};
use std::collections::HashSet;

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
            let new_results = Var(name.as_str(), control.current_scope());
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
    }
}

fn walk_expr<'ast>(
    control: &ControlFlowStack<'ast>,
    expr: &'ast Expr,
    results: &mut HashSet<Var<'ast>>,
) {
    match expr {
        Expr::Binary { left, right, .. } => {
            walk_expr(control, left, results);
            walk_expr(control, right, results);
        }
        Expr::Unary { value, op } => {
            if *op == UnaryOp::AddressOf {
                match value.as_ref() {
                    Expr::GetVar { name } => {
                        let variable = control.resolve_name(name).unwrap_or_else(|| {
                            panic!("Cannot access undeclared variable {}", name)
                        });
                        results.insert(variable);
                    }
                    _ => unreachable!(),
                }
            }
            walk_expr(control, value, results);
        }
        Expr::Call { func, args } => {
            walk_expr(control, func, results);
            for arg in args {
                walk_expr(control, arg, results);
            }
        }
        Expr::GetVar { .. } | Expr::Literal { .. } | Expr::Default(_) => {}
    }
}
