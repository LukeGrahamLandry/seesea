use crate::ast::{CType, Expr, Stmt, UnaryOp, ValueType};
use crate::ir::flow_stack::{ControlFlowStack, Var};
use crate::ir::{Label, Ssa};

// TODO: be less slow
pub fn needs_stack_address(root: &Stmt, variable: Var) -> bool {
    let mut stack = ControlFlowStack::default();
    stack.push_flow_frame(Label(0));
    stack.push_scope();
    // TODO: function arguments live here.
    stack.push_scope();
    walk_stmt(&mut stack, root, variable)
}

fn walk_stmt<'ast>(
    control: &mut ControlFlowStack<'ast>,
    stmt: &'ast Stmt,
    variable: Var<'ast>,
) -> bool {
    match stmt {
        Stmt::Block { body, .. } => {
            control.push_scope();
            for stmt in body {
                if walk_stmt(control, stmt, variable) {
                    return true;
                }
            }
            control.pop_scope();
        }
        Stmt::Expression { expr } => {
            if walk_expr(control, expr, variable) {
                return true;
            }
        }
        Stmt::DeclareVar { name, value, .. } => {
            let new_variable = Var(name.as_str(), control.current_scope());
            control.set(new_variable, Ssa(0)); // don't actually care about the ssas being unique/correct

            if walk_expr(control, value, variable) {
                return true;
            }
        }
        Stmt::If {
            condition,
            else_body,
            then_body,
        } => {
            if walk_expr(control, condition, variable)
                || walk_stmt(control, then_body, variable)
                || walk_stmt(control, else_body, variable)
            {
                return true;
            }
        }
        Stmt::Return { value } => {
            if let Some(value) = value {
                if walk_expr(control, value, variable) {
                    return true;
                }
            }
        }
        Stmt::While { condition, body } => {
            if walk_expr(control, condition, variable) || walk_stmt(control, body, variable) {
                return true;
            }
        }
    }

    false
}

fn walk_expr<'ast>(
    control: &ControlFlowStack<'ast>,
    expr: &'ast Expr,
    variable: Var<'ast>,
) -> bool {
    match expr {
        Expr::Binary { left, right, .. } => {
            if walk_expr(control, left, variable) || walk_expr(control, right, variable) {
                return true;
            }
        }
        Expr::Unary { value, op } => {
            if *op == UnaryOp::AddressOf {
                match value.as_ref() {
                    Expr::GetVar { name } => {
                        let resoloved = control.resolve_name(name).unwrap_or_else(|| {
                            panic!("Cannot access undeclared variable {}", name)
                        });
                        if resoloved == variable {
                            return true;
                        }
                    }
                    _ => unreachable!(),
                }
            }
            if walk_expr(control, value, variable) {
                return true;
            }
        }
        Expr::Call { func, args } => {
            if walk_expr(control, func, variable) {
                return true;
            }
            for arg in args {
                if walk_expr(control, arg, variable) {
                    return true;
                }
            }
        }
        Expr::GetVar { .. } | Expr::Literal { .. } | Expr::Default(_) => {}
    };
    false
}
