//! AST -> IR

use crate::ast;
use crate::ast::{Expr, LiteralValue, Program, Stmt};
use crate::ir;
use crate::ir::{Label, Op, Ssa};
use std::collections::HashMap;

#[derive(Default)]
struct AstParser<'ast> {
    ir: ir::Module,
    func: Option<ir::Function>, // needs to become a stack if i allow parsing nested functions i guess?
    variables: HashMap<&'ast str, Ssa>,
}

impl From<ast::Program> for ir::Module {
    fn from(value: Program) -> Self {
        parse_ast(value)
    }
}

fn parse_ast(program: ast::Program) -> ir::Module {
    let mut parser = AstParser::default();

    for func in program.functions.iter() {
        parser.parse_function(func)
    }

    assert!(parser.func.is_none());
    parser.ir
}

impl<'ast> AstParser<'ast> {
    fn parse_function(&mut self, input: &'ast ast::Function) {
        assert!(self.func.is_none());
        self.func = Some(ir::Function::new(input.signature.clone()));
        let entry = self.func_mut().new_block();
        self.emit_statement(&input.body, entry);
        self.ir.functions.push(self.func.take().unwrap());
    }

    fn emit_statement(&mut self, stmt: &'ast Stmt, block: Label) {
        match stmt {
            Stmt::Block { body } => {
                // let inner_block = self.func_mut().new_block();
                // TODO: I want to make another block and jump in and then back out?
                //      or maybe that just compiles out and only changes the variable scope.
                for stmt in body {
                    self.emit_statement(stmt, block);
                }
            }
            Stmt::Expression { expr } => {
                self.emit_expr(expr, block); // discards return value.
            }
            Stmt::DeclareVar { name, value, .. } => {
                let var = self
                    .emit_expr(value, block)
                    .expect("Variable type cannot be void.");
                self.variables.insert(name, var); // TODO: track types or maybe the ir should handle on the ssa?
            }
            Stmt::Return { value } => match value {
                None => todo!(),
                Some(value) => {
                    let value = self.emit_expr(value.as_ref(), block);
                    self.func_mut().push(block, Op::Return { value });
                }
            },
        }
    }

    fn emit_expr(&mut self, expr: &'ast Expr, block: Label) -> Option<Ssa> {
        match expr {
            Expr::Binary { left, op, right } => {
                let a = self
                    .emit_expr(left, block)
                    .expect("Binary operand cannot be void.");
                let b = self
                    .emit_expr(right, block)
                    .expect("Binary operand cannot be void.");
                let dest = self.func_mut().next_var();
                self.func_mut().push(
                    block,
                    Op::Binary {
                        dest,
                        a,
                        b,
                        kind: *op,
                    },
                );
                Some(dest)
            }
            Expr::Literal { value } => match value {
                LiteralValue::Number { value } => {
                    Some(self.func_mut().constant_int(block, *value as u64))
                }
                _ => todo!(),
            },
            Expr::GetVar { name } => {
                let ssa = self
                    .variables
                    .get(name.as_str())
                    .expect("Variables must be declared before access.");

                Some(*ssa)
            }
            _ => todo!(),
        }
    }

    fn func_mut(&mut self) -> &mut ir::Function {
        self.func.as_mut().unwrap()
    }
}
