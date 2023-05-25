//! AST -> IR

use crate::ast;
use crate::ast::{Expr, LiteralValue, Stmt};
use crate::ir;
use crate::ir::{Label, Op, Ssa};
use std::collections::HashMap;

#[derive(Default)]
struct AstParser<'ast> {
    ir: ir::Module,
    func: Option<ir::Function>, // needs to become a stack if i allow parsing nested functions i guess?
    variables: HashMap<&'ast str, Ssa>, // need to keep track of multiple blocks. maybe insert phis for anything used in if to start
}

impl From<ast::Module> for ir::Module {
    fn from(value: ast::Module) -> Self {
        parse_ast(value)
    }
}

fn parse_ast(program: ast::Module) -> ir::Module {
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
        let mut entry = self.func_mut().new_block();
        self.emit_statement(&input.body, &mut entry);
        self.func_mut().assert_valid();
        self.ir.functions.push(self.func.take().unwrap());
    }

    fn emit_statement(&mut self, stmt: &'ast Stmt, block: &mut Label) {
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
                self.emit_expr(expr, *block); // discards return value.
            }
            Stmt::DeclareVar { name, value, .. } => {
                let var = self
                    .emit_expr(value, *block)
                    .expect("Variable type cannot be void.");
                self.variables.insert(name, var); // TODO: track types or maybe the ir should handle on the ssa?
            }
            Stmt::Return { value } => match value {
                None => todo!(),
                Some(value) => {
                    let value = self.emit_expr(value.as_ref(), *block);
                    self.func_mut().push(*block, Op::Return { value });
                }
            },
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                self.emit_if_stmt(block, condition, then_body, else_body);
            }
        }
    }

    // TODO: this whole passing around a mutable block pointer is scary. idk if it works.
    //         it means you can never rely on being in the same block as you were before parsing a statement.
    //         but that should be fine because its where you would be after flowing through that statement
    fn emit_if_stmt(
        &mut self,
        block: &mut Label,
        condition: &'ast Expr,
        then_body: &'ast Stmt,
        else_body: &'ast Stmt,
    ) {
        // TODO: coerce bool
        let condition = self
            .emit_expr(condition, *block)
            .expect("If condition cannot be void.");
        let mut if_true = self.func_mut().new_block();
        self.emit_statement(then_body, &mut if_true);
        let mut if_false = self.func_mut().new_block();
        self.emit_statement(else_body, &mut if_false);
        // TODO: need to jump to a new basic block from the end of both if and else
        self.func_mut().push(
            *block,
            Op::Jump {
                condition,
                if_true,
                if_false,
            },
        );

        // A new block to continue from when the paths converge.
        let next_block = self.func_mut().new_block();
        if !self.func_mut().ends_with_jump(if_true) {
            self.func_mut().push(if_true, Op::AlwaysJump(next_block));
        }
        if !self.func_mut().ends_with_jump(if_false) {
            self.func_mut().push(if_false, Op::AlwaysJump(next_block));
        }
        *block = next_block;
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
