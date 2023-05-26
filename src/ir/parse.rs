//! AST -> IR

use crate::ast;
use crate::ast::{BinaryOp, Expr, FuncSignature, LiteralValue, Stmt};
use crate::ir;
use crate::ir::debug::IrDebugInfo;
use crate::ir::{Label, Op, Ssa};
use std::collections::HashMap;
use std::marker::PhantomData;

#[derive(Default)]
struct AstParser<'ast> {
    ir: ir::Module,
    func: Option<ir::Function>, // needs to become a stack if i allow parsing nested functions i guess?
    scopes: Vec<LexScope>,
    control: ControlFlowStack<'ast>,
    total_scope_count: usize,
    debug: IrDebugInfo<'ast>,
}

/// Uniquely identifies a lexical scope. These DO NOT correspond to depth of nesting (they are never reused).
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
struct LexScope(usize);

/// Uniquely identifies a variable declaration in the source code by noting which block it came from.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
struct Var<'ast>(&'ast str, LexScope);

/// Collects the list of Ssa nodes that are written to in the statement.
/// This is used to generate Phi nodes when control flow diverges.
/// Needs to be a stack because ifs can be nested, etc.
/// The spans over which you need to track branches are not always the same as the lexical scopes used for variable declaration.
/// For example a single statement if would be its own basic block in the IR but would not have a lexical scope.
// @Memory: it never drops entry (like when we exit a c scope).
// It just removes the LexScope from the parser's stack so we never check those when resolving names.
// Leaking memory as god intended!
#[derive(Default)]
struct ControlFlowStack<'ast>(Vec<HashMap<Var<'ast>, Ssa>>);

impl From<ast::Module> for ir::Module {
    fn from(value: ast::Module) -> Self {
        parse_ast(&value).0
    }
}

pub fn parse_ast<'ast>(program: &'ast ast::Module) -> (ir::Module, IrDebugInfo<'ast>) {
    let mut parser: AstParser<'ast> = AstParser::default();

    for func in program.functions.iter() {
        parser.parse_function(func)
    }

    assert!(parser.func.is_none());
    (parser.ir, parser.debug)
}

impl<'ast> AstParser<'ast> {
    fn parse_function(&mut self, input: &'ast ast::Function) {
        assert!(self.func.is_none());
        self.control.push();
        self.func = Some(ir::Function::new(input.signature.clone()));
        let mut entry = self.func_mut().new_block();

        self.push_scope();
        let arguments = input
            .signature
            .param_types
            .iter()
            .zip(input.signature.param_names.iter());
        for (_ty, name) in arguments {
            let variable = Var(name.as_str(), self.current_scope());
            let register = self.func_mut().next_var();
            self.func_mut()
                .set_debug(register, || format!("{}_arg", name));
            self.control.set(variable, register);
            self.func_mut().arg_registers.push(register);
        }
        self.push_scope();
        self.emit_statement(&input.body, &mut entry);
        self.pop_scope();
        self.pop_scope();

        println!("{:?}", self.func_mut());
        self.func_mut().assert_valid();
        self.ir.functions.push(self.func.take().unwrap());
        let _ = self.control.pop();
        assert!(
            self.control.0.is_empty(),
            "Should have no hanging control scopes... until i do globals maybe but those probably need a different representation in ir"
        );

        println!("------------");
    }

    fn emit_statement(&mut self, stmt: &'ast Stmt, block: &mut Label) {
        match stmt {
            Stmt::Block { body, .. } => {
                // Lexical blocks in the source don't directly correspond to the IR blocks used for control flow.
                // Rather, they affect the variable name resolution stack.
                self.push_scope();
                for stmt in body {
                    self.emit_statement(stmt, block);
                }
                self.pop_scope();
            }
            Stmt::Expression { expr } => {
                let _ = self.emit_expr(expr, *block);
            }
            Stmt::DeclareVar { name, value, .. } => {
                let register = self
                    .emit_expr(value, *block)
                    .expect("Variable type cannot be void.");
                // TODO: track types or maybe the ir should handle on the ssa?
                let variable = Var(name.as_str(), self.current_scope());
                self.control.set(variable, register);
                self.func_mut()
                    .set_debug(register, || format!("{}_{}", name, variable.1 .0));
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

    // TODO: this whole passing around a mutable block pointer is scary.
    //         it means you can never rely on being in the same block as you were before parsing a statement.
    //         but that should be fine because its where you would be after flowing through that statement
    fn emit_if_stmt(
        &mut self,
        block: &mut Label,
        condition: &'ast Expr,
        then_body: &'ast Stmt,
        else_body: &'ast Stmt,
    ) {
        let parent_block = *block;
        // TODO: type check that this is an int llvm can use for conditions
        let condition = self
            .emit_expr(condition, *block)
            .expect("If condition cannot be void.");

        // Execution branches into two new blocks.
        let (then_block, mutated_in_then, then_block_returned) = self.parse_branch(then_body);
        let (else_block, mutated_in_else, else_block_returned) = self.parse_branch(else_body);

        self.func_mut().push(
            *block,
            Op::Jump {
                condition,
                if_true: then_block,
                if_false: else_block,
            },
        );

        // A new block to continue from when the paths converge.
        // Both paths jump back here if they didn't return.
        let next_block = self.func_mut().new_block();

        let both_returned = then_block_returned && else_block_returned;
        if both_returned {
            // This whole branch is over.
            // TODO: Don't emit an empty block and assert that the caller is on their last statement.
            *block = next_block;
            return;
        }

        self.terminate_branch(
            parent_block,
            then_block,
            else_block,
            next_block,
            then_block_returned,
            &mutated_in_else,
        );
        self.terminate_branch(
            parent_block,
            else_block,
            then_block,
            next_block,
            else_block_returned,
            &mutated_in_then,
        );

        let neither_returned = !(then_block_returned || else_block_returned);
        if neither_returned {
            self.emit_phi(
                (then_block, mutated_in_then),
                (else_block, mutated_in_else),
                next_block,
            );
        }

        // Reassign the current block pointer. The rest of the function is emitted in the new one.
        *block = next_block;
    }

    fn parse_branch(&mut self, branch_body: &'ast Stmt) -> (Label, HashMap<Var<'ast>, Ssa>, bool) {
        let branch_block = self.func_mut().new_block();
        let mut working_block_pointer = branch_block;
        self.control.push();
        self.emit_statement(branch_body, &mut working_block_pointer);
        let branch_returned = self.func_mut().ends_with_jump(branch_block);
        let mutated_in_branch = self.control.pop();
        (branch_block, mutated_in_branch, branch_returned)
    }

    /// This only emits phi nodes in next_block if the branch returned.
    fn terminate_branch(
        &mut self,
        parent_block: Label,
        branch_block: Label,
        other_block: Label,
        next_block: Label,
        branch_returns: bool,
        mutated_in_other_branch: &HashMap<Var<'ast>, Ssa>,
    ) {
        if branch_returns {
            // This block always returns, so we don't need to emit phi nodes that considers it (even if the variable was mutated in both branches).
            // Just emit phi nodes for anything mutated in the other block.
            self.emit_phi_parent_or_single_branch(
                parent_block,
                other_block,
                next_block,
                mutated_in_other_branch,
            );
        } else {
            // If the branch just flows down to the next statement, emit a jump.
            // Since i kept a garbage block in the ast when they had no else clause,
            // there will always be a block here and it doesn't need a special case.
            self.func_mut()
                .push(branch_block, Op::AlwaysJump(next_block));
        }
    }

    fn emit_phi_parent_or_single_branch(
        &mut self,
        parent_block: Label,
        branch_block: Label,
        new_block: Label,
        mutated_in_branch: &HashMap<Var<'ast>, Ssa>,
    ) {
        // TODO: assert that self.control is looking at the parent_block
        let mut moved_registers = vec![];
        for (variable, branch_register) in mutated_in_branch {
            let parent_register = self.control.get(*variable).unwrap();
            let new_register = self.func_mut().next_var();
            self.func_mut().push(
                new_block,
                Op::Phi {
                    dest: new_register,
                    a: (parent_block, parent_register),
                    b: (branch_block, *branch_register),
                },
            );
            moved_registers.push((variable, new_register));

            let name_a = self.func_mut().name(&parent_register);
            let name_b = self.func_mut().name(&branch_register);
            self.func_mut()
                .set_debug(new_register, || format!("phi__{}__{}__", name_a, name_b));
        }
        // Now that we've updated everything, throw away the registers from before the branching.
        for (variable, register) in moved_registers {
            self.control.set(*variable, register);
        }
    }

    // Assumes you could have come from either if_true or if_false
    fn emit_phi(
        &mut self,
        (if_true, mutated_in_then): (Label, HashMap<Var<'ast>, Ssa>),
        (if_false, mut mutated_in_else): (Label, HashMap<Var<'ast>, Ssa>),
        block: Label,
    ) {
        let mut moved_registers = vec![];
        // We have the set of Vars whose register changed in one of the branches.
        // Now that we've rejoined, future code in this block needs to access different registers depending how it got here.
        for (variable, then_register) in mutated_in_then {
            let original_register = match self.control.get(variable) {
                None => {
                    // The variable was declared inside the if so it can't be accessed outside and we don't care.
                    // TODO: check if that's true if you do `if (1) long x = 10;`
                    continue;
                }
                Some(ssa) => ssa,
            };
            let other_register = match mutated_in_else.remove(&variable) {
                // If the other path did not mutate the value, use the one from before.
                None => original_register,
                // If the both paths mutated the value, we don't care what it was before we branched.
                Some(else_register) => else_register,
            };

            let new_register = self.func_mut().next_var();
            self.func_mut().push(
                block,
                Op::Phi {
                    dest: new_register,
                    a: (if_true, then_register),
                    b: (if_false, other_register),
                },
            );
            moved_registers.push((variable, new_register));

            let name_a = self.func_mut().name(&then_register);
            let name_b = self.func_mut().name(&other_register);
            self.func_mut()
                .set_debug(new_register, || format!("phi__{}__{}__", name_a, name_b));
        }
        // Any that were mutated in both branches were removed in the previous loop.
        // So we know any remaining will be using the original register as the true branch.
        for (variable, else_register) in mutated_in_else {
            assert!(moved_registers.iter().any(|check| check.0 == variable));

            let original_register = self.control.get(variable).unwrap();
            let new_register = self.func_mut().next_var();
            self.func_mut().push(
                block,
                Op::Phi {
                    dest: new_register,
                    a: (if_true, original_register),
                    b: (if_false, else_register),
                },
            );
            moved_registers.push((variable, new_register));

            let name_a = self.func_mut().name(&original_register);
            let name_b = self.func_mut().name(&else_register);
            self.func_mut()
                .set_debug(new_register, || format!("phi__{}__{}__", name_a, name_b));
        }
        // Now that we've updated everything, throw away the registers from before the branching.
        for (variable, register) in moved_registers {
            self.control.set(variable, register);
        }
    }

    #[must_use]
    fn emit_expr(&mut self, expr: &'ast Expr, block: Label) -> Option<Ssa> {
        match expr {
            Expr::Binary { left, op, right } => {
                if *op == BinaryOp::Assign {
                    self.emit_assignment(left, right, block)
                } else {
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
            }
            Expr::Literal { value } => match value {
                LiteralValue::Number { value } => {
                    Some(self.func_mut().constant_int(block, *value as u64))
                }
            },
            Expr::GetVar { name } => {
                let variable = self.resolve_name(name);
                let register = self
                    .control
                    .get(variable)
                    .unwrap_or_else(|| panic!("GetVar undeclared {}", name));
                Some(register)
            }
            _ => todo!(),
        }
    }

    fn emit_assignment(
        &mut self,
        lvalue: &'ast Expr,
        rvalue: &'ast Expr,
        block: Label,
    ) -> Option<Ssa> {
        // TODO: eval order is probably specified. like can you do a function call to get a pointer on the left?
        let value = self
            .emit_expr(rvalue, block)
            .expect("Can't assign to void.");
        match lvalue {
            Expr::GetVar { name } => {
                let this_variable = self.resolve_name(name);
                self.func_mut()
                    .set_debug(value, || format!("{}_{}", name, this_variable.1 .0));
                self.control.set(this_variable, value);
                Some(value)
            }
            _ => todo!(),
        }
    }

    fn func_mut(&mut self) -> &mut ir::Function {
        self.func.as_mut().unwrap()
    }

    fn push_scope(&mut self) {
        self.scopes.push(LexScope(self.total_scope_count));
        self.total_scope_count += 1;
    }

    fn pop_scope(&mut self) {
        self.scopes.pop().expect("You should always be in a scope.");
    }

    fn current_scope(&self) -> LexScope {
        *self.scopes.last().unwrap()
    }

    fn resolve_name(&self, name: &'ast str) -> Var<'ast> {
        for scope in self.scopes.iter().rev() {
            let var = Var(name, *scope);
            if self.control.get(var).is_some() {
                return var;
            }
        }
        panic!("Cannot access undefined variable {}", name);
    }
}

impl<'ast> ControlFlowStack<'ast> {
    fn push(&mut self) {
        self.0.push(HashMap::new());
    }

    // You need to use this to update other variables and emit phi nodes
    #[must_use]
    fn pop(&mut self) -> HashMap<Var<'ast>, Ssa> {
        self.0.pop().expect("Popped empty MutStack.")
    }

    fn set(&mut self, variable: Var<'ast>, new_register: Ssa) {
        match self.0.last_mut() {
            None => {
                // Nobody pushed a frame so we don't care about tracking yet.
            }
            Some(data) => {
                data.insert(variable, new_register);
            }
        }
    }

    fn get(&self, variable: Var) -> Option<Ssa> {
        for scope in self.0.iter().rev() {
            if let Some(register) = scope.get(&variable) {
                return Some(*register);
            }
        }
        None
    }
}
