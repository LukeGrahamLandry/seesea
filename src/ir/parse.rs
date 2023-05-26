//! AST -> IR

use crate::ast;
use crate::ast::{BinaryOp, Expr, LiteralValue, Stmt, UnaryOp};
use crate::ir;
use crate::ir::allocs::needs_stack_address;
use crate::ir::debug::IrDebugInfo;
use crate::ir::flow_stack::{ControlFlowStack, FlowStackFrame, Var};
use crate::ir::{Label, Op, Ssa};

#[derive(Default)]
struct AstParser<'ast> {
    ir: ir::Module,
    func: Option<ir::Function>, // needs to become a stack if i allow parsing nested functions i guess?
    control: ControlFlowStack<'ast>,
    debug: IrDebugInfo<'ast>,
    root_node: Option<&'ast Stmt>,
}

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
        self.func = Some(ir::Function::new(input.signature.clone()));
        let mut entry = self.func_mut().new_block();
        self.control.push_flow_frame(entry);

        self.control.push_scope();
        let arguments = input
            .signature
            .param_types
            .iter()
            .zip(input.signature.param_names.iter());
        for (_ty, name) in arguments {
            let variable = Var(name.as_str(), self.control.current_scope());
            let register = self.func_mut().next_var();
            self.func_mut()
                .set_debug(register, || format!("{}_arg", name));
            self.control.set(variable, register);
            self.func_mut().arg_registers.push(register);
        }
        self.control.push_scope();
        self.root_node = Some(&input.body);
        self.emit_statement(&input.body, &mut entry);
        self.control.pop_scope();
        self.control.pop_scope();

        println!("{:?}", self.func_mut());
        self.func_mut().assert_valid();
        self.ir.functions.push(self.func.take().unwrap());
        let _ = self.control.pop_flow_frame();
        self.control.clear();

        println!("------------");
    }

    fn emit_statement(&mut self, stmt: &'ast Stmt, block: &mut Label) {
        match stmt {
            Stmt::Block { body, .. } => {
                // Lexical blocks in the source don't directly correspond to the IR blocks used for control flow.
                // Rather, they affect the variable name resolution stack.
                self.control.push_scope();
                for stmt in body {
                    self.emit_statement(stmt, block);
                }
                self.control.pop_scope();
            }
            Stmt::Expression { expr } => {
                let _ = self.emit_expr(expr, *block);
            }
            Stmt::DeclareVar { name, value, .. } => {
                // TODO: track types or maybe the ir should handle on the ssa?
                let variable = Var(name.as_str(), self.control.current_scope());

                if needs_stack_address(self.root_node.unwrap(), variable) {
                    // Somebody wants to take the address of this variable later,
                    // so we need to make sure it gets allocated on the stack and not kept in a register.
                    self.control.set_stack_alloc(variable);
                } else {
                    // Nobody cares where this goes so it can be a register if the backend wants.
                    let register = self
                        .emit_expr(value, *block)
                        .expect("Variable type cannot be void.");
                    self.control.set(variable, register);
                    self.func_mut()
                        .set_debug(register, || format!("{}_{}", name, variable.1 .0));
                }
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

    fn parse_branch(&mut self, branch_body: &'ast Stmt) -> (Label, FlowStackFrame<'ast>, bool) {
        let branch_block = self.func_mut().new_block();
        self.control.push_flow_frame(branch_block);

        let mut working_block_pointer = branch_block;
        self.emit_statement(branch_body, &mut working_block_pointer);

        let branch_returned = self.func_mut().ends_with_jump(branch_block);
        let mutated_in_branch = self.control.pop_flow_frame();
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
        mutated_in_other_branch: &FlowStackFrame<'ast>,
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
        mutated_in_branch: &FlowStackFrame<'ast>,
    ) {
        // TODO: assert that self.control is looking at the parent_block
        let mut moved_registers = vec![];
        for (variable, branch_register) in &mutated_in_branch.mutations {
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
        (if_true, mutated_in_then): (Label, FlowStackFrame<'ast>),
        (if_false, mut mutated_in_else): (Label, FlowStackFrame<'ast>),
        block: Label,
    ) {
        let mut moved_registers = vec![];
        // We have the set of Vars whose register changed in one of the branches.
        // Now that we've rejoined, future code in this block needs to access different registers depending how it got here.
        for (variable, then_register) in mutated_in_then.mutations {
            let original_register = match self.control.get(variable) {
                None => {
                    // The variable was declared inside the if so it can't be accessed outside and we don't care.
                    // TODO: check if that's true if you do `if (1) long x = 10;`
                    continue;
                }
                Some(ssa) => ssa,
            };
            let other_register = match mutated_in_else.mutations.remove(&variable) {
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
        for (variable, else_register) in mutated_in_else.mutations {
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
                let variable = self
                    .control
                    .resolve_name(name)
                    .unwrap_or_else(|| panic!("Cannot access undefined variable {}", name));
                let register = self
                    .control
                    .get(variable)
                    .unwrap_or_else(|| panic!("GetVar undeclared {}", name));
                Some(register)
            }
            Expr::Call { func, args } => {
                let name = match func.as_ref() {
                    Expr::GetVar { name } => name,
                    _ => todo!(),
                };
                let arg_registers = args
                    .iter()
                    .map(|e| {
                        self.emit_expr(e, block)
                            .expect("Passed function arg cannot be void.")
                    })
                    .collect();
                let return_value_dest = self.func_mut().next_var();
                self.func_mut().push(
                    block,
                    Op::Call {
                        func_name: name.clone(), // TODO: directly reference the func def node since we know we'll already hve it from headeres
                        args: arg_registers,
                        return_value_dest,
                    },
                );
                // TODO: return none if the func is void
                Some(return_value_dest)
            }
            Expr::Unary { value, op } => match op {
                UnaryOp::AddressOf => {
                    todo!()
                }
                _ => todo!(),
            },
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
                let this_variable = self
                    .control
                    .resolve_name(name)
                    .expect("todo: support stack alloc");
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
}
