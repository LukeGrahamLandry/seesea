//! AST -> IR

use crate::ast;
use crate::ast::{BinaryOp, CType, Expr, LiteralValue, Stmt, UnaryOp, ValueType};
use crate::ir;
use crate::ir::allocs::collect_stack_allocs;
use crate::ir::debug::IrDebugInfo;
use crate::ir::flow_stack::{patch_reads, ControlFlowStack, FlowStackFrame, Var};
use crate::ir::{Label, Op, Ssa};
use std::collections::{HashMap, HashSet};
use std::mem;
use std::ops::Deref;

struct AstParser<'ast> {
    ast: &'ast ast::Module,
    ir: ir::Module,
    func: Option<ir::Function>, // needs to become a stack if i allow parsing nested functions i guess?
    control: ControlFlowStack<'ast>,
    debug: IrDebugInfo<'ast>,
    root_node: Option<&'ast Stmt>,

    /// variable -> register holding a pointer to that variable's value.
    stack_addresses: HashMap<Var<'ast>, Ssa>,
    /// Collections of which variables require a stable stack address.
    needs_stack_address: HashSet<Var<'ast>>,
}

impl From<ast::Module> for ir::Module {
    fn from(value: ast::Module) -> Self {
        parse_ast(&value).0
    }
}

pub fn parse_ast<'ast>(program: &'ast ast::Module) -> (ir::Module, IrDebugInfo<'ast>) {
    let mut parser: AstParser<'ast> = AstParser::new(program);

    for func in program.functions.iter() {
        parser.parse_function(func)
    }

    assert!(parser.func.is_none());
    parser.ir.structs = program.structs.clone();
    (parser.ir, parser.debug)
}

// TODO: can i make the special casing around memory addresses less annoying with an lvalue/rvalue abstraction?
impl<'ast> AstParser<'ast> {
    fn new(ast: &ast::Module) -> AstParser {
        AstParser {
            ast,
            ir: Default::default(),
            func: None,
            control: Default::default(),
            debug: Default::default(),
            root_node: None,
            stack_addresses: Default::default(),
            needs_stack_address: Default::default(),
        }
    }

    fn parse_function(&mut self, input: &'ast ast::Function) {
        // TODO: separate these out into an Option
        assert!(
            self.func.is_none()
                && self.needs_stack_address.is_empty()
                && self.stack_addresses.is_empty()
        );
        self.func = Some(ir::Function::new(input.signature.clone()));
        let mut entry = self.func_mut().new_block();
        self.control.push_flow_frame(entry);

        self.control.push_scope();
        let arguments = input
            .signature
            .param_types
            .iter()
            .zip(input.signature.param_names.iter());
        for (ty, name) in arguments {
            let variable = Var(name.as_str(), self.control.current_scope());
            let register = self.make_ssa(*ty);
            self.func_mut()
                .set_debug(register, || format!("{}_arg", name));
            self.control.set(variable, register);
            self.func_mut().arg_registers.push(register);
        }
        self.control.push_scope();
        self.root_node = Some(&input.body);
        collect_stack_allocs(&input.body, &mut self.needs_stack_address);
        self.emit_statement(&input.body, &mut entry);
        self.control.pop_scope();
        self.control.pop_scope();

        let mut empty = HashMap::new();
        mem::swap(&mut self.control.register_types, &mut empty);
        self.func_mut().register_types = empty;
        println!("{:?}", self.func_mut());
        self.func_mut().assert_valid();
        self.ir.functions.push(self.func.take().unwrap());
        let _ = self.control.pop_flow_frame();
        self.control.clear();
        self.stack_addresses.clear();
        self.needs_stack_address.clear();
        assert_eq!(self.stack_addresses.len(), self.needs_stack_address.len());

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
            Stmt::DeclareVar { name, value, kind } => {
                self.declare_variable(name, value, kind, *block)
            }
            Stmt::Return { value } => match value {
                None => {
                    self.func_mut().push(*block, Op::Return { value: None });
                }
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
            Stmt::While { condition, body } => {
                self.emit_while_loop(block, condition, body);
            }
        }
    }

    fn declare_variable(&mut self, name: &'ast str, value: &'ast Expr, kind: &CType, block: Label) {
        let variable = Var(name, self.control.current_scope());

        if kind.is_struct() {
            match value {
                Expr::Default(ty) => assert_eq!(ty, kind),
                _ => todo!("Struct that is not init to default."),
            }
            println!("Struct allocation for {:?}", variable);
            let ptr_register = self.func_mut().next_var();
            self.control.set_stack_alloc(variable, kind, ptr_register);
            self.func_mut().push(
                block,
                Op::StackAlloc {
                    dest: ptr_register,
                    ty: *kind,
                    count: 1,
                },
            );
            self.stack_addresses.insert(variable, ptr_register);
            return;
        }

        let value_register = self
            .emit_expr(value, block)
            .expect("Variable type cannot be void.");
        let value_type = self.type_of(value_register);
        assert_eq!(
            value_type, *kind,
            "{:?} expected {:?} but found {:?}",
            variable, kind, value_type
        );

        if self.needs_stack_address.contains(&variable) {
            println!("Stack allocation for {:?}", variable);
            // Somebody wants to take the address of this variable later,
            // so we need to make sure it gets allocated on the stack and not kept in a register.
            let ptr_register = self.func_mut().next_var();
            self.control.set_stack_alloc(variable, kind, ptr_register);
            self.func_mut().push(
                block,
                Op::StackAlloc {
                    dest: ptr_register,
                    ty: *kind,
                    count: 1,
                },
            );
            self.func_mut().push(
                block,
                Op::StoreToPtr {
                    addr: ptr_register,
                    value_source: value_register,
                },
            );
            self.stack_addresses.insert(variable, ptr_register);
        } else {
            println!("No stack allocation for {:?}", variable);
            // Nobody cares where this goes so it can stay a register if the backend wants.
            self.control.set(variable, value_register);
            self.func_mut()
                .set_debug(value_register, || format!("{}_{}", name, variable.1 .0));
        }
    }

    fn emit_function_call(
        &mut self,
        block: Label,
        func_expr: &'ast Expr,
        args: &'ast [Expr],
    ) -> Option<Ssa> {
        let name = match func_expr {
            Expr::GetVar { name } => name,
            _ => todo!("Support function pointers."),
        };

        let signature = &self
            .ast
            .get_func(name)
            .unwrap_or_else(|| panic!("Call undeclared function {}", name))
            .signature;

        let mut arg_registers = vec![];
        for (i, arg) in args.iter().enumerate() {
            let arg_ssa = self
                .emit_expr(arg, block)
                .expect("Passed function arg cannot be void.");

            let found = self.control.ssa_type(arg_ssa);
            let expected = &signature.param_types[i];
            assert_eq!(
                expected, found,
                "{} param {} expected {:?} but found {:?}",
                name, i, expected, found
            );
            arg_registers.push(arg_ssa);
        }

        let return_value_dest = self.make_ssa(signature.return_type);
        self.func_mut().push(
            block,
            Op::Call {
                // TODO: directly reference the func def node since we know we'll already have it from headers
                //       but then does the IR need the lifetime of the ast?
                func_name: name.clone(),
                args: arg_registers,
                return_value_dest,
            },
        );
        // TODO: return none if the func is void
        Some(return_value_dest)
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
        let (then_block_start, then_block_end, mutated_in_then, then_block_returned) =
            self.parse_branch(then_body);
        let (else_block_start, else_block_end, mutated_in_else, else_block_returned) =
            self.parse_branch(else_body);

        self.func_mut().push(
            *block,
            Op::Jump {
                condition,
                if_true: then_block_start,
                if_false: else_block_start,
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
            then_block_end,
            else_block_end,
            next_block,
            then_block_returned,
            &mutated_in_else,
        );
        self.terminate_branch(
            parent_block,
            else_block_end,
            then_block_end,
            next_block,
            else_block_returned,
            &mutated_in_then,
        );

        let neither_returned = !(then_block_returned || else_block_returned);
        if neither_returned {
            self.emit_phi(
                (then_block_end, mutated_in_then),
                (else_block_end, mutated_in_else),
                next_block,
            );
        }

        // Reassign the current block pointer. The rest of the function is emitted in the new one.
        *block = next_block;
    }

    // TODO: this should return a struct
    fn parse_branch(
        &mut self,
        branch_body: &'ast Stmt,
    ) -> (Label, Label, FlowStackFrame<'ast>, bool) {
        let branch_block = self.func_mut().new_block();
        self.control.push_flow_frame(branch_block);

        let mut working_block_pointer = branch_block;
        self.emit_statement(branch_body, &mut working_block_pointer);

        let branch_returned = self.func_mut().ends_with_jump(working_block_pointer);
        let mutated_in_branch = self.control.pop_flow_frame();
        (
            branch_block,
            working_block_pointer,
            mutated_in_branch,
            branch_returned,
        )
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

    /// Returns a map of original Ssa (from before mutation) to new Ssa (of phi node) for back patching loops.
    fn emit_phi_parent_or_single_branch(
        &mut self,
        parent_block: Label,
        branch_block: Label,
        new_block: Label,
        mutated_in_branch: &FlowStackFrame<'ast>,
    ) -> HashMap<Ssa, Ssa> {
        // TODO: assert that self.control is looking at the parent_block?
        let mut moved_registers = vec![];
        for (variable, branch_register) in &mutated_in_branch.mutations {
            let parent_register = match self.control.get_if_in_scope(*variable) {
                None => continue,
                Some(ssa) => ssa,
            };
            assert_eq!(
                self.type_of(parent_register),
                self.type_of(*branch_register)
            );
            let new_register = self.make_ssa(self.type_of(parent_register));
            self.func_mut().push(
                new_block,
                Op::Phi {
                    dest: new_register,
                    a: (parent_block, parent_register),
                    b: (branch_block, *branch_register),
                },
            );
            moved_registers.push((variable, new_register));

            self.set_phi_debug(new_register, parent_register, *branch_register);
        }

        let mut original_to_phi = HashMap::new();

        // Now that we've updated everything, throw away the registers from before the branching.
        for (variable, register) in moved_registers {
            let old_register = self.control.get(*variable).unwrap();
            original_to_phi.insert(old_register, register);
            self.control.set(*variable, register);
        }

        original_to_phi
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
            let original_register = match self.control.get_if_in_scope(variable) {
                None => continue,
                Some(ssa) => ssa,
            };
            let other_register = match mutated_in_else.mutations.remove(&variable) {
                // If the other path did not mutate the value, use the one from before.
                None => original_register,
                // If the both paths mutated the value, we don't care what it was before we branched.
                // TODO: make sure this is true when back patching with loops (but currently they don't call this method)
                Some(else_register) => else_register,
            };

            assert_eq!(self.type_of(then_register), self.type_of(other_register));
            let new_register = self.make_ssa(self.type_of(then_register));
            self.func_mut().push(
                block,
                Op::Phi {
                    dest: new_register,
                    a: (if_true, then_register),
                    b: (if_false, other_register),
                },
            );

            moved_registers.push((variable, new_register));

            self.set_phi_debug(new_register, original_register, other_register);
        }

        for (variable, else_register) in mutated_in_else.mutations {
            // Any that were mutated in both branches were removed in the previous loop.
            // So we know any remaining will be using the original register as the true branch.
            assert!(!moved_registers.iter().any(|check| check.0 == variable));

            let original_register = match self.control.get_if_in_scope(variable) {
                None => continue,
                Some(ssa) => ssa,
            };
            assert_eq!(self.type_of(else_register), self.type_of(original_register));
            let new_register = self.make_ssa(self.type_of(original_register));

            self.func_mut().push(
                block,
                Op::Phi {
                    dest: new_register,
                    a: (if_true, original_register),
                    b: (if_false, else_register),
                },
            );
            moved_registers.push((variable, new_register));

            self.set_phi_debug(new_register, original_register, else_register);
        }
        // Now that we've updated everything, throw away the registers from before the branching.
        for (variable, register) in moved_registers {
            self.control.set(variable, register);
        }
    }

    fn set_phi_debug(&mut self, new_register: Ssa, a: Ssa, b: Ssa) {
        let name_a = self.func_mut().debug_str(&a);
        let name_b = self.func_mut().debug_str(&a);
        assert_eq!(
            name_a, name_b,
            "Both phi branches should refer to the same source variable"
        );
        self.func_mut().set_debug(new_register, || name_a.unwrap());
    }

    // parent > setup > condition
    //                           body_block > end_of_body_block <setup
    //                           exit_block
    fn emit_while_loop(&mut self, block: &mut Label, condition: &'ast Expr, body: &'ast Stmt) {
        let parent_block = *block;
        let setup_block = self.func_mut().new_block();
        let condition_block = self.func_mut().new_block();
        self.func_mut()
            .push(parent_block, Op::AlwaysJump(setup_block));

        self.control.push_flow_frame(condition_block);
        let condition_register = self
            .emit_expr(condition, condition_block)
            .expect("Loop condition can't be void");
        let mutated_in_condition = self.control.pop_flow_frame();

        let start_body_block = self.func_mut().new_block();
        let mut end_of_body_block = start_body_block;

        self.control.push_flow_frame(end_of_body_block);
        self.emit_statement(body, &mut end_of_body_block);
        let mutated_in_body = self.control.pop_flow_frame();

        // todo assert no overlap mutated_in_condition and mutated_in_body

        let changes = self.emit_phi_parent_or_single_branch(
            parent_block,
            end_of_body_block,
            setup_block,
            &mutated_in_body,
        );

        // TODO: what happens if condition mutates but body doesn't run
        // Insert phi nodes in the setup for any mutations in the condition (to use either initial or mutated).
        let condition_changes = self.emit_phi_parent_or_single_branch(
            parent_block,
            end_of_body_block,
            setup_block,
            &mutated_in_condition,
        );

        // The condition always runs so mutations there don't need phi nodes in the exit
        // but since we removed them from the flow stack, we need to put them back.
        for (var, reg) in mutated_in_condition.mutations {
            self.control.set(var, reg);
        }

        let exit_block = self.func_mut().new_block();

        self.func_mut()
            .push(setup_block, Op::AlwaysJump(condition_block));
        self.func_mut()
            .push(end_of_body_block, Op::AlwaysJump(setup_block));
        self.func_mut().push(
            condition_block,
            Op::Jump {
                condition: condition_register,
                if_true: start_body_block,
                if_false: exit_block,
            },
        );

        self.patch_below(condition_block, &condition_changes);
        self.patch_below(condition_block, &changes);

        *block = exit_block;
    }

    /// For all blocks including and after first_block,
    /// replace any reads of register <key> with register <value>.
    /// This is used for making loop bodies and conditions reference phi nodes that didn't exist
    /// until after the whole loop was parsed.
    fn patch_below(&mut self, first_block: Label, changes: &HashMap<Ssa, Ssa>) {
        let start = first_block.index();
        let count = self.func_mut().blocks.len();
        for index in start..count {
            let block = &mut self.func_mut().blocks[index];
            for op in block {
                patch_reads(op, changes);
            }
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
                    let ty = self.control.ssa_type(a);
                    assert_eq!(ty, self.control.ssa_type(b));
                    let dest = self.make_ssa(*ty);
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
                    let dest = self.make_ssa(CType::int());
                    self.func_mut()
                        .set_debug(dest, || format!("const_{}", value));
                    self.func_mut().push(
                        block,
                        Op::ConstInt {
                            dest,
                            value: *value as u64,
                        },
                    );
                    Some(dest)
                }
            },
            Expr::GetVar { .. } => {
                let lvalue = self.parse_lvalue(expr, block);

                let register = match lvalue {
                    Lvalue::RegisterVar(var) => self.control.get(var).unwrap(),
                    Lvalue::DerefPtr(addr) => {
                        let value_type = self.type_of(addr);
                        assert!(value_type.is_basic()); // TODO
                        let value_dest = self.make_ssa(value_type.deref_type());
                        self.func_mut()
                            .push(block, Op::LoadFromPtr { value_dest, addr });
                        value_dest
                    }
                };

                Some(register)
            }
            Expr::Call { func, args } => self.emit_function_call(block, func, args),
            Expr::Unary { value, op } => match op {
                UnaryOp::AddressOf => {
                    let lvalue = self.parse_lvalue(value, block);
                    Some(lvalue.get_addr())
                }
                UnaryOp::Deref => {
                    let addr = self
                        .emit_expr(value, block)
                        .expect("Cannot dereference void.");
                    let register = self.make_ssa(self.type_of(addr).deref_type());
                    self.func_mut().push(
                        block,
                        Op::LoadFromPtr {
                            value_dest: register,
                            addr,
                        },
                    );
                    Some(register)
                }
                _ => todo!(),
            },
            Expr::GetField { .. } => {
                let field_ptr = self.parse_lvalue(expr, block).get_addr();
                let register = self.make_ssa(self.type_of(field_ptr).deref_type());
                self.func_mut().push(
                    block,
                    Op::LoadFromPtr {
                        value_dest: register,
                        addr: field_ptr,
                    },
                );
                Some(register)
            }
            Expr::Default(kind) => {
                assert!(!kind.is_struct());
                let dest = self.make_ssa(*kind);
                self.func_mut().push(block, Op::ConstInt { dest, value: 0 });
                Some(dest)
            }
        }
    }

    fn emit_assignment(
        &mut self,
        lvalue: &'ast Expr,
        rvalue: &'ast Expr,
        block: Label,
    ) -> Option<Ssa> {
        let target = self.parse_lvalue(lvalue, block);
        let value_source = self
            .emit_expr(rvalue, block)
            .expect("Can't assign to void.");

        match target {
            Lvalue::RegisterVar(this_variable) => {
                self.func_mut().set_debug(value_source, || {
                    format!("{}_{}", this_variable.0, this_variable.1 .0)
                });
                self.control.set(this_variable, value_source);
            }
            Lvalue::DerefPtr(addr) => {
                assert!(self
                    .control
                    .ssa_type(addr)
                    .is_pointer_to(self.control.ssa_type(value_source)));
                self.func_mut()
                    .push(block, Op::StoreToPtr { addr, value_source });
            }
        }

        Some(value_source)
    }

    fn type_of(&self, ssa: Ssa) -> CType {
        *self.control.ssa_type(ssa)
    }

    // Try to use this instead of directly calling next_var because it forces you to set the type of the register.
    // The ir validation will catch it if you forget.
    fn make_ssa(&mut self, ty: CType) -> Ssa {
        let ssa = self.func_mut().next_var();
        self.control.register_types.insert(ssa, ty);
        ssa
    }

    fn func_mut(&mut self) -> &mut ir::Function {
        self.func.as_mut().unwrap()
    }

    /// The type of thing that is stored in the Lvalue (so really the Lvalue is a pointer to this)
    fn value_type(&self, value: &Lvalue) -> CType {
        match value {
            Lvalue::RegisterVar(var) => self.type_of(self.control.get(*var).unwrap()),
            Lvalue::DerefPtr(addr) => self.type_of(*addr).deref_type(),
        }
    }

    /// Get the location in memory that the expr refers to (don't dereference it to extract the value yet).
    fn parse_lvalue(&mut self, expr: &'ast Expr, block: Label) -> Lvalue<'ast> {
        match expr {
            Expr::GetVar { name } => {
                let this_variable = self
                    .control
                    .resolve_name(name)
                    .unwrap_or_else(|| panic!("Undeclared variable {:?}", name));
                if self.control.is_stack_alloc(this_variable) {
                    let addr = *self
                        .stack_addresses
                        .get(&this_variable)
                        .expect("Expected stack variable.");
                    let addr_type = self.control.ssa_type(addr);
                    let var_type = self.control.var_type(this_variable);
                    assert!(addr_type.is_pointer_to(var_type));
                    Lvalue::DerefPtr(addr)
                } else {
                    let val = self.control.get(this_variable).unwrap();
                    Lvalue::RegisterVar(this_variable)
                }
            }
            Expr::Unary { value, op } => {
                assert_eq!(*op, UnaryOp::Deref);
                let addr = self.emit_expr(value, block).unwrap();
                Lvalue::DerefPtr(addr)
            }
            Expr::GetField { object, name } => {
                let the_struct = self.parse_lvalue(object, block).get_addr();
                let ty = self.type_of(the_struct);
                assert_eq!(ty.depth, 1);
                if let ValueType::Struct(struct_name) = ty.ty {
                    let struct_def = self.ast.get_struct(struct_name).unwrap();
                    let field_addr_dest = self.make_ssa(struct_def.field_type(name).ref_type());
                    self.func_mut().push(
                        block,
                        Op::GetFieldAddr {
                            dest: field_addr_dest,
                            object_addr: the_struct,
                            field_index: struct_def.field_index(name),
                        },
                    );
                    Lvalue::DerefPtr(field_addr_dest)
                } else {
                    panic!("Tried to access field {} on non-struct {:?}", name, object)
                }
            }
            _ => unreachable!(),
        }
    }
}

/// A location in memory.
enum Lvalue<'ast> {
    RegisterVar(Var<'ast>), // value
    DerefPtr(Ssa),          // addr
}

impl<'ast> Lvalue<'ast> {
    fn get_addr(&self) -> Ssa {
        match self {
            Lvalue::RegisterVar(_) => unreachable!("Cannot get address of temporary value"),
            Lvalue::DerefPtr(addr) => *addr,
        }
    }
}
