//! AST -> IR
/// This stage shouldn't need to worry about type checking because it should only receive a well formed resolved AST.
use crate::ast::{
    AnyFunction, AnyModule, AnyStmt, BinaryOp, CType, FuncSignature, LiteralValue, MetaExpr,
    OpDebugInfo, ValueType,
};
use crate::ir::flow_stack::{patch_reads, ControlFlowStack, FlowStackFrame};
use crate::ir::{Label, Op, Ssa};
use crate::{ir, log};

use crate::resolve::parse::Resolver;
use crate::resolve::{FuncSource, Operation, ResolvedExpr, VariableRef};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::mem;

type AstStmt = AnyStmt<ResolvedExpr>;
type AstFunction = AnyFunction<ResolvedExpr>;
type AstModule = AnyModule<AstFunction>;

struct AstParser<'ast> {
    ir: ir::Module,
    func: Option<ir::Function>, // needs to become a stack if i allow parsing nested functions i guess?
    control: ControlFlowStack,
    root_node: Option<&'ast AstStmt>,

    /// variable -> register holding a pointer to that variable's value.
    stack_addresses: HashMap<VariableRef, Ssa>,
}

impl From<AnyModule<AnyFunction<MetaExpr>>> for ir::Module {
    fn from(mut value: AnyModule<AnyFunction<MetaExpr>>) -> Self {
        value.calc_struct_padding();
        let mut resolver = Resolver::new(&value);
        resolver.all();
        parse_ast(&resolver.resolved)
    }
}

pub fn parse_ast<'ast>(program: &'ast AstModule) -> ir::Module {
    log!("{:?}", program);
    let mut parser: AstParser<'ast> = AstParser::new(program);

    for func in program.forward_declarations.clone() {
        parser.ir.forward_declarations.push(func);
    }

    for func in program.functions.iter() {
        parser.parse_function(func)
    }

    assert!(parser.func.is_none());
    parser.ir.structs = program.structs.clone();
    parser.ir
}

impl<'ast> AstParser<'ast> {
    fn new(ast: &'ast AstModule) -> AstParser {
        AstParser {
            ir: ir::Module::new(ast.name.clone()),
            func: None,
            control: Default::default(),
            root_node: None,
            stack_addresses: Default::default(),
        }
    }

    fn parse_function(&mut self, input: &'ast AstFunction) {
        // TODO: separate these out into an Option
        assert!(self.func.is_none() && self.stack_addresses.is_empty());
        self.func = Some(ir::Function::new(input.signature.clone()));
        let mut entry = self.func_mut().new_block();
        self.control.push_flow_frame(entry);

        self.control.push_scope();
        for variable in input.arg_vars.as_ref().unwrap().iter() {
            let register = self.make_ssa(&variable.ty);
            assert!(!variable.needs_stack_alloc.get());
            self.func_mut()
                .set_debug(register, || format!("{}_arg", variable.name));
            self.control.set(variable.clone(), register);
            self.func_mut().arg_registers.push(register);
        }
        self.control.push_scope();
        self.root_node = Some(&input.body);
        self.emit_statement(&input.body, &mut entry);
        self.control.pop_scope();
        self.control.pop_scope();

        let mut empty = HashMap::new();
        mem::swap(&mut self.control.register_types, &mut empty);
        self.func_mut().register_types = empty;
        log!("{:?}", self.func_mut());
        self.func_mut().finish();
        self.ir.functions.push(self.func.take().unwrap());
        let _ = self.control.pop_flow_frame();
        self.control.clear();
        self.stack_addresses.clear();

        log!("------------");
    }

    fn emit_statement(&mut self, stmt: &'ast AstStmt, block: &mut Label) {
        match stmt {
            AstStmt::Block { body, .. } => {
                // Lexical blocks in the source don't directly correspond to the IR blocks used for control flow.
                // Rather, they affect the variable name resolution stack.
                self.control.push_scope();
                for stmt in body {
                    self.emit_statement(stmt, block);
                }
                self.control.pop_scope();
            }
            AstStmt::Expression { expr } => {
                let _ = self.emit_expr_voidable(expr, *block);
            }
            AstStmt::DeclareVar {
                value, variable, ..
            } => self.declare_variable(variable.as_ref().unwrap().clone(), value, *block),
            AstStmt::Return { value } => match value {
                None => {
                    self.func_mut().push_no_debug(*block, Op::Return(None));
                }
                Some(value) => {
                    let result = self.emit_expr(value, *block);
                    self.func_mut()
                        .push(*block, Op::Return(Some(result)), value.info());
                }
            },
            AstStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                self.emit_if_stmt(block, condition, then_body, else_body);
            }
            AstStmt::While { condition, body } => {
                self.emit_while_loop(block, condition, body);
            }
            AstStmt::For { .. } => {
                todo!()
            }
            AstStmt::Nothing => {
                // TODO: make sure its fine if this is the only statement in a block we want to jump to
            }
            AstStmt::Intrinsic(name, _, _) => {
                unreachable!("{:?} should be translated in resolve pass.", name)
            }
        }
    }

    fn declare_variable(&mut self, variable: VariableRef, value: &'ast ResolvedExpr, block: Label) {
        assert_eq!(variable.ty, value.ty);
        if variable.ty.is_struct() {
            assert!(matches!(
                value.as_ref(),
                Operation::Literal(LiteralValue::UninitStruct)
            ));
            let ptr_register = self.func_mut().next_var();
            self.control.set_stack_alloc(variable.clone(), ptr_register);
            self.func_mut().push(
                block,
                Op::StackAlloc {
                    dest: ptr_register,
                    ty: variable.ty.clone(),
                    count: 1,
                },
                value.info(),
            );
            self.stack_addresses.insert(variable, ptr_register);
            return;
        }

        let value_register = self.emit_expr(value, block);
        assert_eq!(self.type_of(value_register), variable.ty);

        if variable.needs_stack_alloc.get() {
            // Somebody wants to take the address of this variable later,
            // so we need to make sure it gets allocated on the stack and not kept in a register.
            let ptr_register = self.func_mut().next_var();
            self.control.set_stack_alloc(variable.clone(), ptr_register);
            self.func_mut().required_stack_bytes += self.ir.size_of(&value.ty);
            self.func_mut().push(
                block,
                Op::StackAlloc {
                    dest: ptr_register,
                    ty: variable.ty.clone(),
                    count: 1,
                },
                value.info(),
            );
            self.func_mut().push(
                block,
                Op::StoreToPtr {
                    addr: ptr_register,
                    value_source: value_register,
                },
                value.info(),
            );
            self.stack_addresses.insert(variable, ptr_register);
        } else {
            // Nobody cares where this goes so it can stay a register if the backend wants.
            self.control.set(variable.clone(), value_register);
            self.func_mut().set_debug(value_register, || {
                format!("{}_{}", variable.name, variable.scope.0)
            });
        }
    }

    fn emit_function_call(
        &mut self,
        block: Label,
        signature: &'ast FuncSignature,
        func_src: &'ast FuncSource,
        args: &'ast [ResolvedExpr],
        debug: OpDebugInfo,
    ) -> Option<Ssa> {
        assert!(matches!(
            func_src,
            FuncSource::Internal | FuncSource::External
        ));
        let arg_registers = args.iter().map(|arg| self.emit_expr(arg, block)).collect();
        let return_value_dest = if signature.return_type.is_raw_void() {
            None
        } else {
            Some(self.make_ssa(&signature.return_type))
        };

        self.func_mut().push(
            block,
            Op::Call {
                // TODO: directly reference the func def node since we know we'll already have it from headers
                //       but then does the IR need the lifetime of the ast?
                func_name: signature.name.clone(),
                args: arg_registers,
                return_value_dest,
                kind: func_src.clone(),
            },
            debug,
        );
        return_value_dest
    }

    // TODO: this whole passing around a mutable block pointer is scary.
    //         it means you can never rely on being in the same block as you were before parsing a statement.
    //         but that should be fine because its where you would be after flowing through that statement
    fn emit_if_stmt(
        &mut self,
        block: &mut Label,
        condition_expr: &'ast ResolvedExpr,
        then_body: &'ast AstStmt,
        else_body: &'ast AstStmt,
    ) {
        let parent_block = *block;
        let condition = self.emit_expr(condition_expr, *block);

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
            condition_expr.info(),
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
    fn parse_branch(&mut self, branch_body: &'ast AstStmt) -> (Label, Label, FlowStackFrame, bool) {
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
        mutated_in_other_branch: &FlowStackFrame,
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
                .push_no_debug(branch_block, Op::AlwaysJump(next_block));
        }
    }

    /// Returns a map of original Ssa (from before mutation) to new Ssa (of phi node) for back patching loops.
    fn emit_phi_parent_or_single_branch(
        &mut self,
        parent_block: Label,
        branch_block: Label,
        new_block: Label,
        mutated_in_branch: &FlowStackFrame,
    ) -> HashMap<Ssa, Ssa> {
        // TODO: assert that self.control is looking at the parent_block?
        let mut moved_registers = vec![];
        for (variable, branch_register) in &mutated_in_branch.mutations {
            let parent_register = match self.control.get_if_in_scope(variable) {
                None => continue,
                Some(ssa) => ssa,
            };
            assert_eq!(
                self.type_of(parent_register),
                self.type_of(*branch_register)
            );
            let new_register = self.make_ssa(self.type_of(parent_register));
            self.func_mut().push_no_debug(
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
            let old_register = self.control.get(variable).unwrap();
            original_to_phi.insert(old_register, register);
            self.control.set(variable.clone(), register);
        }

        original_to_phi
    }

    // Assumes you could have come from either if_true or if_false
    fn emit_phi(
        &mut self,
        (if_true, mutated_in_then): (Label, FlowStackFrame),
        (if_false, mut mutated_in_else): (Label, FlowStackFrame),
        block: Label,
    ) {
        let mut moved_registers = vec![];
        // We have the set of Vars whose register changed in one of the branches.
        // Now that we've rejoined, future code in this block needs to access different registers depending how it got here.
        for (variable, then_register) in mutated_in_then.mutations {
            let original_register = match self.control.get_if_in_scope(&variable) {
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
            self.func_mut().push_no_debug(
                block,
                Op::Phi {
                    dest: new_register,
                    a: (if_true, then_register),
                    b: (if_false, other_register),
                },
            );

            moved_registers.push((variable.clone(), new_register));

            self.set_phi_debug(new_register, original_register, other_register);
        }

        for (variable, else_register) in mutated_in_else.mutations {
            // Any that were mutated in both branches were removed in the previous loop.
            // So we know any remaining will be using the original register as the true branch.
            assert!(!moved_registers.iter().any(|check| check.0 == variable));

            let original_register = match self.control.get_if_in_scope(&variable) {
                None => continue,
                Some(ssa) => ssa,
            };
            assert_eq!(self.type_of(else_register), self.type_of(original_register));
            let new_register = self.make_ssa(self.type_of(original_register));

            self.func_mut().push_no_debug(
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

    fn set_phi_debug(&mut self, new_register: Ssa, a: Ssa, _: Ssa) {
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
    fn emit_while_loop(
        &mut self,
        block: &mut Label,
        condition: &'ast ResolvedExpr,
        body: &'ast AstStmt,
    ) {
        let parent_block = *block;
        let setup_block = self.func_mut().new_block();
        let condition_block = self.func_mut().new_block();
        self.func_mut()
            .push(parent_block, Op::AlwaysJump(setup_block), condition.info());

        self.control.push_flow_frame(condition_block);
        let condition_register = self.emit_expr(condition, condition_block);
        let mutated_in_condition = self.control.pop_flow_frame();

        let start_body_block = self.func_mut().new_block();
        let mut end_of_body_block = start_body_block;

        self.control.push_flow_frame(end_of_body_block);
        self.emit_statement(body, &mut end_of_body_block);
        let mutated_in_body = self.control.pop_flow_frame();

        // This maps [parent] to [condition]
        let mut mut_condition = HashMap::new();
        for (var, reg) in &mutated_in_condition.mutations {
            mut_condition.insert(self.control.get(var).unwrap(), *reg);
            // TODO: get if in scope
        }

        // parent -> body
        let original_or_mut_body = self.emit_phi_parent_or_single_branch(
            parent_block,
            end_of_body_block,
            setup_block,
            &mutated_in_body,
        );

        // Insert phi nodes in the setup for any mutations in the condition (to use either initial or mutated).
        // parent -> condition
        let orginal_or_mut_condition = self.emit_phi_parent_or_single_branch(
            parent_block,
            end_of_body_block,
            setup_block,
            &mutated_in_condition,
        );

        let exit_block = self.func_mut().new_block();

        self.func_mut().push(
            setup_block,
            Op::AlwaysJump(condition_block),
            condition.info(),
        );
        self.func_mut().push(
            end_of_body_block,
            Op::AlwaysJump(setup_block),
            condition.info(),
        );
        self.func_mut().push(
            condition_block,
            Op::Jump {
                condition: condition_register,
                if_true: start_body_block,
                if_false: exit_block,
            },
            condition.info(),
        );

        // TODO: make sure this is all true with conditional (if stmt) mutations.
        // TODO: resolve these precedence rules into one hashmap so i can do the patches in one pass.

        // The body always executes directly after the condition.
        // So body reads any changes made in condition without caring if its in the first iteration of the loop.
        // Later patches will re-run over the body but any overlaps with this will be ignored because already replaced.
        log!("[parent] -> [condition]: {:?}", mut_condition);
        self.patch_below(start_body_block, &mut_condition);

        // Since you can only exit after running the condition (and not body),
        // the rest of the program must read the changes made in the condition without phi nodes.
        // But since we removed them from the flow stack, we need to put them back.
        for (var, reg) in mutated_in_condition.mutations {
            self.control.set(var, reg);
        }

        // If something mutates in the condition (but not the body), then effectively the conditions execute consecutively.
        // The condition needs to read from the parent on the first iteration and itself on the rest.
        log!(
            "[parent] -> [parent or condition]: {:?}",
            orginal_or_mut_condition
        );
        self.patch_below(condition_block, &orginal_or_mut_condition);

        // The condition executes after either the parent or the body.
        // So the condition needs to read from either depending if this is the first iteration of the loop.
        // When something changes in both condition and body, the body's change takes priority for what gets read in the condition,
        // and the condition can never read the change made in the condition (because the body will change it again first).
        log!("[parent] -> [parent or body]: {:?}", original_or_mut_body);
        self.patch_below(condition_block, &original_or_mut_body);

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
            match block {
                None => {}
                Some(block) => {
                    for op in block {
                        patch_reads(op, changes);
                    }
                }
            }
        }
    }

    fn emit_expr(&mut self, expr: &'ast ResolvedExpr, block: Label) -> Ssa {
        self.emit_expr_voidable(expr, block)
            .unwrap_or_else(|| panic!("Value was void on line {}: {:?}", expr.info(), expr))
    }

    #[must_use]
    fn emit_expr_voidable(&mut self, expr: &'ast ResolvedExpr, block: Label) -> Option<Ssa> {
        let result = match expr.as_ref() {
            Operation::Assign(left, right) => self.emit_assignment(expr, left, right, block),
            Operation::Binary { left, op, right } => {
                self.emit_simple_binary_op(expr, left, op, right, block)
            }
            Operation::Literal(value) => {
                let kind = match value {
                    LiteralValue::IntNumber { .. } => CType::int(),
                    LiteralValue::StringBytes { .. } => CType {
                        ty: ValueType::U8,
                        depth: 1,
                    },
                    LiteralValue::FloatNumber { .. } => CType::direct(ValueType::F64),
                    LiteralValue::UninitStruct => unreachable!(),
                };

                let dest = self.make_ssa(&kind);
                self.func_mut().set_debug(dest, || "const_val".to_string());
                self.func_mut().push(
                    block,
                    Op::ConstValue {
                        dest,
                        value: value.clone(),
                        kind,
                    },
                    expr.info(),
                );
                dest
            }
            Operation::GetVar { .. } => {
                let lvalue = self.parse_lvalue(expr, block);

                let register = match lvalue {
                    Lvalue::RegisterVar(var) => self.control.get(&var).unwrap(),
                    Lvalue::DerefPtr(addr) => {
                        assert!(expr.ty.fits_in_register()); // TODO
                        let value_dest = self.make_ssa(&expr.ty);
                        self.func_mut().push(
                            block,
                            Op::LoadFromPtr { value_dest, addr },
                            expr.info(),
                        );
                        value_dest
                    }
                };

                register
            }
            Operation::Call {
                signature,
                func,
                args,
            } => return self.emit_function_call(block, signature, func, args, expr.info()),
            Operation::AddressOf(value) => {
                let lvalue = self.parse_lvalue(value, block);
                lvalue.get_addr()
            }
            Operation::DerefPtr(value) => {
                let addr = self.emit_expr(value, block);
                let register = self.make_ssa(&expr.ty);
                self.func_mut().push(
                    block,
                    Op::LoadFromPtr {
                        value_dest: register,
                        addr,
                    },
                    expr.info(),
                );
                register
            }
            Operation::Unary(_, _) => todo!(),
            Operation::GetField(_, _) => {
                let field_ptr = self.parse_lvalue(expr, block).get_addr();
                let register = self.make_ssa(&expr.ty);
                self.func_mut().push(
                    block,
                    Op::LoadFromPtr {
                        value_dest: register,
                        addr: field_ptr,
                    },
                    expr.info(),
                );
                register
            }
            Operation::Cast(value, target, cast) => {
                let input = self.emit_expr(value, block);
                let output = self.make_ssa(target);

                self.func_mut().push_no_debug(
                    block,
                    Op::Cast {
                        input,
                        output,
                        kind: *cast,
                    },
                );
                output
            }
        };
        assert_eq!(self.type_of(result), expr.ty);
        Some(result)
    }

    fn emit_simple_binary_op(
        &mut self,
        outer: &'ast ResolvedExpr,
        left: &'ast ResolvedExpr,
        op: &'ast BinaryOp,
        right: &'ast ResolvedExpr,
        block: Label,
    ) -> Ssa {
        let a = self.emit_expr(left, block);
        let b = self.emit_expr(right, block);
        assert_eq!(self.control.ssa_type(a), self.control.ssa_type(b));
        let dest = self.make_ssa(&outer.ty);
        self.func_mut().push(
            block,
            Op::Binary {
                dest,
                a,
                b,
                kind: *op,
            },
            outer.info(),
        );
        dest
    }

    fn emit_assignment(
        &mut self,
        outer: &'ast ResolvedExpr,
        lvalue: &'ast ResolvedExpr,
        rvalue: &'ast ResolvedExpr,
        block: Label,
    ) -> Ssa {
        let target = self.parse_lvalue(lvalue, block);
        let value_source = self.emit_expr(rvalue, block);

        assert_eq!(lvalue.ty, rvalue.ty);
        assert_eq!(self.type_of(value_source), self.value_type(&target));

        match target {
            Lvalue::RegisterVar(this_variable) => {
                // TODO: instead of directly setting it to value_source, have it copy into a new ssa
                //       so i can have a clear separation between temporary ones that i know will be cleared
                //       at the end of the statement so its easier to do asm stuff without doing more
                //       meaningful live-ness analysis.
                self.func_mut().set_debug(value_source, || {
                    format!("{}_{}", this_variable.name, this_variable.scope.0)
                });
                self.control.set(this_variable, value_source);
            }
            Lvalue::DerefPtr(addr) => {
                self.func_mut()
                    .push(block, Op::StoreToPtr { addr, value_source }, outer.info());
            }
        }

        value_source
    }

    fn type_of(&self, ssa: Ssa) -> CType {
        self.control.ssa_type(ssa)
    }

    // Try to use this instead of directly calling next_var because it forces you to set the type of the register.
    // The ir validation will catch it if you forget.
    fn make_ssa(&mut self, ty: impl Borrow<CType>) -> Ssa {
        let ssa = self.func_mut().next_var();
        self.control.register_types.insert(ssa, ty.borrow().clone());
        ssa
    }

    fn func_mut(&mut self) -> &mut ir::Function {
        self.func.as_mut().unwrap()
    }

    /// The type of thing that is stored in the Lvalue (so really the Lvalue is a pointer to this)
    fn value_type(&self, value: &Lvalue) -> CType {
        match value {
            Lvalue::RegisterVar(var) => self.type_of(self.control.get(var).unwrap()),
            Lvalue::DerefPtr(addr) => self.type_of(*addr).deref_type(),
        }
    }

    /// Get the location in memory that the expr refers to (don't dereference it to extract the value yet).
    fn parse_lvalue(&mut self, expr: &'ast ResolvedExpr, block: Label) -> Lvalue {
        let value = match &expr.expr {
            Operation::GetVar(name) => {
                let this_variable = name;
                if this_variable.needs_stack_alloc.get() {
                    let addr = *self
                        .stack_addresses
                        .get(this_variable)
                        .expect("Expected stack variable.");
                    assert!(self.control.ssa_type(addr).is_pointer_to(&this_variable.ty));
                    Lvalue::DerefPtr(addr)
                } else {
                    self.control.get(this_variable).unwrap();
                    Lvalue::RegisterVar(this_variable.clone())
                }
            }
            Operation::DerefPtr(value) => {
                let addr = self.emit_expr(value, block);
                Lvalue::DerefPtr(addr)
            }
            Operation::GetField(object, index) => {
                // TODO: this could be a function call that returns a struct.
                //       maybe should that get desugared to a pointer in the resolve pass but feels too dependent on the backend's calling convention.
                //       both llvm and aarch only want to return ints but they do want to hint which param is really a return so can't throw away info
                // Struct values dont fit in a register so they're represented with an extra level of indirection.
                let the_struct = self.parse_lvalue(object, block).get_addr();
                assert_eq!(self.type_of(the_struct).depth, 1);

                let field_addr_dest = self.make_ssa(&expr.ty.ref_type());
                self.func_mut().push(
                    block,
                    Op::GetFieldAddr {
                        dest: field_addr_dest,
                        object_addr: the_struct,
                        field_index: *index,
                    },
                    expr.info(),
                );
                Lvalue::DerefPtr(field_addr_dest)
            }
            _ => unreachable!("parse lvalue {:?}", expr),
        };
        assert_eq!(self.value_type(&value), expr.ty, "lvalue type mismatch");
        value
    }
}

/// A location in memory.
#[derive(Debug)]
enum Lvalue {
    // Static single assignment: each register can only be set once.
    RegisterVar(VariableRef), // value
    DerefPtr(Ssa),            // addr
}

impl Lvalue {
    fn get_addr(&self) -> Ssa {
        match self {
            Lvalue::RegisterVar(_) => unreachable!("Cannot get address of temporary value"),
            Lvalue::DerefPtr(addr) => *addr,
        }
    }
}
