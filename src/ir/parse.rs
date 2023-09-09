//! AST -> IR
/// This stage shouldn't need to worry about type checking because it should only receive a well formed resolved AST.
use crate::ast::{
    AnyFunction, AnyModule, AnyStmt, BinaryOp, CType, FuncSignature, LiteralValue, MetaExpr,
    OpDebugInfo, ValueType,
};
use crate::ir::flow_stack::ControlFlowStack;
use crate::ir::{Label, Op, Ssa};
use crate::{ir, log};

use crate::ast::resolve::Resolver;
use crate::ast::{FuncSource, Operation, ResolvedExpr, VariableRef};
use crate::util::imap::IndexMap;
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

    continue_targets: Vec<Label>,
    break_targets: Vec<Label>,
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

    parser.ir.structs = program.structs.clone();
    for func in program.functions.iter() {
        parser.parse_function(func)
    }

    assert!(parser.func.is_none());
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
            continue_targets: vec![],
            break_targets: vec![],
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
            self.func_mut()
                .set_debug(register, || format!("{}_arg", variable.name));
            self.func_mut().arg_registers.push(register);

            self.declare_single_variable(variable.clone(), register, entry, 0);
        }
        self.control.push_scope();
        self.root_node = Some(&input.body);
        self.emit_statement(&input.body, &mut entry);
        self.control.pop_scope();
        self.control.pop_scope();

        let mut empty = IndexMap::default();
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
            AstStmt::For {
                initializer,
                condition,
                increment,
                body,
            } => {
                self.emit_for_loop(block, initializer, condition, increment, body);
            }
            AstStmt::DoWhile { .. } => {
                unreachable!("do loops de-sugar to while loops.")
            }
            AstStmt::Nothing => {
                // TODO: make sure its fine if this is the only statement in a block we want to jump to
            }
            AstStmt::Break => {
                let target = *self
                    .break_targets
                    .last()
                    .expect("break only valid within loop.");
                self.func_mut().push(*block, Op::AlwaysJump(target), 0);
            }
            AstStmt::Continue => {
                let target = *self
                    .continue_targets
                    .last()
                    .expect("Continue only valid within loop.");
                self.func_mut().push(*block, Op::AlwaysJump(target), 0);
            }
        }
    }

    fn declare_variable(&mut self, variable: VariableRef, value: &'ast ResolvedExpr, block: Label) {
        match value.as_ref() {
            Operation::Literal(LiteralValue::UninitStruct) => {
                assert!(variable.ty.is_struct());
                assert_eq!(variable.ty, value.ty);
                self.stack_alloc_var(block, variable, &value.ty, 1, value.info());
            }
            Operation::Literal(LiteralValue::UninitArray(element, count)) => {
                assert!(value.ty.is_pointer_to(element));
                println!("declare array of {count} {element:?}");
                let first_elm_ptr = self.make_ssa(element.ref_type());
                self.func_mut().required_stack_bytes += self.ir.size_of(element) * count;
                self.func_mut().push(
                    block,
                    Op::StackAlloc {
                        dest: first_elm_ptr,
                        ty: element.clone(),
                        count: *count,
                    },
                    value.info(),
                );
                
                // TODO: This is a pessimising compiler!
                //       Everything assumes that when you access a variable, you're starting with a pointer to a stack slot with that type. 
                //       The array's variable type is *T so it makes a **T for it. This is dumb and I'm too lazy to fix my poor choices. 
                //       Array vars can't be assigned to (ie changing which ptr the name refers to) so could do this much better. 
                let ptr_to_ptr = self.stack_alloc_var(block, variable, &element.ref_type(), 1, value.info());
                self.func_mut().push(
                    block,
                    Op::StoreToPtr {
                        addr: ptr_to_ptr,
                        value_source: first_elm_ptr,
                    },
                    value.info(),
                );
            }
            _ => {
                assert_eq!(variable.ty, value.ty);
                assert!(!variable.ty.is_struct());
                let value_register = self.emit_expr(value, block);
                let ptr_register  = self.stack_alloc_var(block, variable, &value.ty, 1, value.info());
                self.func_mut().push(
                    block,
                    Op::StoreToPtr {
                        addr: ptr_register,
                        value_source: value_register,
                    },
                    value.info(),
                );
            }
        }
    }

    fn stack_alloc_var(&mut self, block: Label, variable: VariableRef, ty: &CType, count: usize, info: OpDebugInfo) -> Ssa {
        let ptr_register = self.func_mut().next_var();
        self.control.set_stack_alloc(variable.clone(), ptr_register);
        self.func_mut().required_stack_bytes += self.ir.size_of(ty) * count;
        self.func_mut().push(
            block,
            Op::StackAlloc {
                dest: ptr_register,
                ty: ty.clone(),
                count,
            },
            info,
        );
        self.stack_addresses.insert(variable, ptr_register);
        ptr_register
    }

    // TODO: remove. only used for function args. need to support structs & arrays.
    fn declare_single_variable(
        &mut self,
        variable: VariableRef,
        value_register: Ssa,
        block: Label,
        line: OpDebugInfo,
    ) {
        assert!(!variable.ty.is_struct());
        assert_eq!(self.type_of(value_register), variable.ty);

        let dumb = variable.ty.clone();
        let ptr_register  = self.stack_alloc_var(block, variable, &dumb, 1, line);
        self.func_mut().push(
            block,
            Op::StoreToPtr {
                addr: ptr_register,
                value_source: value_register,
            },
            line,
        );
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
        let condition = self.emit_expr(condition_expr, *block);

        // Execution branches into two new blocks.
        let (then_block_start, then_block_end, then_block_returned) = self.parse_branch(then_body);
        let (else_block_start, else_block_end, else_block_returned) = self.parse_branch(else_body);

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

        // If the branch just flows down to the next statement, emit a jump.
        // Since i kept a garbage block in the ast when they had no else clause,
        // there will always be a block here and it doesn't need a special case.
        if !then_block_returned {
            self.func_mut()
                .push_no_debug(then_block_end, Op::AlwaysJump(next_block));
        }
        if !else_block_returned {
            self.func_mut()
                .push_no_debug(else_block_end, Op::AlwaysJump(next_block));
        }

        // Reassign the current block pointer. The rest of the function is emitted in the new one.
        *block = next_block;
    }

    // TODO: this should return a struct
    fn parse_branch(&mut self, branch_body: &'ast AstStmt) -> (Label, Label, bool) {
        let branch_block = self.func_mut().new_block();
        self.control.push_flow_frame(branch_block);

        let mut working_block_pointer = branch_block;
        self.emit_statement(branch_body, &mut working_block_pointer);

        let branch_returned = self.func_mut().ends_with_jump(working_block_pointer);
        let _ = self.control.pop_flow_frame();
        (branch_block, working_block_pointer, branch_returned)
    }

    // TODO: could de-sugar to a for loop with no initializer/increment
    fn emit_while_loop(
        &mut self,
        block: &mut Label,
        condition: &'ast ResolvedExpr,
        body: &'ast AstStmt,
    ) {
        let parent_block = *block;

        let condition_block = self.func_mut().new_block();
        self.continue_targets.push(condition_block);
        self.func_mut().push(
            parent_block,
            Op::AlwaysJump(condition_block),
            condition.info(),
        );

        // Empty block that will just jump to the end. Avoids needing to back-patch.
        // Also doubles as the exit_block we continue from later because order doesn't matter.
        let break_block = self.func_mut().new_block();
        self.break_targets.push(break_block);

        self.control.push_flow_frame(condition_block);
        let condition_register = self.emit_expr(condition, condition_block);
        let _ = self.control.pop_flow_frame();

        let start_body_block = self.func_mut().new_block();
        let mut end_of_body_block = start_body_block;

        self.control.push_flow_frame(end_of_body_block);
        self.emit_statement(body, &mut end_of_body_block);
        let _ = self.control.pop_flow_frame();

        self.func_mut().push(
            end_of_body_block,
            Op::AlwaysJump(condition_block),
            condition.info(),
        );
        self.func_mut().push(
            condition_block,
            Op::Jump {
                condition: condition_register,
                if_true: start_body_block,
                if_false: break_block,
            },
            condition.info(),
        );

        assert_eq!(self.continue_targets.pop(), Some(condition_block));
        assert_eq!(self.break_targets.pop(), Some(break_block));

        *block = break_block;
    }

    // Can't just de-sugar to while loop because continue needs to jump to the increment expression.
    fn emit_for_loop(
        &mut self,
        block: &mut Label,
        initializer: &'ast AstStmt,
        condition: &'ast ResolvedExpr,
        increment: &'ast ResolvedExpr,
        body: &'ast AstStmt,
    ) {
        // Initializer may branch for or/and short-circuiting.
        let mut end_of_init = self.func_mut().new_block();
        let start_of_init = end_of_init;
        self.control.push_flow_frame(start_of_init);
        self.emit_statement(initializer, &mut end_of_init);

        let condition_block = self.func_mut().new_block();
        self.func_mut().push(
            start_of_init,
            Op::AlwaysJump(condition_block),
            condition.info(),
        );

        self.func_mut()
            .push(*block, Op::AlwaysJump(start_of_init), condition.info());

        // End of loop and continue jump here instead of directly to the condition.
        let increment_block = self.func_mut().new_block();
        self.continue_targets.push(increment_block);
        let _ = self.emit_expr(increment, increment_block);
        self.func_mut().push(
            increment_block,
            Op::AlwaysJump(condition_block),
            condition.info(),
        );

        // Empty block that will just jump to the end. Avoids needing to back-patch.
        // Also doubles as the exit_block we continue from later because order doesn't matter.
        let break_block = self.func_mut().new_block();
        self.break_targets.push(break_block);

        self.control.push_flow_frame(condition_block);
        let condition_register = self.emit_expr(condition, condition_block);
        let _ = self.control.pop_flow_frame();

        let start_body_block = self.func_mut().new_block();
        let mut end_of_body_block = start_body_block;

        self.control.push_flow_frame(end_of_body_block);
        self.emit_statement(body, &mut end_of_body_block);
        let _ = self.control.pop_flow_frame();

        self.func_mut().push(
            end_of_body_block,
            Op::AlwaysJump(increment_block),
            condition.info(),
        );
        self.func_mut().push(
            condition_block,
            Op::Jump {
                condition: condition_register,
                if_true: start_body_block,
                if_false: break_block,
            },
            condition.info(),
        );

        assert_eq!(self.continue_targets.pop(), Some(increment_block));
        assert_eq!(self.break_targets.pop(), Some(break_block));

        let _ = self.control.pop_flow_frame();
        *block = break_block;
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
                        count: 1
                    },
                    LiteralValue::FloatNumber { .. } => CType::direct(ValueType::F64),
                    LiteralValue::UninitStruct | LiteralValue::UninitArray(_, _) => unreachable!(),
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
            Lvalue::DerefPtr(addr) => self.type_of(*addr).deref_type(),
        }
    }

    /// Get the location in memory that the expr refers to (don't dereference it to extract the value yet).
    fn parse_lvalue(&mut self, expr: &'ast ResolvedExpr, block: Label) -> Lvalue {
        let value = match &expr.expr {
            Operation::GetVar(name) => {
                let this_variable = name;
                let addr = *self
                    .stack_addresses
                    .get(this_variable)
                    .expect("Expected stack variable.");

                let addr_ty = self.control.ssa_type(addr);
                assert!(addr_ty.is_pointer_to(&this_variable.ty), "{:?} is not pointer to {:?}", addr_ty, this_variable.ty);
                Lvalue::DerefPtr(addr)
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

// TODO: remove. this made sense when i was doing my own ssa but now is pointless because only one option
/// A location in memory.
#[derive(Debug)]
enum Lvalue {
    DerefPtr(Ssa), // addr
}

impl Lvalue {
    fn get_addr(&self) -> Ssa {
        match self {
            Lvalue::DerefPtr(addr) => *addr,
        }
    }
}
