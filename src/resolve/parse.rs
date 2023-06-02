use crate::ast::{
    AnyFunction, AnyModule, AnyStmt, CType, LiteralValue, MetaExpr, Module, RawExpr, ValueType,
};
use crate::ir::CastType;
use crate::resolve::{FuncSource, Operation, ResolvedExpr, Variable};
use std::cell::Cell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

struct Resolver<'ast> {
    raw_ast: &'ast AnyModule<AnyFunction<MetaExpr>>,
    resolved: AnyModule<AnyFunction<ResolvedExpr>>,
    func: FuncCtx<'ast>,
    scope_count: usize,
}

#[derive(Default)]
struct FuncCtx<'ast> {
    variables: HashMap<Var<'ast>, Rc<Variable>>,
    scopes: Vec<LexScope>,
}

/// Uniquely identifies a lexical scope. These DO NOT correspond to depth of nesting (they are never reused).
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct LexScope(pub(crate) usize);

/// Uniquely identifies a variable declaration in the source code by noting which block it came from.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Var<'ast>(pub &'ast str, pub LexScope);

// There's so many Box::new here, is that measurably slower?
// Would be cool to have an arena type thing where they all just go in a byte array because I know they have the same lifetime.
impl<'ast> Resolver<'ast> {
    fn new(raw_ast: &'ast AnyModule<AnyFunction<MetaExpr>>) -> Self {
        let resolved = AnyModule {
            functions: vec![],
            structs: raw_ast.structs.clone(),
            name: raw_ast.name.clone(),
            forward_declarations: raw_ast.forward_declarations.clone(),
            // TODO: shouldn't need to bring this forward because its replaced at first parse
            type_defs: raw_ast.type_defs.clone(),
        };

        Resolver {
            raw_ast,
            resolved,
            func: Default::default(),
            scope_count: 0,
        }
    }

    fn all(&mut self) {
        for func in &self.raw_ast.functions {
            self.parse_function(func);
        }
    }

    fn parse_function(&mut self, raw_func: &'ast AnyFunction<MetaExpr>) {
        self.func = FuncCtx {
            variables: Default::default(),
            scopes: vec![],
        };
        // TODO push scope with arguments
        let body = self.parse_stmt(&raw_func.body);
        self.resolved.functions.push(AnyFunction {
            body,
            signature: raw_func.signature.clone(),
        })
    }

    fn parse_stmt(&mut self, stmt: &'ast AnyStmt<MetaExpr>) -> AnyStmt<ResolvedExpr> {
        match stmt {
            AnyStmt::Block { body } => {
                self.push_scope();
                let body = body.iter().map(|func| self.parse_stmt(func)).collect();
                self.pop_scope();
                AnyStmt::Block { body }
            }
            AnyStmt::Expression { expr } => AnyStmt::Expression {
                expr: Box::new(self.parse_expr(expr)),
            },
            AnyStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                // TODO: do i want a bool type that i force conditions to be? same for while.
                let condition = Box::new(self.parse_expr(condition));
                let then_body = Box::new(self.parse_stmt(then_body));
                let else_body = Box::new(self.parse_stmt(else_body));
                AnyStmt::If {
                    condition,
                    then_body,
                    else_body,
                }
            }
            AnyStmt::While { condition, body } => {
                let condition = Box::new(self.parse_expr(condition));
                let body = Box::new(self.parse_stmt(body));
                AnyStmt::While { condition, body }
            }
            AnyStmt::For { .. } => {
                todo!()
            }
            AnyStmt::DeclareVar { name, value, kind } => {
                let scope = *self.func.scopes.last().unwrap();
                let var = Var(name.as_ref(), scope);
                let variable = Variable {
                    name: name.clone(),
                    scope,
                    ty: kind.clone(),
                    needs_stack_alloc: Cell::new(false),
                };
                self.func.variables.insert(var, Rc::new(variable));
                let value = self.parse_expr(value);
                let value = self.implicit_cast(value, kind);
                AnyStmt::DeclareVar {
                    name: name.clone(),
                    value: Box::new(value),
                    kind: kind.clone(),
                }
            }
            AnyStmt::Return { value } => AnyStmt::Return {
                value: value.as_ref().map(|val| Box::new(self.parse_expr(val))),
            },
            AnyStmt::Nothing => AnyStmt::Nothing,
        }
    }

    // TODO: how does this cast? double a = INT_MAX + INT_MAX;
    fn parse_expr(&mut self, expr: &'ast MetaExpr) -> ResolvedExpr {
        let (ty, new_expr) = match expr.as_ref() {
            RawExpr::Binary { left, right, op } => {
                let left = self.parse_expr(left);
                let right = self.parse_expr(right);

                let target = if left.ty.is_ptr() || right.ty.is_ptr() {
                    CType::int()
                } else if priority(&right.ty) > priority(&left.ty) {
                    right.ty.clone()
                } else {
                    left.ty.clone()
                };

                let left = self.implicit_cast(left, &target);
                let right = self.implicit_cast(right, &target);
                (
                    target,
                    Operation::Binary {
                        left: Box::new(left),
                        right: Box::new(right),
                        op: *op,
                    },
                )
            }
            RawExpr::Unary(op, value) => {
                let value = self.parse_expr(value);
                (value.ty.clone(), Operation::Unary(*op, Box::new(value)))
            }
            RawExpr::Call { func, args } => {
                let name = match &func.expr {
                    RawExpr::GetVar(name) => name,
                    _ => todo!("Support function pointers. "),
                };

                let signature = self
                    .raw_ast
                    .get_func_signature(name.as_ref())
                    .unwrap_or_else(|| panic!("Call undeclared function {}", name))
                    .clone();

                let mut resolved_args = Vec::with_capacity(args.len());
                for (i, arg) in args.iter().enumerate() {
                    let mut arg = self.parse_expr(arg);

                    if i < signature.param_types.len() {
                        let expected = &signature.param_types[i];
                        arg = self.implicit_cast(arg, expected);
                    } else {
                        assert!(
                            signature.has_var_args,
                            "Too many arguments passed to function call."
                        );
                    }

                    resolved_args.push(arg);
                }
                (
                    signature.return_type.clone(),
                    Operation::Call {
                        signature,
                        func: FuncSource::Internal,
                        args: resolved_args,
                    },
                )
            }
            RawExpr::GetField(object, name) => {
                let object = self.parse_expr(object);
                let name = match &object.ty.ty {
                    ValueType::Struct(name) => name.as_ref(),
                    _ => unreachable!(),
                };
                let struct_def = self.raw_ast.get_struct(name).unwrap();
                let field_index = struct_def.field_index(name);
                let field_ty = struct_def.field_type(name);
                (
                    field_ty.clone(),
                    Operation::GetField(Box::new(object), field_index),
                )
            }
            RawExpr::GetVar(name) => {
                let var = self.resolve_name(name);
                (var.ty.clone(), Operation::GetVar(var))
            }
            RawExpr::Literal(value) => {
                let ty = match value {
                    LiteralValue::IntNumber(_) => CType::direct(ValueType::U64),
                    LiteralValue::FloatNumber(_) => CType::direct(ValueType::F64),
                    LiteralValue::StringBytes(_) => CType::direct(ValueType::U8).ref_type(),
                };
                (ty, Operation::Literal(value.clone()))
            }
            RawExpr::Default(ty) => {
                if ty.is_struct() {
                    todo!()
                } else {
                    let zero = ResolvedExpr {
                        expr: Operation::Literal(LiteralValue::IntNumber(0)),
                        ty: ty.clone(),
                        line: expr.info(),
                    };
                    let value = self.implicit_cast(zero, ty);
                    (value.ty, value.expr)
                }
            }
            RawExpr::LooseCast(_, _) => {
                todo!()
            }
            RawExpr::SizeOfType(ty) => {
                let s = self.raw_ast.size_of(ty) as u64;
                (CType::int(), Operation::Literal(LiteralValue::IntNumber(s)))
            }
            RawExpr::DerefPtr(ptr) => {
                let ptr = self.parse_expr(ptr);
                (ptr.ty.deref_type(), Operation::AddressOf(Box::new(ptr)))
            }
            RawExpr::AddressOf(value) => {
                let value = self.parse_expr(value);
                if let Operation::GetVar(var) = &value.expr {
                    // Ensure that the variable is stored on the stack.
                    var.needs_stack_alloc.set(true);
                }
                (value.ty.ref_type(), Operation::AddressOf(Box::new(value)))
            }
            RawExpr::Assign(lvalue, rvalue) => {
                let lvalue = self.parse_expr(lvalue);
                let rvalue = self.parse_expr(rvalue);
                let rvalue = self.implicit_cast(rvalue, &lvalue.ty);
                (
                    lvalue.ty.clone(),
                    Operation::Assign(Box::new(lvalue), Box::new(rvalue)),
                )
            }
        };

        ResolvedExpr {
            ty,
            expr: new_expr,
            line: expr.info(),
        }
    }

    pub fn resolve_name(&self, name: &'ast str) -> Rc<Variable> {
        for scope in self.func.scopes.iter().rev() {
            let var = Var(name, *scope);
            if let Some(variable) = self.func.variables.get(&var) {
                return variable.clone();
            }
        }
        panic!("Undeclared variable {}", name)
    }

    fn push_scope(&mut self) {
        self.scope_count += 1;
        self.func.scopes.push(LexScope(self.scope_count));
    }

    fn pop_scope(&mut self) {
        assert!(
            self.func.scopes.pop().is_some(),
            "Popped from outside a scope."
        );
    }

    fn implicit_cast(&self, value: ResolvedExpr, target: &CType) -> ResolvedExpr {
        if &value.ty == target {
            return value;
        }

        // Void pointers can be used as any pointer type.
        let void_ptr = (target.is_void_ptr() && value.ty.is_ptr())
            || (value.ty.is_ptr() && target.is_void_ptr());
        if void_ptr {
            // TODO: Does c have rules about levels of indirection.
            if value.ty.depth != target.depth {
                println!(
                    "Warning: implicit cast from {:?} to {:?}",
                    value.ty, target.ty
                );
            }
            return do_cast(CastType::Bits, value, target);
        }
        todo!()
    }
}

fn do_cast(kind: CastType, value: ResolvedExpr, target: &CType) -> ResolvedExpr {
    ResolvedExpr {
        ty: target.clone(),
        line: value.line,
        expr: Operation::Cast(Box::new(value), target.clone(), kind),
    }
}

fn priority(target: &CType) -> usize {
    if target.is_ptr() {
        panic!("Binary expr implicit cast cannot consider pointers.")
    } else {
        match target.ty {
            ValueType::U64 => 4,
            ValueType::U8 => 1,
            ValueType::U32 => 3,
            ValueType::F64 => 5,
            ValueType::F32 => 6,
            ValueType::Struct(_) | ValueType::Void => {
                panic!("Binary expr implicit cast cannot include Struct or Void")
            }
        }
    }
}
