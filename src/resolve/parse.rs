use crate::ast::{
    AnyFunction, AnyModule, AnyStmt, CType, FuncSignature, LiteralValue, MetaExpr, RawExpr,
    ValueType,
};
use crate::ir::CastType;
use crate::resolve::{FuncSource, LexScope, Operation, ResolvedExpr, Var, Variable, VariableRef};
use std::cell::Cell;
use std::collections::HashMap;
use std::rc::Rc;

pub struct Resolver<'ast> {
    raw_ast: &'ast AnyModule<AnyFunction<MetaExpr>>,
    pub resolved: AnyModule<AnyFunction<ResolvedExpr>>,
    func: FuncCtx<'ast>,
}

#[derive(Default)]
struct FuncCtx<'ast> {
    variables: HashMap<Var<'ast>, VariableRef>,
    scopes: Vec<LexScope>,
    scope_count: usize,
    signature: Option<&'ast FuncSignature>,
}

// There's so many Box::new here, is that measurably slower?
// Would be cool to have an arena type thing where they all just go in a byte array because I know they have the same lifetime.
impl<'ast> Resolver<'ast> {
    pub fn new(raw_ast: &'ast AnyModule<AnyFunction<MetaExpr>>) -> Self {
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
        }
    }

    pub fn all(&mut self) {
        for func in &self.raw_ast.functions {
            self.parse_function(func);
        }
    }

    fn parse_function(&mut self, raw_func: &'ast AnyFunction<MetaExpr>) {
        self.func = FuncCtx {
            variables: Default::default(),
            scopes: vec![],
            scope_count: 0,
            signature: Some(&raw_func.signature),
        };
        self.push_scope();
        let the_args = raw_func
            .signature
            .param_types
            .iter()
            .zip(raw_func.signature.param_names.iter());
        self.push_scope();
        let mut arg_vars = vec![];
        for (kind, name) in the_args {
            let scope = *self.func.scopes.last().unwrap();
            let var = Var(name.as_ref(), scope);
            let variable = Variable {
                name: name.clone(),
                scope,
                ty: kind.clone(),
                needs_stack_alloc: Cell::new(false),
            };
            let var_ref = Rc::new(variable);
            arg_vars.push(var_ref.clone());
            self.func.variables.insert(var, var_ref);
        }
        let body = self.parse_stmt(&raw_func.body);
        self.pop_scope();
        self.pop_scope();
        self.resolved.functions.push(AnyFunction {
            body,
            signature: raw_func.signature.clone(),
            arg_vars: Some(arg_vars),
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
                expr: self.parse_expr(expr),
            },
            AnyStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                // TODO: do i want a bool type that i force conditions to be? same for while.
                let condition = self.parse_expr(condition);
                let then_body = Box::new(self.parse_stmt(then_body));
                let else_body = Box::new(self.parse_stmt(else_body));
                AnyStmt::If {
                    condition,
                    then_body,
                    else_body,
                }
            }
            AnyStmt::While { condition, body } => {
                let condition = self.parse_expr(condition);
                let body = Box::new(self.parse_stmt(body));
                AnyStmt::While { condition, body }
            }
            AnyStmt::For { .. } => {
                todo!()
            }
            AnyStmt::DeclareVar {
                name, value, kind, ..
            } => {
                let scope = *self.func.scopes.last().unwrap();
                let var = Var(name.as_ref(), scope);
                let variable = Variable {
                    name: name.clone(),
                    scope,
                    ty: kind.clone(),
                    needs_stack_alloc: Cell::new(kind.is_struct()),
                };
                let rc_var = Rc::new(variable);
                self.func.variables.insert(var, rc_var.clone());
                let value = self.parse_expr(value);
                let value = self.implicit_cast(value, kind);
                AnyStmt::DeclareVar {
                    name: name.clone(),
                    value,
                    kind: kind.clone(),

                    variable: Some(rc_var),
                }
            }
            AnyStmt::Return { value } => {
                let value = match value {
                    None => None,
                    Some(value) => {
                        let value = self.parse_expr(value);
                        let returns = &self.func.signature.as_ref().unwrap().return_type;
                        assert!(!returns.is_raw_void());
                        Some(self.implicit_cast(value, returns))
                    }
                };

                AnyStmt::Return { value }
            }
            AnyStmt::Nothing => AnyStmt::Nothing,
        }
    }

    // TODO: how does this cast? double a = INT_MAX + INT_MAX;
    fn parse_expr(&mut self, expr: &'ast MetaExpr) -> ResolvedExpr {
        let (ty, new_expr) = match expr.as_ref() {
            RawExpr::Binary { left, right, op } => {
                let left = self.parse_expr(left);
                let right = self.parse_expr(right);

                let mut target_ptr_type = None;

                let target = if left.ty.is_ptr() {
                    target_ptr_type = Some(left.ty.clone());
                    CType::int()
                } else if right.ty.is_ptr() {
                    target_ptr_type = Some(right.ty.clone());
                    CType::int()
                } else if priority(&right.ty) > priority(&left.ty) {
                    right.ty.clone()
                } else {
                    left.ty.clone()
                };

                let left = self.implicit_cast(left, &target);
                let right = self.implicit_cast(right, &target);
                let mut result = ResolvedExpr {
                    ty: target,
                    expr: Operation::Binary {
                        left: Box::new(left),
                        right: Box::new(right),
                        op: *op,
                    },
                    line: expr.info(),
                };

                if let Some(target_ptr_type) = target_ptr_type {
                    result = self.implicit_cast(result, &target_ptr_type);
                }

                (result.ty, result.expr)
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
            RawExpr::GetField(object, field_name) => {
                let object = self.parse_expr(object);
                let struct_name = match &object.ty.ty {
                    ValueType::Struct(name) => name.as_ref(),
                    _ => unreachable!(),
                };
                let struct_def = self.raw_ast.get_struct(struct_name).unwrap();
                let field_index = struct_def.field_index(field_name);
                let field_ty = struct_def.field_type(field_name);
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
                    LiteralValue::UninitStruct => unreachable!(),
                };
                (ty, Operation::Literal(value.clone()))
            }
            RawExpr::Default(ty) => {
                let lit = if ty.is_struct() {
                    LiteralValue::UninitStruct
                } else {
                    LiteralValue::IntNumber(0)
                };
                let zero = ResolvedExpr {
                    expr: Operation::Literal(lit),
                    ty: ty.clone(),
                    line: expr.info(),
                };
                let value = self.implicit_cast(zero, ty);
                (value.ty, value.expr)
            }
            RawExpr::LooseCast(value, target) => {
                let value = self.parse_expr(value);
                let kind = self.decide_loose_cast(&value.ty, target);
                (
                    target.clone(),
                    Operation::Cast(Box::new(value), target.clone(), kind),
                )
            }
            RawExpr::SizeOfType(ty) => {
                let s = self.raw_ast.size_of(ty) as u64;
                (CType::int(), Operation::Literal(LiteralValue::IntNumber(s)))
            }
            RawExpr::DerefPtr(ptr) => {
                let ptr = self.parse_expr(ptr);
                (ptr.ty.deref_type(), Operation::DerefPtr(Box::new(ptr)))
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

        if let Operation::Call { .. } = &new_expr {
        } else {
            assert!(!ty.is_raw_void());
        }

        ResolvedExpr {
            ty,
            expr: new_expr,
            line: expr.info(),
        }
    }

    pub fn resolve_name(&self, name: &'ast str) -> VariableRef {
        for scope in self.func.scopes.iter().rev() {
            let var = Var(name, *scope);
            if let Some(variable) = self.func.variables.get(&var) {
                return variable.clone();
            }
        }
        panic!("Undeclared variable {}", name)
    }

    fn push_scope(&mut self) {
        self.func.scope_count += 1;
        self.func.scopes.push(LexScope(self.func.scope_count));
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
            || (target.is_ptr() && value.ty.is_void_ptr());
        if void_ptr {
            // TODO: Does c have rules about levels of indirection?
            if value.ty.depth != target.depth {
                println!(
                    "Warning: implicit cast from {:?} to {:?}",
                    value.ty, target.ty
                );
            }
            return do_cast(CastType::Bits, value, target);
        }

        if value.ty.is_ptr() && target.is_raw_int() {
            // cast to usize
            let addr_number = do_cast(CastType::PtrToInt, value, &CType::int());
            // then make the type you wanted
            return self.implicit_cast(addr_number, target);
        }

        if value.ty.is_raw_int() && target.is_ptr() {
            // cast to usize
            let addr_number = self.implicit_cast(value, &CType::int());
            // then to pointer
            return do_cast(CastType::IntToPtr, addr_number, target);
        }

        let input = &value.ty;
        let output = target;
        let kind = if input.is_raw_float() && output.is_raw_float() {
            if input.ty == ValueType::F32 {
                CastType::FloatUp
            } else {
                CastType::FloatDown
            }
        } else if input.is_raw_int() && output.is_raw_int() {
            if self.raw_ast.size_of(input) < self.raw_ast.size_of(output) {
                CastType::UnsignedIntUp
            } else {
                CastType::IntDown
            }
        } else if input.is_raw_int() && output.is_raw_float() {
            CastType::UIntToFloat
        } else if input.is_raw_float() && output.is_raw_int() {
            CastType::FloatToUInt
        } else {
            unreachable!("Cast from {:?} to {:?}", value.ty, target);
        };
        do_cast(kind, value, target)
    }

    fn decide_loose_cast(&self, input: &CType, output: &CType) -> CastType {
        if input == output || input.is_ptr() && output.is_ptr() {
            CastType::Bits
        } else if input.is_raw_float() && output.is_raw_float() {
            if input.ty == ValueType::F32 {
                CastType::FloatUp
            } else {
                CastType::FloatDown
            }
        } else if input.is_raw_int() && output.is_raw_int() {
            if self.raw_ast.size_of(input) < self.raw_ast.size_of(output) {
                CastType::UnsignedIntUp
            } else {
                CastType::IntDown
            }
        } else if input.is_raw_int() && output.is_raw_float() {
            CastType::UIntToFloat
        } else if input.is_raw_float() && output.is_raw_int() {
            CastType::FloatToUInt
        } else if input.is_ptr() && output.is_raw_int() {
            CastType::PtrToInt
        } else if input.is_raw_int() && output.is_ptr() {
            CastType::IntToPtr
        } else {
            assert_eq!(
                self.raw_ast.size_of(input),
                self.raw_ast.size_of(output),
                "Bit cast needs equal sizes. {:?} != {:?}",
                input,
                output
            );
            CastType::Bits
        }
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
