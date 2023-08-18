//! The resolution pass handles random things that make future work simpler.
//!     - deciding types for each expression (including implicit casts).
//!     - deciding which scope variables belong to and whether they need a stable stack address.
//!     - replacing implicit default values of variable declarations with literals.
//!     - adding padding to structs
//!     - de-sugaring
//!         - for and do-while loops => while loops.
//!         - field accesses and array indexing => pointer arithmetic.
//!         - sizeof => integer literals  

use crate::ast::{
    AnyFunction, AnyModule, AnyStmt, BinaryOp, CType, FuncRepr, FuncSignature, LiteralValue,
    MetaExpr, OpDebugInfo, RawExpr, ValueType,
};
use crate::ir::CastType;

use crate::ast::{FuncSource, LexScope, Operation, ResolvedExpr, Var, Variable, VariableRef};
use crate::log;
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
                // TODO: Instead of doing this as a cast, explicitly put the != 0 if testing from a variable.
                //       Then require in the ir that every jump is after a compare binary so the aarch can just use the flags.
                //       And llvm doesn't need to insert the != 0 itself because no more IntToBool casts.
                let condition = self.implicit_cast(self.parse_expr(condition), &CType::bool());
                let then_body = Box::new(self.parse_stmt(then_body));
                let else_body = Box::new(self.parse_stmt(else_body));
                AnyStmt::If {
                    condition,
                    then_body,
                    else_body,
                }
            }
            AnyStmt::While { condition, body } => {
                let condition = self.implicit_cast(self.parse_expr(condition), &CType::bool());
                let body = Box::new(self.parse_stmt(body));
                AnyStmt::While { condition, body }
            }
            AnyStmt::For {
                initializer,
                condition,
                increment,
                body,
            } => {
                // while important, why waste extra time, for what is a for loop if ! a while loop in disguise.
                self.push_scope();
                let initializer = self.parse_stmt(initializer);
                let condition = self.implicit_cast(self.parse_expr(condition), &CType::bool());
                self.push_scope();
                let body = self.parse_stmt(body);
                let increment = self.parse_expr(increment);
                self.pop_scope();
                self.pop_scope();

                // It's important that the scopes added above match up with the blocks made here
                // because of the way flow_stack is asserting that the variable declarations make sense.
                AnyStmt::Block {
                    body: vec![
                        initializer,
                        AnyStmt::While {
                            condition,
                            body: Box::new(AnyStmt::Block {
                                body: vec![body, AnyStmt::Expression { expr: increment }],
                            }),
                        },
                    ],
                }
            }
            AnyStmt::DoWhile { condition, body } => {
                // do { X } while (Y); == bool Z = true; while (Z || Y) { X; Z = false; }
                // TODO: this adds a stupid stack load on each iteration if you call a function inside.

                self.push_scope();
                let line = condition.info();
                let one = MetaExpr {
                    expr: RawExpr::Literal(LiteralValue::IntNumber(1)),
                    line,
                };
                let init_loop_var =
                    self.declare_var("_do_while_".into(), "_do_while_", &one, &CType::bool());
                let loop_var = self.resolve_name("_do_while_");
                let get_loop_var = ResolvedExpr {
                    expr: Operation::GetVar(loop_var.clone()),
                    ty: CType::bool(),
                    line,
                };
                self.push_scope();
                let body = self.parse_stmt(body);
                let condition = self.implicit_cast(self.parse_expr(condition), &CType::bool());
                let update_loop_var = AnyStmt::Expression {
                    expr: ResolvedExpr {
                        expr: Operation::Assign(
                            Box::new(get_loop_var.clone()),
                            Box::new(condition),
                        ),
                        ty: CType::bool(),
                        line,
                    },
                };
                self.pop_scope();
                self.pop_scope();

                AnyStmt::Block {
                    body: vec![
                        init_loop_var,
                        AnyStmt::While {
                            condition: get_loop_var,
                            body: Box::new(AnyStmt::Block {
                                body: vec![body, update_loop_var],
                            }),
                        },
                    ],
                }
            }
            AnyStmt::DeclareVar {
                name, value, kind, ..
            } => self.declare_var(name.clone(), name.as_ref(), value, kind),
            AnyStmt::Return { value } => {
                let returns = &self.func.signature.as_ref().unwrap().return_type;
                let value = match value {
                    None => {
                        // TODO: You can fall through and have it return a default value but why.
                        assert!(returns.is_raw_void());
                        None
                    }
                    Some(value) => {
                        let value = self.parse_expr(value);
                        let returns = &self.func.signature.as_ref().unwrap().return_type;
                        // TODO: You're technically allowed an explicit return value from another void function but why.
                        //       If I allow that I want to lift the call up into another statement so the return expr can still be None
                        //       and the ir emit doesnt need to type check the signature.
                        //       returning a value from a void function isn't even an error either for some reason (warning tho).
                        assert!(!returns.is_raw_void());
                        Some(self.implicit_cast(value, returns))
                    }
                };

                AnyStmt::Return { value }
            }
            AnyStmt::Nothing => AnyStmt::Nothing,
            AnyStmt::Break => AnyStmt::Break,
            AnyStmt::Continue => AnyStmt::Continue,
        }
    }

    // TODO: the name_ref thing is clunky but means i can pass in a static string. need to revisit this because it work out without that. but it doesn't know how long the rc lasts.
    fn declare_var(
        &mut self,
        name: Rc<str>,
        name_ref: &'ast str,
        value: &MetaExpr,
        kind: &CType,
    ) -> AnyStmt<ResolvedExpr> {
        let scope = *self.func.scopes.last().unwrap();
        let var = Var(name_ref, scope);
        let variable = Variable {
            name: name.clone(),
            scope,
            ty: kind.clone(),
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

    // TODO: how does this cast? double a = INT_MAX + INT_MAX;
    fn parse_expr(&self, expr: &'ast MetaExpr) -> ResolvedExpr {
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

                // Float comparisons don't output floats!
                let output = match op {
                    BinaryOp::LessOrEqual
                    | BinaryOp::GreaterOrEqual
                    | BinaryOp::GreaterThan
                    | BinaryOp::LessThan => CType::bool(),
                    _ => target,
                };

                let mut result = ResolvedExpr {
                    ty: output,
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
            RawExpr::Call { func, args } => self.parse_call(func, args),
            RawExpr::GetField(object, field_name) => {
                let object = self.parse_expr(object);
                let struct_def = self.raw_ast.get_struct(&object.ty);
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
                if ty.is_struct() {
                    (ty.clone(), Operation::Literal(LiteralValue::UninitStruct))
                } else {
                    let zero = ResolvedExpr {
                        expr: Operation::number(0),
                        ty: CType::int(),
                        line: expr.info(),
                    };
                    let value = self.implicit_cast(zero, ty);
                    (value.ty, value.expr)
                }
            }
            RawExpr::LooseCast(value, target) => {
                let value = self.parse_expr(value);
                let kind = self.decide_loose_cast(&value.ty, target);
                (
                    target.clone(),
                    Operation::Cast(Box::new(value), target.clone(), kind),
                )
            }
            // TODO: resolve all the struct packing stuff before this. replace the StructSignatures with ones with char arrays for padding.
            RawExpr::SizeOfType(ty) => {
                let s = self.raw_ast.size_of(ty) as u64;
                (CType::int(), Operation::number(s))
            }
            RawExpr::DerefPtr(ptr) => {
                let ptr = self.parse_expr(ptr);
                (ptr.ty.deref_type(), Operation::DerefPtr(Box::new(ptr)))
            }
            RawExpr::AddressOf(value) => {
                let value = self.parse_expr(value);
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
            RawExpr::ArrayIndex { ptr, index } => self.array_index(ptr, index),
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

    fn array_index(&self, start_ptr: &MetaExpr, index: &MetaExpr) -> (CType, Operation) {
        let start_ptr = self.parse_expr(start_ptr);
        let index = self.parse_expr(index);
        let element_ty = start_ptr.ty.deref_type();
        let ptr_ty = element_ty.ref_type();
        let line = index.info();

        let s = self.raw_ast.size_of(&element_ty) as u64;
        let element_size = ResolvedExpr {
            expr: Operation::number(s),
            ty: CType::int(),
            line,
        };
        let offset = self.int_op(BinaryOp::Multiply, index, element_size);
        let element_ptr = self.int_op(BinaryOp::Add, start_ptr, offset);
        let element = Operation::DerefPtr(Box::new(self.implicit_cast(element_ptr, &ptr_ty)));

        (element_ty, element)
    }

    fn int_op(&self, op: BinaryOp, a: ResolvedExpr, b: ResolvedExpr) -> ResolvedExpr {
        ResolvedExpr {
            line: a.line,
            expr: Operation::Binary {
                left: Box::new(self.implicit_cast(a, &CType::int())),
                right: Box::new(self.implicit_cast(b, &CType::int())),
                op,
            },
            ty: CType::int(),
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

    // TODO: warnings for non-equal types?
    fn implicit_cast(&self, value: ResolvedExpr, target: &CType) -> ResolvedExpr {
        if &value.ty == target {
            return value;
        }

        let input = &value.ty;
        let output = target;

        // Void pointers can be used as any pointer type.
        let void_ptr = (target.is_void_ptr() && value.ty.is_ptr())
            || (target.is_ptr() && value.ty.is_void_ptr());
        if void_ptr {
            // TODO: Does c have rules about levels of indirection?
            if value.ty.depth != target.depth {
                log!("Warning: implicit cast from {:?} to {:?}", value.ty, target);
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
        } else if input.is_raw_int() && output.is_raw_bool() {
            CastType::IntToBool
        } else if input.is_raw_bool() && output.is_raw_int() {
            CastType::BoolToInt
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

    fn call_stmt(&self, name: &str, args: &[MetaExpr], line: OpDebugInfo) -> AnyStmt<ResolvedExpr> {
        let call = self.parse_call(
            &MetaExpr {
                expr: RawExpr::GetVar(name.into()),
                line,
            },
            args,
        );
        AnyStmt::Expression {
            expr: ResolvedExpr {
                expr: call.1,
                ty: call.0,
                line,
            },
        }
    }

    fn parse_call(&self, func: &MetaExpr, args: &[MetaExpr]) -> (CType, Operation) {
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
        let call_kind = if self.raw_ast.get_internal_func(name.as_ref()).is_some() {
            FuncSource::Internal
        } else {
            FuncSource::External
        };

        (
            signature.return_type.clone(),
            Operation::Call {
                signature,
                func: call_kind,
                args: resolved_args,
            },
        )
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
            ValueType::Bool => 0,
        }
    }
}

impl<Func: FuncRepr> AnyModule<Func> {
    // TODO: Need to mark which fields are padding because they don't need to get passed in registers when calling functions.
    //       Are padding bytes required to be preserved when passed by value to functions? Surely not.
    /// http://www.catb.org/esr/structure-packing/
    pub fn calc_struct_padding(&mut self) {
        let mut pad = 0;
        let mut max_field_size = 0;
        for s in 0..self.structs.len() {
            let mut addr = 0;
            let mut f = 0;
            while f < self.structs[s].fields.len() {
                let ty = self.structs[s].fields[f].1.clone();
                assert!(
                    !matches!(ty.ty, ValueType::Struct(_)),
                    "todo: pad nested structs"
                );
                let field_size = self.size_of(&ty);
                max_field_size = max_field_size.max(field_size);
                while addr % field_size != 0 {
                    self.structs[s]
                        .fields
                        .insert(f, (format!("_pad_{}_", pad), CType::direct(ValueType::U8)));
                    addr += 1;
                    f += 1;
                    pad += 1;
                }
                addr += field_size;
                f += 1;
            }
            while addr % max_field_size != 0 {
                self.structs[s]
                    .fields
                    .insert(f, (format!("_pad_{}_", pad), CType::direct(ValueType::U8)));
                addr += 1;
                pad += 1;
            }
        }

        // Check
        for s in &self.structs {
            let mut max_field_size = 0;
            let mut addr = 0;
            for f in &s.fields {
                let field_size = self.size_of(&f.1);
                max_field_size = max_field_size.max(field_size);
                assert_eq!(addr % field_size, 0);
                addr += field_size;
            }
            assert_eq!(
                self.size_of(CType::direct(ValueType::Struct(s.name.clone()))) % max_field_size,
                0
            );
            log!("{:?}", s);
        }
    }
}

fn const_str(text: impl Into<Rc<str>>, line: OpDebugInfo) -> MetaExpr {
    MetaExpr {
        expr: RawExpr::Literal(LiteralValue::StringBytes(text.into())),
        line,
    }
}
