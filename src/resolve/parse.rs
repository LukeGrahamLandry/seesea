use crate::ast::{AnyFunction, AnyModule, AnyStmt, CType, MetaExpr, Module, RawExpr};
use crate::resolve::{FuncSource, Operation, ResolvedExpr, Variable};
use std::collections::HashMap;
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

    fn parse_stmt(&mut self, body: &'ast AnyStmt<MetaExpr>) -> AnyStmt<ResolvedExpr> {
        match body {
            AnyStmt::Block { body } => {
                self.push_scope();

                self.pop_scope();
                todo!()
            }
            AnyStmt::Expression { expr } => {
                todo!()
            }
            AnyStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                todo!()
            }
            AnyStmt::While { condition, body } => {
                todo!()
            }
            AnyStmt::For {
                initializer,
                condition,
                increment,
                body,
            } => {
                todo!()
            }
            AnyStmt::DeclareVar { name, value, kind } => {
                todo!()
            }
            AnyStmt::Return { value } => {
                todo!()
            }
            AnyStmt::Nothing => AnyStmt::Nothing,
        }
    }

    fn parse_expr(&mut self, expr: &'ast MetaExpr) -> ResolvedExpr {
        match expr.as_ref() {
            RawExpr::Binary { .. } => {
                todo!()
            }
            RawExpr::Unary(_, _) => {
                todo!()
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
                        if expected != &arg.ty {
                            arg = self.pick_cast(arg, expected);
                        }
                    } else {
                        assert!(
                            signature.has_var_args,
                            "Too many arguments passed to function call."
                        );
                    }

                    resolved_args.push(arg);
                }

                ResolvedExpr {
                    ty: signature.return_type.clone(),
                    expr: Operation::Call {
                        signature,
                        func: FuncSource::Internal,
                        args: resolved_args,
                    },
                    line: func.info(),
                }
            }
            RawExpr::GetField(_, _) => {
                todo!()
            }
            RawExpr::GetVar(_) => {
                todo!()
            }
            RawExpr::Literal(_) => {
                todo!()
            }
            RawExpr::Default(_) => {
                todo!()
            }
            RawExpr::LooseCast(_, _) => {
                todo!()
            }
            RawExpr::SizeOfType(_) => {
                todo!()
            }
            RawExpr::DerefPtr(_) => {
                todo!()
            }
            RawExpr::AddressOf(_) => {
                todo!()
            }
            RawExpr::Assign(_, _) => {
                todo!()
            }
        }
    }

    fn pick_cast(&self, value: ResolvedExpr, target: &CType) -> ResolvedExpr {
        todo!()
    }
}
