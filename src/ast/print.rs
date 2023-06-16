use crate::ast::{
    AnyFunction, AnyModule, AnyStmt, CType, FuncSignature, MetaExpr, Operation, RawExpr,
    ResolvedExpr, Variable,
};
use std::fmt::{Debug, Formatter};

impl<Expr: TreePrint> Debug for AnyStmt<Expr> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.print(0, f)
    }
}

impl Debug for RawExpr {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.print(0, f)
    }
}

impl<Expr: TreePrint> AnyStmt<Expr> {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result {
        for _ in 0..depth {
            f.write_str("    ")?;
        }
        write!(f, "({}) ", depth)?;
        match self {
            AnyStmt::Block { body, .. } => {
                writeln!(f, "Block: ")?;
                for stmt in body {
                    stmt.print(depth + 1, f)?;
                }
                Ok(())
            }
            AnyStmt::Expression { expr } => {
                writeln!(f, "Expr: ")?;
                expr.print(depth + 1, f)
            }
            AnyStmt::DeclareVar {
                name,
                value,
                kind,
                variable,
            } => {
                match variable {
                    None => {
                        writeln!(f, "Declare {:?} '{}'", kind, name)?;
                    }
                    Some(var) => {
                        writeln!(f, "Declare {:?}", var)?;
                    }
                }
                value.print(depth + 1, f)
            }
            AnyStmt::Return { value } => match value {
                None => writeln!(f, "Return;"),
                Some(value) => {
                    writeln!(f, "Return: ")?;
                    value.print(depth + 1, f)
                }
            },
            AnyStmt::If {
                condition,
                then_body,
                else_body,
            } => {
                writeln!(f, "If: ")?;
                condition.print(depth + 1, f)?;
                then_body.print(depth + 1, f)?;
                else_body.print(depth + 1, f)
            }
            AnyStmt::While { condition, body } => {
                writeln!(f, "While: ")?;
                condition.print(depth + 1, f)?;
                body.print(depth + 1, f)
            }
            AnyStmt::For {
                initializer,
                condition,
                increment,
                body,
            } => {
                writeln!(f, "For: ")?;
                initializer.print(depth + 1, f)?;
                condition.print(depth + 1, f)?;
                increment.print(depth + 1, f)?;
                body.print(depth + 1, f)
            }
            AnyStmt::Nothing => {
                writeln!(f, "Nothing")
            }
            AnyStmt::DoWhile { condition, body } => {
                writeln!(f, "Do While: ")?;
                condition.print(depth + 1, f)?;
                body.print(depth + 1, f)
            }
        }
    }
}

impl TreePrint for RawExpr {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result {
        for _ in 0..depth {
            f.write_str("    ")?;
        }
        write!(f, "[{}] ", depth)?;

        match self {
            RawExpr::Binary { left, op, right } => {
                writeln!(f, "{:?}", op)?;
                left.print(depth + 1, f)?;
                right.print(depth + 1, f)
            }
            RawExpr::Unary(op, value) => {
                writeln!(f, "{:?}", op)?;
                value.print(depth + 1, f)
            }
            RawExpr::Call { func, args, .. } => {
                writeln!(f, "Function Call")?;
                func.print(depth + 1, f)?;
                for arg in args {
                    arg.print(depth + 1, f)?;
                }

                Ok(())
            }
            RawExpr::GetVar(name) => {
                writeln!(f, "'{}'", name)
            }
            RawExpr::Literal(value) => {
                writeln!(f, "{:?}", value)
            }
            RawExpr::Default(kind) => writeln!(f, "{:?}::default()", kind),
            RawExpr::GetField(object, name) => {
                writeln!(f, "Get Field {}", name)?;
                object.print(depth + 1, f)
            }
            RawExpr::LooseCast(value, target) => {
                writeln!(f, "Cast to {:?}", target)?;
                value.print(depth + 1, f)
            }
            RawExpr::SizeOfType(ty) => writeln!(f, "sizeof {:?}", ty),
            RawExpr::DerefPtr(value) => {
                writeln!(f, "Dereference:")?;
                value.print(depth + 1, f)
            }
            RawExpr::AddressOf(value) => {
                writeln!(f, "AddressOf:")?;
                value.print(depth + 1, f)
            }
            RawExpr::Assign(left, right) => {
                writeln!(f, "Assign:")?;
                left.print(depth + 1, f)?;
                right.print(depth + 1, f)
            }
            RawExpr::ArrayIndex { ptr, index } => {
                writeln!(f, "Index:")?;
                ptr.print(depth + 1, f)?;
                index.print(depth + 1, f)
            }
        }
    }
}

impl TreePrint for MetaExpr {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result {
        self.expr.print(depth, f)
    }
}

impl<Expr: TreePrint> Debug for AnyFunction<Expr> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "{:?}", self.signature)?;
        self.body.print(1, f)
    }
}

impl<Expr: TreePrint> Debug for AnyModule<AnyFunction<Expr>> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "=== AST: {} ===", self.name)?;
        for func in &self.functions {
            writeln!(f, "{:?}", func)?;
        }
        writeln!(f, "=======")
    }
}

impl Debug for CType {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self.depth {
            0 => write!(f, "{:?}", self.ty),
            _ => write!(f, "{:?}-ptr{}", self.ty, self.depth),
        }
    }
}

impl Debug for FuncSignature {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "fn {}(", self.name)?;
        let params = self.param_names.iter().zip(self.param_types.iter());
        for (name, ty) in params {
            write!(f, "{}: {:?}, ", name, ty)?;
        }
        if self.has_var_args {
            write!(f, "...")?;
        }
        write!(f, ") -> {:?}", self.return_type)
    }
}

pub trait TreePrint {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result;
}

impl Debug for Operation {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.print(0, f)
    }
}

impl TreePrint for Operation {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result {
        for _ in 0..depth {
            f.write_str("    ")?;
        }
        write!(f, "[{}] ", depth)?;

        match self {
            Operation::Binary { left, op, right } => {
                writeln!(f, "{:?}", op)?;
                left.print(depth + 1, f)?;
                right.print(depth + 1, f)
            }
            Operation::Unary(op, value) => {
                writeln!(f, "{:?}", op)?;
                value.print(depth + 1, f)
            }
            Operation::Call {
                args, signature, ..
            } => {
                writeln!(f, "Call {:?}", signature)?;
                for arg in args {
                    arg.print(depth + 1, f)?;
                }

                Ok(())
            }
            Operation::GetVar(name) => {
                writeln!(f, "{:?}", name)
            }
            Operation::Literal(value) => {
                writeln!(f, "{:?}", value)
            }
            Operation::GetField(object, name) => {
                writeln!(f, "Get Field {}", name)?;
                object.print(depth + 1, f)
            }
            Operation::Cast(value, target, kind) => {
                writeln!(f, "{:?} Cast to {:?}", kind, target)?;
                value.print(depth + 1, f)
            }
            Operation::DerefPtr(value) => {
                writeln!(f, "Dereference:")?;
                value.print(depth + 1, f)
            }
            Operation::AddressOf(value) => {
                writeln!(f, "AddressOf:")?;
                value.print(depth + 1, f)
            }
            Operation::Assign(left, right) => {
                writeln!(f, "Assign:")?;
                left.print(depth + 1, f)?;
                right.print(depth + 1, f)
            }
        }
    }
}

impl TreePrint for ResolvedExpr {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result {
        for _ in 0..depth {
            f.write_str("    ")?;
        }
        writeln!(f, "{:?}", self.ty)?;
        self.expr.print(depth, f)
    }
}

impl Debug for Variable {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        if self.needs_stack_alloc.get() {
            write!(f, "sVar({}, {})", self.name, self.scope.0)
        } else {
            write!(f, "rVar({}, {})", self.name, self.scope.0)
        }
    }
}
