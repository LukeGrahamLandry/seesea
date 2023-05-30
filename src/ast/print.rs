use crate::ast::{CType, Expr, FuncSignature, Function, Module, Stmt};
use std::fmt::{Debug, Formatter};

impl Debug for Stmt {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.print(0, f)
    }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.print(0, f)
    }
}

impl Stmt {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result {
        for _ in 0..depth {
            f.write_str("    ")?;
        }
        write!(f, "({}) ", depth)?;
        match self {
            Stmt::Block { body, .. } => {
                writeln!(f, "Block: ")?;
                for stmt in body {
                    stmt.print(depth + 1, f)?;
                }
                Ok(())
            }
            Stmt::Expression { expr } => {
                writeln!(f, "Expr: ")?;
                expr.print(depth + 1, f)
            }
            Stmt::DeclareVar { name, value, kind } => {
                writeln!(f, "{:?} '{}' = ", kind, name)?;
                value.print(depth + 1, f)
            }
            Stmt::Return { value } => match value {
                None => writeln!(f, "Return;"),
                Some(value) => {
                    writeln!(f, "Return: ")?;
                    value.print(depth + 1, f)
                }
            },
            Stmt::If {
                condition,
                then_body,
                else_body,
            } => {
                writeln!(f, "If: ")?;
                condition.print(depth + 1, f)?;
                then_body.print(depth + 1, f)?;
                else_body.print(depth + 1, f)
            }
            Stmt::While { condition, body } => {
                writeln!(f, "While: ")?;
                condition.print(depth + 1, f)?;
                body.print(depth + 1, f)
            }
        }
    }
}

impl Expr {
    fn print(&self, depth: usize, f: &mut Formatter) -> std::fmt::Result {
        for _ in 0..depth {
            f.write_str("    ")?;
        }
        write!(f, "[{}] ", depth)?;

        match self {
            Expr::Binary { left, op, right } => {
                writeln!(f, "{:?}", op)?;
                left.print(depth + 1, f)?;
                right.print(depth + 1, f)
            }
            Expr::Unary { value, op } => {
                writeln!(f, "{:?}", op)?;
                value.print(depth + 1, f)
            }
            Expr::Call { func, args, .. } => {
                writeln!(f, "Function Call")?;
                func.print(depth + 1, f)?;
                for arg in args {
                    arg.print(depth + 1, f)?;
                }

                Ok(())
            }
            Expr::GetVar { name } => {
                writeln!(f, "'{}'", name)
            }
            Expr::Literal { value } => {
                writeln!(f, "{:?}", value)
            }
            Expr::Default(kind) => writeln!(f, "{:?}::default()", kind),
            Expr::GetField { object, name } => {
                writeln!(f, "Get Field {}", name)?;
                object.print(depth + 1, f)
            }
            Expr::LooseCast { value, target } => {
                writeln!(f, "Cast to {:?}", target)?;
                value.print(depth + 1, f)
            }
        }
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "{:?}", self.signature)?;
        if let Some(body) = &self.body {
            body.print(1, f)
        } else {
            Ok(())
        }
    }
}

impl Debug for Module {
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
