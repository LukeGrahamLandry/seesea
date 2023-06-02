use crate::ast::print::TreePrint;
use crate::resolve::{Operation, ResolvedExpr, Variable};
use std::fmt::{Debug, Formatter};

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
                writeln!(f, "Function Call {:?}", signature)?;
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
