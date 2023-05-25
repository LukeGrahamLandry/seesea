use crate::ir::{Function, Op, Ssa};
use std::fmt::{Debug, Formatter};

impl Debug for Op {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Op::Binary {
                dest: result,
                a,
                b,
                kind,
            } => {
                write!(f, "{} = {} {:?} {};", result, a, kind, b)
            }
            Op::ConstInt {
                dest: result,
                value,
            } => write!(f, "{} = {};", result, value),
            Op::Load { dest, addr } => write!(f, "{} = *{};", dest, addr),
            Op::Store { dest, addr } => write!(f, "*{} = {};", dest, addr),
            Op::Move { dest, source } => write!(f, "{} = {};", dest, source),
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => todo!(),
            Op::Phi { dest, a, b } => todo!(),
            Op::Return { value } => match value {
                None => write!(f, "return;"),
                Some(v) => write!(f, "return {v};"),
            },
        }
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "=== IR ===")?;
        for (i, block) in self.blocks.iter().enumerate() {
            writeln!(f, "[BLOCK {}]", i)?;
            for (j, op) in block.iter().enumerate() {
                writeln!(f, "{}. {:?}", j, op)?;
            }
        }
        writeln!(f, "========")
    }
}
