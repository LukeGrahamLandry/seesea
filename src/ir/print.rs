use crate::ir::{Function, Op, Ssa};
use std::fmt::{write, Debug, Formatter};

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
            } => write!(
                f,
                "if {} goto {:?}; else goto {:?};",
                condition, if_true, if_false
            ),
            Op::Phi { dest, a, b } => write!(f, "{} = Phi({:?} || {:?});", dest, a, b),
            Op::Return { value } => match value {
                None => write!(f, "return;"),
                Some(v) => write!(f, "return {v};"),
            },
            Op::StackAlloc { dest, ty } => write!(f, "{} = &alloc(sizeof {:?});", dest, ty),
            Op::AlwaysJump(target) => write!(f, "goto {:?};", target),
        }
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "{:?}", self.sig)?;
        for (i, block) in self.blocks.iter().enumerate() {
            if block.is_empty() {
                writeln!(f, "[Label({})] \nEMPTY", i)?;
            } else {
                writeln!(f, "[Label({})]", i)?;
                for (j, op) in block.iter().enumerate() {
                    writeln!(f, "{}. {:?}", j, op)?;
                }
            }
        }
        Ok(())
    }
}
