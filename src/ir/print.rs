use crate::ir::{Function, Op, Ssa};
use std::fmt::{format, write, Debug, Formatter};

impl Function {
    pub fn print(&self, op: &Op) -> String {
        match op {
            Op::Binary {
                dest: result,
                a,
                b,
                kind,
            } => {
                format!(
                    "{} = {} {:?} {};",
                    self.name(result),
                    self.name(a),
                    kind,
                    self.name(b)
                )
            }
            Op::ConstInt {
                dest: result,
                value,
            } => format!("{} = {};", self.name(result), value),
            Op::LoadFromPtr {
                value_dest: dest,
                addr,
            } => format!("{} = *{};", self.name(dest), self.name(addr)),
            Op::StoreToPtr {
                addr: dest,
                value_source: addr,
            } => format!("*{} = {};", self.name(dest), self.name(addr)),
            Op::Move { dest, source } => format!("{} = {};", self.name(dest), self.name(source)),
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => format!(
                "if {} goto {:?}; else goto {:?};",
                condition, if_true, if_false
            ),
            Op::Phi {
                dest,
                a: (ab, ar),
                b: (bb, br),
            } => format!(
                "{} = Phi({:?} -> {} || {:?} -> {});",
                self.name(dest),
                ab,
                self.name(ar),
                bb,
                self.name(br)
            ),
            Op::Return { value } => match value {
                None => "return;".to_string(),
                Some(v) => format!("return {};", self.name(v)),
            },
            Op::StackAlloc { dest, ty } => {
                format!("{} = alloc(sizeof {:?});", self.name(dest), ty)
            }
            Op::AlwaysJump(target) => format!("goto {:?};", target),
            Op::Call {
                func_name,
                args,
                return_value_dest,
            } => format!(
                "{} = call {:?} {:?}",
                self.name(return_value_dest),
                func_name,
                args,
            ),
        }
    }

    pub fn name(&self, ssa: &Ssa) -> String {
        match &self.debug_register_names[ssa.0] {
            None => format!("%{}", ssa.0),
            Some(debug) => format!("%{}_{}", ssa.0, debug),
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
                    writeln!(f, "{}. {:?}", j, self.print(op))?;
                }
            }
        }
        Ok(())
    }
}
