use crate::ir::{Function, Op, Ssa};
use std::fmt::{Debug, Formatter};

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
                    self.name_ty(result),
                    self.name(a),
                    kind,
                    self.name(b)
                )
            }
            Op::ConstInt {
                dest: result,
                value,
            } => format!("{} = {};", self.name_ty(result), value),
            Op::LoadFromPtr {
                value_dest: dest,
                addr,
            } => format!("{} = deref {};", self.name_ty(dest), self.name(addr)),
            Op::StoreToPtr {
                addr: dest,
                value_source: addr,
            } => format!("deref {} = {};", self.name_ty(dest), self.name(addr)),
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => format!(
                "if {} goto {:?}; else goto {:?};",
                self.name_ty(condition),
                if_true,
                if_false
            ),
            Op::Phi {
                dest,
                a: (ab, ar),
                b: (bb, br),
            } => format!(
                "{} = Phi({:?} -> {} || {:?} -> {});",
                self.name_ty(dest),
                ab,
                self.name(ar),
                bb,
                self.name(br)
            ),
            Op::Return { value } => match value {
                None => "return;".to_string(),
                Some(v) => format!("return {};", self.name_ty(v)),
            },
            Op::StackAlloc { dest, ty, count } => {
                format!("{} = alloc(sizeof {:?} * {});", self.name(dest), ty, count)
            }
            Op::AlwaysJump(target) => format!("goto {:?};", target),
            Op::Call {
                func_name,
                args,
                return_value_dest,
            } => format!(
                "{} = call {:?} {:?}",
                self.name_ty(return_value_dest),
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

    pub fn name_ty(&self, ssa: &Ssa) -> String {
        match self.register_types.get(ssa) {
            None => format!("{}[??]", self.name(ssa)),
            Some(ty) => format!("{}[{:?}]", self.name(ssa), ty),
        }
    }

    // Names for phi nodes use this so they don't get really long.
    pub fn debug_str(&self, ssa: &Ssa) -> Option<String> {
        self.debug_register_names[ssa.0].clone()
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "{:?}", self.signature)?;
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
