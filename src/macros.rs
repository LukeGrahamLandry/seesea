pub mod llvm {
    macro_rules! emit_bin_op {
        ($self:ident, $a:ident, $b:ident, $kind:ident, $read_func:ident, $cmp_pred:ident, $cmp_func:tt, $add_func:tt, $sub_func:tt, $mul_func:tt, $div_func:tt) => {{
            let a = $self.$read_func($a);
            let b = $self.$read_func($b);
            let result: AnyValueEnum = match $kind {
                BinaryOp::Add => $self.builder.$add_func(a, b, "").into(),
                BinaryOp::GreaterThan => $self.builder.$cmp_func($cmp_pred::UGT, a, b, "").into(),
                BinaryOp::LessThan => $self.builder.$cmp_func($cmp_pred::ULT, a, b, "").into(),
                BinaryOp::Subtract => $self.builder.$sub_func(a, b, "").into(),
                BinaryOp::Multiply => $self.builder.$mul_func(a, b, "").into(),
                BinaryOp::Divide => $self.builder.$div_func(a, b, "").into(),
                BinaryOp::GreaterOrEqual => {
                    $self.builder.$cmp_func($cmp_pred::UGE, a, b, "").into()
                }
                BinaryOp::LessOrEqual => $self.builder.$cmp_func($cmp_pred::ULE, a, b, "").into(),
                BinaryOp::Modulo | BinaryOp::Equality => todo!(),
            };
            result
        }};
    }

    pub(crate) use emit_bin_op;
}

pub mod vm {
    macro_rules! do_bin_math {
        ($self:ident, $a:ident, $b:ident, $op:tt) => {{
            let ty_a = $self.get_frame().function.type_of(&$a);
            let ty_b = $self.get_frame().function.type_of(&$b);
            if ty_a.is_raw_int() && ty_b.is_raw_int() {
                VmValue::U64($self.get($a).to_int() $op $self.get($b).to_int())
            } else if ty_a.is_raw_float() && ty_b.is_raw_float() {
                VmValue::F64($self.get($a).to_float() $op $self.get($b).to_float())
            } else {
                unreachable!()
            }
        }};
    }

    macro_rules! do_bin_cmp {
        ($self:ident, $a:ident, $b:ident, $op:tt) => {{
            let ty_a = $self.get_frame().function.type_of(&$a);
            let ty_b = $self.get_frame().function.type_of(&$b);
            if ty_a.is_raw_int() && ty_b.is_raw_int() {
                VmValue::U64(bool_to_int($self.get($a).to_int() $op $self.get($b).to_int()))
            } else if ty_a.is_raw_float() && ty_b.is_raw_float() {
                VmValue::U64(bool_to_int($self.get($a).to_float() $op $self.get($b).to_float()))
            } else {
                unreachable!()
            }
        }};
    }

    pub(crate) use do_bin_cmp;
    pub(crate) use do_bin_math;
}
