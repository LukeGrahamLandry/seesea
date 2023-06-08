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
