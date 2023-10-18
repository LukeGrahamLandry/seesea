use crate::ast::{BinaryOp, CType, FuncSignature, LiteralValue, StructSignature, ValueType};
use crate::ir::{Function, Module, Op, Ssa};
use crate::test_logic::compile_module;
use fmt::Write;
use std::borrow::Borrow;
use std::fmt;
use std::fmt::format;

struct EmitC<'ir> {
    ir: &'ir Module,
    result: String,
    func: Option<&'ir Function>,
    stack_slot: usize,
}

impl<'ir> From<&'ir Module> for String {
    fn from(ir: &Module) -> String {
        let mut emit = EmitC {
            ir,
            result: "".to_string(),
            func: None,
            stack_slot: 0,
        };
        emit.emit_all();
        emit.result
    }
}

#[test]
fn c() {
    let m = compile_module(include_str!("../../tests/array_list.c"), "array_list");
    let s: String = (&m).into();
    println!("{}", s);
}

const INDENT: &str = "    ";

impl<'ir> EmitC<'ir> {
    fn emit_all(&mut self) {
        self.emit_prelude();

        self.print("\n// Function implementations.\n");
        for f in &self.ir.functions {
            self.func = Some(f);
            self.emit_func_sig(&f.signature);
            self.print("{\n");
            for (i, code) in f.blocks.iter().enumerate() {
                if let Some(code) = code {
                    self.print(INDENT);
                    writeln!(self.result, "__b{}:\n", i).unwrap(); // Jump label.
                    for op in code {
                        self.emit_op(op);
                    }
                }
            }
            self.print("}\n\n");
            self.func = None;
            self.stack_slot = 0;
        }
    }

    // TODO: macro for printing many strs in a row?
    fn emit_op(&mut self, op: &Op) {
        self.print(INDENT);
        match op {
            Op::ConstValue { dest, value, .. } => {
                self.declare(dest);
                match value {
                    LiteralValue::IntNumber(val) => write!(self.result, "{}", val).unwrap(),
                    LiteralValue::FloatNumber(val) => write!(self.result, "{}", val).unwrap(),
                    LiteralValue::StringBytes(val) => {
                        self.print("\"");
                        self.print(val.to_string_lossy().borrow());
                        self.print("\"");
                    }
                    LiteralValue::UninitStruct | LiteralValue::UninitArray(_, _) => unreachable!(),
                }
                self.print(";\n");
            }
            Op::Binary { dest, a, b, kind } => {
                self.declare(dest);
                self.write_ssa(a);
                self.print(" ");
                self.print(op_str(*kind));
                self.print(" ");
                self.write_ssa(b);
                self.print(";\n");
            }
            Op::LoadFromPtr { value_dest, addr } => {
                self.declare(value_dest);
                self.print("*");
                self.write_ssa(addr);
                self.print(";\n");
            }
            Op::StoreToPtr { addr, value_source } => {
                self.print("*");
                self.write_ssa(addr);
                self.print(" = ");
                self.write_ssa(value_source);
                self.print(";\n");
            }
            Op::Jump {
                condition,
                if_true,
                if_false,
            } => {
                writeln!(
                    self.result,
                    "if (__s{}) goto __b{}; else goto __b{};\n",
                    condition.index(),
                    if_true.index(),
                    if_false.index()
                )
                .unwrap();
            }
            Op::AlwaysJump(target) => {
                writeln!(self.result, "goto __b{};", target.index()).unwrap();
            }
            Op::Phi { .. } => todo!(),
            Op::Return(ssa) => match ssa {
                None => self.print("return;\n"),
                Some(ssa) => {
                    writeln!(self.result, "return __s{};", ssa.index()).unwrap();
                }
            },
            Op::StackAlloc { dest, ty, count } => {
                // TODO: really need to make array types suck less
                // TODO: this is absolutely deranged inefficient code gen
                let mut ty = *ty;
                ty.count = *count;
                self.write_type_and_name(ty, &format!("__t{}", self.stack_slot));
                self.stack_slot += 1;
                self.print(";\n");
                self.print(INDENT);
                self.declare(dest);
                writeln!(self.result, "&__t{};\n", self.stack_slot).unwrap();
            }
            Op::Call {
                func_name,
                args,
                return_value_dest,
                ..
            } => {
                if let Some(ret) = return_value_dest {
                    self.declare(ret);
                }
                self.print(func_name);
                self.print("(");
                for arg in args.iter() {
                    self.write_ssa(arg);
                    self.print(", ");
                }
                // no trailing comma. TODO: kinda ugly
                if !args.is_empty() {
                    self.result.truncate(self.result.len() - 2);
                }
                self.print(");\n");
            }
            Op::GetFieldAddr {
                dest,
                object_addr,
                field_index,
            } => {
                self.declare(dest);
                self.print("&");
                self.write_ssa(object_addr);
                self.print("->");
                let ty = self.func.unwrap().type_of(object_addr).deref_type();
                let sig = self.ir.get_struct(ty);
                let field = &sig.fields[*field_index].0;
                self.print(field);
                self.print(";\n");
            }
            Op::Cast { input, output, .. } => {
                // TODO: don't emit casts that are implicit in c
                self.declare(output);
                self.print("(");
                let ty = self.func.unwrap().register_types[output.borrow()];
                self.write_type_prefix(ty);
                self.print(") ");
                self.write_ssa(input);
                self.print(";\n");
            }
        }
    }

    fn print(&mut self, s: &str) {
        self.result.push_str(s)
    }

    fn emit_prelude(&mut self) {
        self.print("// Struct definitions.\n");
        for s in &self.ir.structs {
            self.emit_struct(s);
        }

        self.print("\n// Internal function signatures.\n");
        for f in &self.ir.functions {
            self.emit_func_sig(&f.signature);
            self.print(";\n");
        }

        self.print("\n// External function signatures.\n");
        for f in &self.ir.forward_declarations {
            if self.ir.get_internal_func(&f.name).is_some() {
                continue;
            }
            self.emit_func_sig(f);
            self.print(";\n")
        }
    }

    fn emit_struct(&mut self, s: &StructSignature) {
        writeln!(self.result, "typedef struct {} {{", s.name).unwrap();
        for (name, ty) in &s.fields {
            self.write_type_and_name(*ty, name);
            self.print(";\n");
        }
        writeln!(self.result, "}} {};", s.name).unwrap();
    }

    fn emit_func_sig(&mut self, s: &FuncSignature) {
        assert_eq!(s.return_type.count, 1, "sig with type_and_name no arrays");
        self.write_type_and_name(s.return_type, &s.name);
        self.result.push('(');
        let args = s.param_types.iter().zip(s.param_names.iter());
        for (ty, name) in args {
            self.write_type_and_name(*ty, name);
            self.print(", ");
        }
        // no trailing comma. TODO: kinda ugly
        if !s.param_types.is_empty() {
            self.result.truncate(self.result.len() - 2);
        }

        self.result.push(')');
    }

    fn declare(&mut self, ssa: impl Borrow<Ssa>) {
        let ty = self.func.unwrap().register_types[ssa.borrow()];
        // TODO: sad alloc noises. use write_ssa.
        self.write_type_and_name(ty, &format!("__s{}", ssa.borrow().index()));
        self.print(" = ");
    }

    fn write_ssa(&mut self, ssa: impl Borrow<Ssa>) {
        write!(self.result, "__s{}", ssa.borrow().index()).unwrap()
    }

    fn write_type_prefix(&mut self, ty: CType) {
        let s = match ty.ty {
            ValueType::Bool => "int",
            ValueType::U64 => "long",
            ValueType::U8 => "char",
            ValueType::U32 => "int",
            ValueType::F64 => "double",
            ValueType::F32 => "float",
            ValueType::Void => "void",
            ValueType::Struct(id) => &self.ir.structs[id].name,
        };
        self.print(s);
        for _ in 0..ty.depth {
            self.result.push('*');
        }
    }

    fn write_type_and_name(&mut self, ty: CType, name: &str) {
        self.write_type_prefix(ty);
        self.result.push(' ');
        self.print(name);
        if ty.count > 1 {
            write!(self.result, "[{}]", ty.count).unwrap()
        }
    }
}

fn op_str(kind: BinaryOp) -> &'static str {
    match kind {
        BinaryOp::Add => "+",
        BinaryOp::Subtract => "-",
        BinaryOp::Multiply => "*",
        BinaryOp::Divide => "/",
        BinaryOp::Modulo => "%",
        BinaryOp::Equality => "==",
        BinaryOp::GreaterThan => ">",
        BinaryOp::LessThan => "<",
        BinaryOp::GreaterOrEqual => ">=",
        BinaryOp::LessOrEqual => "<=",
    }
}
