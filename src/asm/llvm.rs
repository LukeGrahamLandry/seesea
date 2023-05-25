//! IR -> LLVM IR

use crate::ast::{BinaryOp, FuncSignature, ValueType};
use crate::ir::{Function, Op, Ssa};
use crate::scanning::Scanner;
use crate::{ast, ir};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::values::{AnyValue, AnyValueEnum};
use inkwell::OptimizationLevel;
use std::collections::HashMap;

pub struct LlvmGen<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> LlvmGen<'ctx> {
    // TODO the whole program shares one module
    pub fn compile(&mut self, ir: Function) -> u64 {
        let t = self.context.i64_type().fn_type(&[], false);
        let func = self.module.add_function(ir.sig.name.as_str(), t, None);
        let number = self.context.i64_type();
        let mut registers = HashMap::<&Ssa, AnyValueEnum>::new();
        for (i, block) in ir.blocks.iter().enumerate() {
            let code = self.context.append_basic_block(func, &format!(".b{}", i));
            self.builder.position_at_end(code);
            let mut has_returned = false;
            for op in block {
                assert!(!has_returned);
                match op {
                    Op::ConstInt { dest, value } => {
                        let val = number.const_int(*value, false);
                        registers.insert(dest, val.as_any_value_enum());
                    }
                    Op::Binary { dest, a, b, kind } => match kind {
                        BinaryOp::Add => {
                            let result = self.builder.build_int_add(
                                registers.get(a).unwrap().into_int_value(),
                                registers.get(b).unwrap().into_int_value(),
                                &format!("_var_{}", i),
                            );
                            registers.insert(dest, result.as_any_value_enum());
                        }
                        _ => todo!(),
                    },
                    Op::Return { value } => {
                        match value {
                            None => self.builder.build_return(None),
                            Some(value) => self.builder.build_return(Some(
                                &registers.get(value).unwrap().into_int_value(),
                            )),
                        };
                        has_returned = true;
                    }
                    _ => todo!(),
                }
            }
        }

        assert_eq!(ir.sig.returns, ValueType::U64);
        assert!(ir.sig.args.is_empty());
        self.module.verify().unwrap();
        type GetInt = unsafe extern "C" fn() -> u64;
        let function: JitFunction<GetInt> = unsafe {
            self.execution_engine
                .get_function(ir.sig.name.as_str())
                .unwrap()
        };

        unsafe { function.call() }
    }
}
