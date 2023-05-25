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
use inkwell::{IntPredicate, OptimizationLevel};
use std::collections::HashMap;

pub struct LlvmGen<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> LlvmGen<'ctx> {
    // TODO: the whole program shares one module
    // TODO: module names?
    pub fn compile(&mut self, ir: Function) -> u64 {
        let t = self.context.i64_type().fn_type(&[], false);
        let func = self.module.add_function(ir.sig.name.as_str(), t, None);
        let number = self.context.i64_type();
        let mut registers = HashMap::<&Ssa, AnyValueEnum>::new();
        let blocks = ir
            .blocks
            .iter()
            .enumerate()
            .map(|(i, _)| self.context.append_basic_block(func, &format!(".b{}", i)))
            .collect::<Vec<_>>();
        for (i, block) in ir.blocks.iter().enumerate() {
            let code = blocks[i];
            self.builder.position_at_end(code);
            let mut has_returned = false;

            if block.is_empty() {
                // TODO: get rid of garbage blocks before it gets to llvm.
                //       but it crashes with invalid blocks that don't jump anywhere so temp fix.
                //       llvm optimises it out anyway.
                let garbage = number.const_int(3141592, false);
                self.builder.build_return(Some(&garbage));
                continue;
            }

            for (op_index, op) in block.iter().enumerate() {
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
                                &format!("_var_{}", op_index),
                            );
                            registers.insert(dest, result.as_any_value_enum());
                        }
                        BinaryOp::GreaterThan => {
                            let result = self.builder.build_int_compare(
                                IntPredicate::UGT,
                                registers.get(a).unwrap().into_int_value(),
                                registers.get(b).unwrap().into_int_value(),
                                &format!("_var_{}", op_index),
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
                    Op::AlwaysJump(target) => {
                        // TODO: factor out a FunctionBuilder that gives you type safety over these index -> block conversions.
                        self.builder
                            .build_unconditional_branch(blocks[target.index()]);
                    }
                    Op::Jump {
                        condition,
                        if_true,
                        if_false,
                    } => {
                        let condition = registers.get(condition).unwrap().into_int_value();
                        self.builder.build_conditional_branch(
                            condition,
                            blocks[if_true.index()],
                            blocks[if_false.index()],
                        );
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
