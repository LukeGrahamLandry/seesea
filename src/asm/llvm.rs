use crate::ir::{Func, Op, Ssa};
use crate::parse::BinaryOp;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::types::IntType;
use inkwell::values::{AnyValue, AnyValueEnum, IntMathValue, IntValue};
use inkwell::OptimizationLevel;
use std::collections::HashMap;

pub struct LlvmGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> LlvmGen<'ctx> {
    pub fn compile(&mut self, ir: Func) -> u64 {
        let t = self.context.void_type().fn_type(&[], false);
        let func = self.module.add_function("test", t, None);
        let number = self.context.i64_type();
        let mut registers = HashMap::<&Ssa, AnyValueEnum>::new();
        for (i, block) in ir.blocks.iter().enumerate() {
            let mut code = self
                .context
                .append_basic_block(func, &format!("_block_{}", i));
            self.builder.position_at_end(code);
            for op in block {
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
                            None => todo!(),
                            Some(value) => self.builder.build_return(Some(
                                &registers.get(value).unwrap().into_int_value(),
                            )),
                            // TODO: assert block is over now.
                        };
                    }
                    _ => todo!(),
                }
            }
        }

        type GetInt = unsafe extern "C" fn() -> u64;
        let function: JitFunction<GetInt> =
            unsafe { self.execution_engine.get_function("test").unwrap() };

        unsafe { function.call() }
    }
}

// #[test]
pub fn add_numbers() {
    let mut ir = Func::default();
    let block = ir.new_block();
    let a = ir.constant_int(block, 5);
    let b = ir.constant_int(block, 10);
    let dest = ir.next_var();
    ir.push(
        block,
        Op::Binary {
            dest,
            a,
            b,
            kind: BinaryOp::Add,
        },
    );
    ir.push(block, Op::Return { value: Some(dest) });

    let context = Context::create();
    let module = context.create_module("sum");
    let execution_engine = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .unwrap();
    let mut codegen = LlvmGen {
        context: &context,
        module,
        builder: context.create_builder(),
        execution_engine,
    };

    assert_eq!(codegen.compile(ir), 15);
    println!("{}", codegen.module.to_string());
}
