//! IR -> LLVM IR

use crate::ast::{BinaryOp, FuncSignature, Program, ValueType};
use crate::ir::{five_plus_ten, Function, Op, Ssa};
use crate::scanning::Scanner;
use crate::{ast, ir};
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
    pub fn compile(&mut self, ir: Function) -> u64 {
        let t = self.context.void_type().fn_type(&[], false);
        let func = self.module.add_function("test", t, None);
        let number = self.context.i64_type();
        let mut registers = HashMap::<&Ssa, AnyValueEnum>::new();
        for (i, block) in ir.blocks.iter().enumerate() {
            let mut code = self
                .context
                .append_basic_block(func, &format!("_block_{}", i));
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

        type GetInt = unsafe extern "C" fn() -> u64;
        let function: JitFunction<GetInt> =
            unsafe { self.execution_engine.get_function("test").unwrap() };

        unsafe { function.call() }
    }
}

#[test]
fn just_ir() {
    eval_expect(five_plus_ten(), 15);
}

#[test]
fn ast_to_ir() {
    let ast = ast::five_plus_ten();
    println!("{:?}", ast);
    let ir = ir::Module::from(Program {
        functions: vec![ast],
    });
    eval_expect(ir.functions[0].clone(), 15);
}

#[test]
fn src_to_ast_to_ir() {
    let src = "
long main(){
    long x = 5;
    long y = 10;
    long z = x + y;
    return z;
}
    ";
    let mut scan = Scanner::new(src);
    println!("{:?}", scan);

    let scan = Scanner::new(src);
    let ast = Program::from(scan);
    println!("{:?}", ast);
    let ir = ir::Module::from(ast);
    eval_expect(ir.functions[0].clone(), 15);
}

pub fn add_numbers() {}

pub fn eval_expect(ir: Function, result: u64) {
    println!("{:?}", ir);
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

    assert_eq!(codegen.compile(ir), result);
    println!("=== LLVM IR ===");
    println!("{}", codegen.module.to_string());
    println!("========");
}
