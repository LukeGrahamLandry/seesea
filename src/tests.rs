use inkwell::context::Context;
use inkwell::execution_engine::UnsafeFunctionPointer;
use inkwell::module::Module;
use inkwell::OptimizationLevel;
use std::rc::Rc;

use crate::asm::llvm::LlvmFuncGen;
use crate::scanning::Scanner;
use crate::{ast, ir};

#[test]
fn src_to_ast_to_ir() {
    no_args_full_pipeline(
        "
long main(){
    long x = 5;
    long y = 10;
    long z = x + y;
    return z;
}
    ",
        15,
    );
}

#[test]
fn if_statement() {
    no_args_full_pipeline(
        "
long main(){
    long x = 5;
    long y = 10;
    long z = 15;
    if (x > y) {
        return x;
    } else {
        return y;
    }
}
    ",
        10,
    );
}

#[test]
fn if_statement_with_mutation() {
    no_args_full_pipeline(
        "
long main(){
    long x = 5;
    long y = 10;
    long z = 0; 
    if (y < x) {
        x = z + 1;
    }
    return x;
}
    ",
        5,
    );
    no_args_full_pipeline(
        "
long main(){
    long x = 5;
    long y = 10;
    long z = 0; 
    if (y > x) {
        x = z + 1;
        y = 25;
        z = 20;
    }
    return x;
}
    ",
        1,
    );
}

#[test]
fn function_args() {
    let src = "
long max(long a, long b){
    if (a > b) {
        return a;
    } else {
        return b;
    }
}
    ";

    type Func = unsafe extern "C" fn(u64, u64) -> u64;
    compile_then(src, |max: Func| {
        let answer = unsafe { max(155, 20) };
        assert_eq!(answer, 155);
        let answer = unsafe { max(15, 200) };
        assert_eq!(answer, 200);
    });

    // Lying about the signature for science purposes.
    // It just casts the bits and does an unsigned comparison.
    // So negative numbers are highest because the sign bit is set.
    type EvilFunc = unsafe extern "C" fn(i64, i64) -> i64;
    compile_then(src, |max: EvilFunc| {
        let answer = unsafe { max(-10, 9999) };
        assert_eq!(answer, -10);
    });
}

fn no_args_full_pipeline(src: &str, expected: u64) {
    type NoArgToU64 = unsafe extern "C" fn() -> u64;
    compile_then(src, |function: NoArgToU64| {
        let answer = unsafe { function() };
        assert_eq!(answer, expected);
    });
}

// Wildly unsafe! For fuck sake don't put the fn pointer somewhere.
fn compile_then<F: UnsafeFunctionPointer>(src: &str, action: impl FnOnce(F)) {
    println!("{}", src);
    let scan = Scanner::new(src);
    println!("{:?}", scan);
    let ast = ast::Module::from(scan);
    println!("{:?}", ast);
    let ir = ir::Module::from(ast).functions[0].clone();
    println!("{:?}", ir);
    let context = Context::create();
    let module = context.create_module("max");
    let execution_engine = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .unwrap();

    let codegen = LlvmFuncGen::new(&module);
    let function = unsafe { codegen.compile_function::<F>(ir, &execution_engine) };
    println!("=== LLVM IR ===");
    println!("{}", module.to_string());
    println!("========");

    action(function);
}

// short circuiting
//
// boolean _0 = a || b
//
// boolean _0 = false;
// if (a) _0 = true;
// else if (b) _0 = true;
//
// boolean _0 = a && b;
//
// boolean _0 = true;
// if (!a) _0 = false;
// else if (!b) _0 = false;
