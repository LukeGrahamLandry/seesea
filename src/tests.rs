use inkwell::context::Context;
use inkwell::execution_engine::UnsafeFunctionPointer;
use inkwell::module::Module;
use inkwell::OptimizationLevel;
use std::fmt::Debug;
use std::fs;
use std::rc::Rc;

use crate::asm::llvm::LlvmFuncGen;
use crate::scanning::Scanner;
use crate::vm::Vm;
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
fn scopes() {
    no_args_full_pipeline(
        "
long main(){
    long x = 2;
    long y = 3;
    {
        long y = 5;
        x = x + y;
    }
    {
        x = x + y;
    }
    {
        long x = 50;
        x = x + 999;
        if (x > y){
            long x = 20;
            y = x;
        }
    }
    x = x + y;
    
    return x;
}
    ",
        30,
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

    let func = compile_module(src);
    assert_eq!(Vm::eval(&func, "max", &[155, 20]), Some(155));
    assert_eq!(Vm::eval(&func, "max", &[15, 200]), Some(200));
}

#[test]
fn nested_ifs() {
    // This failed when I was mutating the block pointer incorrectly.
    let src = "
long main(long a){
    long x = a + 5;
    if (x > 11){
        return 99;
    } else if (x > 5) {
        long y = 7;
        if (x > y) {
            y = y + x;
        }
        if (x < y) {
            return y;
        }
    }
    return x;
}
    ";
    let vm_result = Vm::eval(&compile_module(src), "main", &[5]).unwrap();
    type Func = unsafe extern "C" fn(u64) -> u64;
    compile_then(src, |func: Func| {
        assert_eq!(unsafe { func(5) }, 17);
    });
    assert_eq!(vm_result, 17);
}

#[test]
fn dont_emit_phi_nodes_referencing_blocks_that_jump_instead_of_falling_through() {
    // LLVM validation failed with "PHINode should have one entry for each predecessor of its parent basic block!\n  %6 = phi i64 [ %5, %.b4 ], [ 7, %.b5 ]"
    let src = "
long main(long a){
    long x = a + 5;
    if (x > 11){
        return 99;
    } else if (x > 5) {
        long y = 7;
        if (x > y) {
            y = y + x;
            return 999;
        }
        if (x < y) {
            return y;
        }
    }
    return x;
}
    ";
    let vm_result = Vm::eval(&compile_module(src), "main", &[5]).unwrap();
    assert_eq!(vm_result, 999);
    type Func = unsafe extern "C" fn(u64) -> u64;
    compile_then(src, |func: Func| {
        assert_eq!(unsafe { func(5) }, 999);
    });
}

#[test]
fn function_calls() {
    let src = "
long tri_max(long a, long b, long c){
    return max(max(a, b), c);
}
long max(long a, long b){
    if (a > b) {
        return a;
    } else {
        return b;
    }
}
    ";

    let cases = [([1u64, 2u64, 4u64], 4u64)];

    // TODO: get the right function
    // type Func = unsafe extern "C" fn(u64, u64, u64) -> u64;
    // compile_then(src, |tri_max: Func| {
    //     for (args, answer) in cases {
    //         let result = unsafe { tri_max(args[0], args[1], args[2]) };
    //         assert_eq!(result, answer);
    //     }
    // });

    let module = compile_module(src);
    for (args, answer) in cases {
        assert_eq!(Vm::eval(&module, "tri_max", &args), Some(answer));
    }
}

fn no_args_full_pipeline(src: &str, expected: u64) {
    type NoArgToU64 = unsafe extern "C" fn() -> u64;
    compile_then(src, |function: NoArgToU64| {
        let answer = unsafe { function() };
        assert_eq!(answer, expected);
    });
    assert_eq!(Vm::eval(&compile_module(src), "main", &[]), Some(expected));
}

// Wildly unsafe! For fuck sake don't put the fn pointer somewhere.
fn compile_then<F: UnsafeFunctionPointer>(src: &str, action: impl FnOnce(F)) {
    println!("{}", src);
    let scan = Scanner::new(src, "test_code".into());
    println!("{:?}", scan);
    let ast = ast::Module::from(scan);
    println!("{:?}", ast);
    let context = Context::create();
    let module = context.create_module(ast.name.as_str());
    let ir = ir::Module::from(ast).functions[0].clone();
    println!("{:?}", ir);
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

fn save<T: Debug>(value: T, filename: &str) {
    fs::write(filename, format!("{:?}", value)).unwrap();
}

fn get_first_function(src: &str) -> ir::Function {
    compile_module(src).functions[0].clone()
}

fn compile_module(src: &str) -> ir::Module {
    println!("{}", src);
    let scan = Scanner::new(src, "test_code".into());
    println!("{:?}", scan);
    let ast = ast::Module::from(scan);
    println!("{:?}", ast);
    ir::Module::from(ast)
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
