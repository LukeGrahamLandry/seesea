use inkwell::context::Context;
use inkwell::execution_engine::{JitFunction, UnsafeFunctionPointer};
use inkwell::OptimizationLevel;

use crate::asm::llvm::LlvmFuncGen;
use crate::scanning::Scanner;
use crate::vm::Vm;
use crate::{ast, ir};

#[test]
fn src_to_ast_to_ir() {
    no_args_run_main(
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
    no_args_run_main(
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
    let src = "
long main(){
    long x = 5;
    long y = 10;
    long z = 0; 
    if (COND) {
        x = z + 1;
        y = 25;
        z = 20;
    }
    return x;
}
    ";
    let less = src.replace("COND", "y < x");
    let greater = src.replace("COND", "y > x");
    no_args_run_main(&less, 5);
    no_args_run_main(&greater, 1);
}

#[test]
fn scopes() {
    no_args_run_main(
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
    let cases = [([155, 20].as_slice(), 155), ([15, 200].as_slice(), 200)];
    let ir = compile_module(src);

    vm_run_cases(&ir, "max", &cases);
    type Func = unsafe extern "C" fn(u64, u64) -> u64;
    llvm_run::<Func, _>(&ir, "max", |max| {
        for (args, answer) in cases {
            assert_eq!(unsafe { max.call(args[0], args[1]) }, answer);
        }
    });

    // Lying about the signature for science purposes.
    // It just casts the bits and does an unsigned comparison.
    // So negative numbers are highest because the sign bit is set.
    type EvilFunc = unsafe extern "C" fn(i64, i64) -> i64;
    llvm_run::<EvilFunc, _>(&ir, "max", |max| {
        let answer = unsafe { max.call(-10, 9999) };
        assert_eq!(answer, -10);
    });
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

    let ir = compile_module(src);
    let vm_result = Vm::eval(&ir, "main", &[5]).unwrap();
    assert_eq!(vm_result, 17);
    type Func = unsafe extern "C" fn(u64) -> u64;
    llvm_run::<Func, _>(&ir, "main", |func| {
        assert_eq!(unsafe { func.call(5) }, 17);
    });
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
    let ir = compile_module(src);
    assert_eq!(Vm::eval(&ir, "main", &[5]), Some(999));
    type Func = unsafe extern "C" fn(u64) -> u64;
    llvm_run::<Func, _>(&ir, "main", |func| {
        assert_eq!(unsafe { func.call(5) }, 999);
    });
}

#[test]
fn function_calls() {
    let src = "
long max(long a, long b){
    if (a > b) {
        return a;
    } else {
        return b;
    }
}
long tri_max(long a, long b, long c){
    return max(max(a, b), c);
}
    ";

    let ir = compile_module(src);
    let cases = [
        ([1u64, 2u64, 4u64].as_slice(), 4u64),
        ([10u64, 20u64, 5u64].as_slice(), 20u64),
    ];

    vm_run_cases(&ir, "tri_max", &cases);
    type Func = unsafe extern "C" fn(u64, u64, u64) -> u64;
    llvm_run::<Func, _>(&ir, "tri_max", |tri_max| {
        for (args, answer) in cases {
            let result = unsafe { tri_max.call(args[0], args[1], args[2]) };
            assert_eq!(result, answer);
        }
    });
}

#[test]
fn recursion() {
    let src = "
long fib(long n){
    if (n < 2) return 1;
    return fib(n - 1) + fib(n - 2);
}
    ";

    // 1 1 2 3 5 8
    let cases = [([5u64].as_slice(), 8u64)];
    let ir = compile_module(src);

    vm_run_cases(&ir, "fib", &cases);
    type Func = unsafe extern "C" fn(u64) -> u64;
    llvm_run::<Func, _>(&ir, "fib", |fib| {
        for (args, answer) in cases {
            let result = unsafe { fib.call(args[0]) };
            println!("args: {:?}. result: {}", args, result);
            assert_eq!(result, answer);
        }
    });
}

#[test]
fn pointers() {
    let src = "
long main(long a){
    long x = a + 5;
    long* ax = &x;
    long temp = *ax;
    *ax = temp + 10;
    return x;
}
    ";

    let ir = compile_module(src);
    assert_eq!(Vm::eval(&ir, "main", &[10]), Some(25));
    type Func = unsafe extern "C" fn(u64) -> u64;
    llvm_run::<Func, _>(&ir, "main", |fib| assert_eq!(unsafe { fib.call(10) }, 25));
}

#[test]
fn if_statement_with_mutation_in_else() {
    let src = "
long main(){
    long x = 5;
    long y = 10;
    long z = 0; 
    if (x > y) {
        y = 0;
    } else {
        x = 0;
    }
    return x;
}
    ";
    no_args_run_main(src, 0);
}

fn no_args_run_main(src: &str, expected: u64) {
    let ir = compile_module(src);
    assert_eq!(Vm::eval(&ir, "main", &[]), Some(expected));
    type Func = unsafe extern "C" fn() -> u64;
    llvm_run::<Func, _>(&ir, "main", |function| {
        let answer = unsafe { function.call() };
        assert_eq!(answer, expected);
    });
}

fn vm_run_cases(ir: &ir::Module, func_name: &str, cases: &[(&[u64], u64)]) {
    for (args, answer) in cases {
        assert_eq!(Vm::eval(ir, func_name, args), Some(*answer));
    }
}

// This is unsafe! But since its just in tests and calling the function is unsafe anyway I don't really care.
// The caller MUST specify the right signature for F.
// TODO: is there a way I can reflect on the signature since I know what it should be from the ir? maybe make this a macro?
#[cfg(test)]
fn llvm_run<F, A>(ir: &ir::Module, func_name: &str, action: A)
where
    F: UnsafeFunctionPointer,
    // JitFunction instead of direct F to hold the lifetime of our exec engine.
    A: FnOnce(JitFunction<F>),
{
    assert!(ir.get_func(func_name).is_some(), "Function not found.");
    let context = Context::create();
    let module = context.create_module(&ir.name);
    let execution_engine = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .unwrap();
    let mut codegen = LlvmFuncGen::new(&module);
    codegen.compile_all(ir);
    println!("=== LLVM IR ====");
    println!("{}", module.to_string());
    println!("=========");
    let func = unsafe { execution_engine.get_function::<F>(func_name).unwrap() };
    action(func);
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
