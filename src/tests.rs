use inkwell::context::Context;
use inkwell::execution_engine::{JitFunction, UnsafeFunctionPointer};
use inkwell::OptimizationLevel;
use std::fs::File;
use std::io::Write;
use std::mem::size_of;

use crate::asm::llvm::LlvmFuncGen;
use crate::ir::Op;
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
    let vm_result = Vm::eval(&ir, "main", &[5]).to_int();
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
    assert_eq!(Vm::eval(&ir, "main", &[5]).to_int(), 999);
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
    assert_eq!(Vm::eval(&ir, "main", &[10]).to_int(), 25);
    type Func = unsafe extern "C" fn(u64) -> u64;
    llvm_run::<Func, _>(&ir, "main", |func| assert_eq!(unsafe { func.call(10) }, 25));
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

#[test]
fn declare_in_else() {
    let src = "
long main(){
    if (1 < 0) {
        long x = 5;
    } else {
        long y = 10;
    }
    return 0;
}
    ";
    no_args_run_main(src, 0);
}

#[test]
fn while_loop() {
    let src = "
long main(){
    long x = 0;
    while (x < 10) {
        x = x + 1;
    }
    return x;
}
    ";
    no_args_run_main(src, 10);
}

#[test]
fn nested_while_loop_var() {
    // Since a variable is declared inside a loop, this fails if emitting phi nodes doesn't know about scopes closing and tries to bubble up dead variables.
    let src = "
long main(){
  long x = 0;
    long z = 0;
    while (z < 3) {
        z = z + 1;
        long y = 0;
        while (y < 3) {
            x = x + 1;
            y = y + 1;
        }
    }
    return x;
}
    ";
    no_args_run_main(src, 9);
}

#[test]
fn mutate_in_if_condition() {
    let src = "
long main(){
    long x = 0;
    if ((x = 5) > 0){
        x = x + 1;
    }
    return x;
}
    ";
    no_args_run_main(src, 6);
}

#[test]
fn mutate_in_nested_if_condition() {
    let src = "
long main(){
    long x = 0;
    long y = 0;
    if ((x = 5) > 0){
        x = x + 1;
        if ((y = 4) < 10){
            y = 1;
        }
    }
    return x + y;
}
    ";
    no_args_run_main(src, 7);
}

#[test]
fn mutate_in_while_condition() {
    // this loop relies on mutation in the condition to terminate
    let src = "
long main(){
    long y = 0;
    long z = 0;
    while ((y = y + 1) < 5) {
        z = z + 1;
    }
    return y + z;
}
    ";
    no_args_run_main(src, 9);
}

#[test]
fn false_loop_condition_mutates() {
    let src = "
long main(){
    long y = 10;
    while ((y = 1) > 5) {
        y = 15;
    }
    return y;
}
    ";

    no_args_run_main(src, 1);
}

#[test]
fn struct_defs() {
    let src = "
struct Thing {
    long a;
    long* b;
};

long main(){
    long x = 10;
    long* y = &x;
    struct Thing z;
    z.a = x;
    z.b = y;
    *z.b = 5;
    return x + z.a;
}
    ";
    no_args_run_main(src, 15);
}

#[test]
fn struct_field_addr() {
    let src = "
struct Thing {
    long a;
    long b;
};

long main(){
    struct Thing z;
    z.a = 10;
    z.b = 0;
    long* za = &z.a;
    *za = 5;
    return z.a + z.b;
}
    ";
    no_args_run_main(src, 5);
}

#[test]
fn printf_variadic_args() {
    let src = r#"
int printf(char* format, ...);
long main(){
    long number = 12345;
    printf("hello world!!!! %d", number);
    return 0;
}
    "#;
    // TODO: how to capture results from printf in jit execution engine? can probably define a function on it.
    no_args_run_main(src, 0);
}

#[test]
fn math_dot_h_sin() {
    let src = "
double sin(double value);
double main(){
    double r = sin(3.1415926525897);
    return r;
}
    ";
    let ir = compile_module(src);
    assert!(Vm::eval(&ir, "main", &[]).to_float().abs() < 0.000001);
    type Func = unsafe extern "C" fn() -> f64;
    llvm_run::<Func, _>(&ir, "main", |function| {
        let answer = unsafe { function.call() };
        assert!(answer.abs() < 0.000001);
    });
    println!("{}", size_of::<Op>());
}

#[test]
fn int_cast() {
    let src = "
long main(long start){
    int a = (float) start;
    double b = 300 + a;
    a = a + b;
    char c = a + 0;
    return c;
}
    ";
    type Func = unsafe extern "C" fn(u64) -> u64;
    llvm_run::<Func, _>(&compile_module(src), "main", |function| {
        let answer = unsafe { function.call(5) };
        assert_eq!(answer, 54);
    });
}

// do malloc next!

fn no_args_run_main(src: &str, expected: u64) {
    let ir = compile_module(src);
    assert_eq!(Vm::eval(&ir, "main", &[]).to_int(), expected);
    type Func = unsafe extern "C" fn() -> u64;
    llvm_run::<Func, _>(&ir, "main", |function| {
        let answer = unsafe { function.call() };
        assert_eq!(answer, expected);
    });
}

fn vm_run_cases(ir: &ir::Module, func_name: &str, cases: &[(&[u64], u64)]) {
    for (args, answer) in cases {
        assert_eq!(Vm::eval(ir, func_name, args).to_int(), *answer);
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
    LlvmFuncGen::new(&module).compile_all(ir);
    let func = unsafe { execution_engine.get_function::<F>(func_name).unwrap() };
    action(func);
    // module.verify().unwrap();
}

#[allow(unused)]
fn llvm_compile(ir: &ir::Module, filename: &str) {
    assert!(ir.get_func("main").is_some(), "Function 'main' not found.");
    let context = Context::create();
    let module = context.create_module(&ir.name);
    LlvmFuncGen::new(&module).compile_all(ir);
    let mut file = File::create(format!("target/{}.ll", filename)).unwrap();
    file.write_all(module.to_string().as_bytes()).unwrap();
    // cd target
    // llc -filetype=obj struct_field_addr.ll && /usr/bin/clang struct_field_addr.o -o struct_field_addr && ./struct_field_addr
    // llc -filetype=obj printf_test.ll && /usr/bin/clang printf_test.o -o printf_test && ./printf_test
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
