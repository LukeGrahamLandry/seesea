use crate::test_logic::TestCase;
use std::cell::RefCell;

// TODO: move the code into separate files in ../tests?
pub fn get_tests() -> Vec<TestCase> {
    let test_data = RefCell::new(vec![]);
    let no_args_run_main = |src: &str, expected: u64, name: &str| {
        test_data.borrow_mut().push(TestCase::NoArgsRunMain {
            src: src.to_string(),
            expected,
            name: name.to_string(),
        })
    };

    let int_to_int_run_main = |src: &str, input: u64, expected: u64, name: &str| {
        test_data.borrow_mut().push(TestCase::IntToIntRunMain {
            src: src.to_string(),
            input,
            expected,
            name: name.to_string(),
        })
    };

    // #[test]
    // fn src_to_ast_to_ir() {
    // language=c
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
        "src_to_ast_to_ir",
    );
    // }
    //
    // #[test]
    // fn if_statement() {
    // language=c
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
        "if_statement",
    );
    // }
    //
    // #[test]
    // fn if_statement_with_mutation() {
    // language=c
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
    no_args_run_main(&less, 5, "if_statement_with_mutation");
    no_args_run_main(&greater, 1, "if_statement_with_mutation2");
    // }
    //
    // #[test]
    // fn scopes() {
    // language=c
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
        "scopes",
    );
    // }

    //
    // #[test]
    // fn if_statement_with_mutation_in_else() {
    // language=c
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
    no_args_run_main(src, 0, "if_statement_with_mutation_in_else");
    // }
    //
    // #[test]
    // fn declare_in_else() {
    // language=c
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
    no_args_run_main(src, 0, "declare_in_else");
    // }
    //
    // #[test]
    // fn while_loop() {
    // language=c
    let src = "
long main(){
    long x = 0;
    while (x < 10) {
        x = x + 1;
    }
    return x;
}
    ";
    no_args_run_main(src, 10, "while_loop");
    // }
    //
    // #[test]
    // fn nested_while_loop_var() {
    // Since a variable is declared inside a loop, this fails if emitting phi nodes doesn't know about scopes closing and tries to bubble up dead variables.
    // language=c
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
    no_args_run_main(src, 9, "nested_while_loop_var");
    // }
    //
    // #[test]
    // fn mutate_in_if_condition() {
    // language=c
    let src = "
long main(){
    long x = 0;
    if ((x = 5) > 0){
        x = x + 1;
    }
    return x;
}
    ";
    no_args_run_main(src, 6, "mutate_in_if_condition");
    // }
    //
    // #[test]
    // fn mutate_in_nested_if_condition() {
    // language=c
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
    no_args_run_main(src, 7, "mutate_in_nested_if_condition");
    // }
    //
    // #[test]
    // fn mutate_in_while_condition() {
    // this loop relies on mutation in the condition to terminate
    // ie. condition sees condition's changes
    // language=c
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
    no_args_run_main(src, 9, "mutate_in_while_condition");
    // }
    //
    // #[test]
    // fn false_loop_condition_mutates() {
    // language=c
    let src = "
long main(){
    long y = 10;
    long x = 0;
    while ((y = 1 - x) > 5) {
        x = 10;
    }
    return y + x;
}
    ";

    no_args_run_main(src, 1, "false_loop_condition_mutates");
    // }
    //
    // #[test]
    // fn body_sees_conditions_changes() {
    // language=c
    let src = "
long main(){
    long y = 0;
    long z = 0;
    while ((y = y + 1) < 5) {
        z = z + y;
    }
    return y + z;
}
    ";
    no_args_run_main(src, 15, "body_sees_conditions_changes");
    // }
    //
    // #[test]
    // fn loop_condition_body_mutations_overlap() {
    // When they overlap, it needs to prioritise the condition's change coming out of the loop because that's the only one that will run when it exits.
    // Will need to revisit this when I add a break statement.
    // language=c
    let src = "
long main(){
    long y = 0;
    while ((y = y + 1) < 10) {
        y = y + 1;
    }
    return y;
}
    ";

    no_args_run_main(src, 11, "loop_condition_body_mutations_overlap");
    // }
    //
    // #[test]
    // fn struct_defs() {
    // language=c
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
    no_args_run_main(src, 15, "struct_defs");
    // }
    //
    // #[test]
    // fn struct_field_addr() {
    // language=c
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
    no_args_run_main(src, 5, "struct_field_addr");
    // }
    //
    // #[test]
    // fn printf_variadic_args() {
    // language=c
    let src = r#"
int printf(char* format, ...);
long main(){
    long number = 12345;
    printf("hello world!!!! %d", number);
    return 0;
}
    "#;
    // TODO: how to capture results from printf in jit execution engine? can probably define a function on it.
    no_args_run_main(src, 0, "printf_variadic_args");
    // }
    //
    //
    // #[test]
    // fn mul_div() {
    // language=c
    let src = "
long main(){
    return (2 * 3) / 6;
}
    ";

    no_args_run_main(src, 1, "mul_div");
    // }
    //
    // #[test]
    // fn allocation() {
    // language=c
    let src = "
void* malloc(long size);
void free(void* ptr);

long* t(long start){
    long* x = malloc(sizeof(long));
    *x = 1;
    return x;
}

long main()
{
    long* ptr = t(5);
    long y = *ptr;
    free(ptr);
    return y;
}
    ";

    no_args_run_main(src, 1, "allocation");
    // }
    //
    // #[test]
    // fn ptr_math() {
    // language=c
    let src = "
void* malloc(long size);
void free(void* ptr);

long main()
{
    long* first = malloc(sizeof(long) * 2);
    *first = 1;
    long* second = first + sizeof(long);
    *second = 2;
    long result = *first + *second;
    free(first);
    return result;
}
    ";

    no_args_run_main(src, 3, "ptr_math");
    // }
    //
    // #[test]
    // fn ptr_to_struct() {
    // language=c
    let src = "
struct Thing {
    long a;
    long b;
};

long main(){
    struct Thing z;
    z.b = 5;
    struct Thing* zz = &z;
    (*zz).a = 10;
    return z.a + (*zz).b;
}
    ";
    no_args_run_main(src, 15, "ptr_to_struct");
    // }
    //
    // #[test]
    // fn typedef() {
    // language=c
    let src = "
typedef long i64;
typedef struct Thing {
    i64 a;
    long b;
} Thing;

long main(){
    Thing z;
    z.b = 5;
    return z.b;
}
    ";
    no_args_run_main(src, 5, "typedef");
    // }
    //
    // #[test]
    // fn array_list() {
    // language=c
    let src = "
long main(){
    return test();
}
    ";
    let src = &[include_str!("../tests/array_list.c"), src].join("");
    no_args_run_main(src, 0, "array_list");

    // #[test]
    // fn pointers() {
    //     // language=c
    let src = "
long main(long a){
    long x = a + 5;
    long* ax = &x;
    long temp = *ax;
    *ax = temp + 10;
    return x;
}
    ";
    int_to_int_run_main(src, 10, 25, "pointers");

    // }

    test_data.into_inner()
}

// TODO
// #[test]
// fn nested_ifs() {
//     // This failed when I was mutating the block pointer incorrectly.
//     // language=c
//     let src = "
// long main(long a){
//     long x = a + 5;
//     if (x > 11){
//         return 99;
//     } else if (x > 5) {
//         long y = 7;
//         if (x > y) {
//             y = y + x;
//         }
//         if (x < y) {
//             return y;
//         }
//     }
//     return x;
// }
//     ";
//
//     let ir = compile_module(src, "nested_ifs");
//     let vm_result = Vm::eval_int_args(&ir, "main", &[5]).to_int();
//     assert_eq!(vm_result, 17);
//     type Func = unsafe extern "C" fn(u64) -> u64;
//     compile_and_run::<Func, _>(&ir, "main", |func| {
//         assert_eq!(unsafe { func(5) }, 17);
//     });
// }
//
// #[test]
// fn dont_emit_phi_nodes_referencing_blocks_that_jump_instead_of_falling_through() {
//     // LLVM validation failed with "PHINode should have one entry for each predecessor of its parent basic block!\n  %6 = phi i64 [ %5, %.b4 ], [ 7, %.b5 ]"
//     // language=c
//     let src = "
// long main(long a){
//     long x = a + 5;
//     if (x > 11){
//         return 99;
//     } else if (x > 5) {
//         long y = 7;
//         if (x > y) {
//             y = y + x;
//             return 999;
//         }
//         if (x < y) {
//             return y;
//         }
//     }
//     return x;
// }
//     ";
//     let ir = compile_module(
//         src,
//         "dont_emit_phi_nodes_referencing_blocks_that_jump_instead_of_falling_through",
//     );
//     assert_eq!(Vm::eval_int_args(&ir, "main", &[5]).to_int(), 999);
//     type Func = unsafe extern "C" fn(u64) -> u64;
//     compile_and_run::<Func, _>(&ir, "main", |func| {
//         assert_eq!(unsafe { func(5) }, 999);
//     });
// }
//
// #[test]
// fn function_calls() {
//     // language=c
//     let src = "
// long max(long a, long b){
//     if (a > b) {
//         return a;
//     } else {
//         return b;
//     }
// }
// long tri_max(long a, long b, long c){
//     return max(max(a, b), c);
// }
//     ";
//
//     let ir = compile_module(src, "function_calls");
//     let cases = [
//         ([1u64, 2u64, 4u64].as_slice(), 4u64),
//         ([10u64, 20u64, 5u64].as_slice(), 20u64),
//     ];
//
//     vm_run_cases(&ir, "tri_max", &cases);
//     type Func = unsafe extern "C" fn(u64, u64, u64) -> u64;
//     compile_and_run::<Func, _>(&ir, "tri_max", |tri_max| {
//         for (args, answer) in cases {
//             let result = unsafe { tri_max(args[0], args[1], args[2]) };
//             assert_eq!(result, answer);
//         }
//     });
// }
//
// #[test]
// fn recursion() {
//     // language=c
//     let src = "
// long fib(long n){
//     if (n < 2) return 1;
//     return fib(n - 1) + fib(n - 2);
// }
//     ";
//
//     // 1 1 2 3 5 8
//     let cases = [([5u64].as_slice(), 8u64)];
//     let ir = compile_module(src, "recursion");
//
//     vm_run_cases(&ir, "fib", &cases);
//     type Func = unsafe extern "C" fn(u64) -> u64;
//     compile_and_run::<Func, _>(&ir, "fib", |fib| {
//         for (args, answer) in cases {
//             let result = unsafe { fib(args[0]) };
//             log!("args: {:?}. result: {}", args, result);
//             assert_eq!(result, answer);
//         }
//     });
// }
//

// #[test]
// fn math_dot_h_sin() {
//     let src = "
// double sin(double value);
// double main(){
//     double r = sin(3.1415926525897);
//     return r;
// }
//     ";
//     let ir = compile_module(src, "math_dot_h_sin");
//     assert!(Vm::eval_int_args(&ir, "main", &[]).to_float().abs() < 0.000001);
//     type Func = unsafe extern "C" fn() -> f64;
//     compile_and_run::<Func, _>(&ir, "main", |function| {
//         let answer = unsafe { function() };
//         assert!(answer.abs() < 0.000001);
//     });
// }
//
// #[test]
// fn int_cast() {
//     // language=c
//     let src = "
// long main(long start){
//     int a = (float) start;
//     double b = 300 + a;
//     a = a + b;
//     char c = a + 0;
//     return c;
// }";
//     let ir = compile_module(src, "int_cast");
//     type Func = unsafe extern "C" fn(u64) -> u64;
//     assert_eq!(Vm::eval(&ir, "main", &[VmValue::U64(5)]).to_int(), 54);
//     compile_and_run::<Func, _>(&ir, "main", |function| {
//         let answer = unsafe { function(5) };
//         assert_eq!(answer, 54);
//     });
// }
//
// #[test]
// fn float_compare() {
//     // language=c
//     let src = "
// long main(double a){
//     if (a > 0.5) {
//         return 3;
//     } else {
//         return 2;
//     }
// }
//     ";
//     let ir = compile_module(src, "float_compare");
//     assert_eq!(Vm::eval(&ir, "main", &[VmValue::F64(0.1)]).to_int(), 2);
//     type Func = unsafe extern "C" fn(f64) -> u64;
//     compile_and_run::<Func, _>(&ir, "main", |function| {
//         let answer = unsafe { function(0.1) };
//         assert_eq!(answer, 2);
//     });
// }
//
//
// #[test]
// fn function_args() {
//     // language=c
//     let src = "
// long max(long a, long b){
//     if (a > b) {
//         return a;
//     } else {
//         return b;
//     }
// }
//     ";
//     let cases = [([155, 20].as_slice(), 155), ([15, 200].as_slice(), 200)];
//     let ir = compile_module(src, "function_args");
//
//     vm_run_cases(&ir, "max", &cases);
//     type Func = unsafe extern "C" fn(u64, u64) -> u64;
//     compile_and_run::<Func, _>(&ir, "max", |max| {
//         for (args, answer) in cases {
//             assert_eq!(unsafe { max(args[0], args[1]) }, answer);
//         }
//     });
//
//     // Lying about the signature for science purposes.
//     // It just casts the bits and does an unsigned comparison.
//     // So negative numbers are highest because the sign bit is set.
//     type EvilFunc = unsafe extern "C" fn(i64, i64) -> i64;
//     compile_and_run::<EvilFunc, _>(&ir, "max", |max| {
//         let answer = unsafe { max(-10, 9999) };
//         assert_eq!(answer, -10);
//     });
// }