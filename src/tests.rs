use crate::asm::cranelift::compile_object;
use crate::asm::llvm;
use crate::test_logic::*;
use std::fs;
use std::process::Command;

#[test]
fn simplest_return() {
    // language=c
    no_args_run_main(
        "
long main(){
    return 13;
}
    ",
        13,
        "simplest_return",
    );
}

#[test]
fn variable() {
    // language=c
    no_args_run_main(
        "
long main(){
    long x = 2;
    x = 5; 
    return x;
}
    ",
        5,
        "variable",
    );
}

#[test]
fn call() {
    // language=c
    no_args_run_main(
        "
long a(long b) {
    return b + 15;
}
long main(){
    return a(1);
}
    ",
        16,
        "call",
    );
}

#[test]
fn forward_declare() {
    // language=c
    no_args_run_main(
        "
long a(long b);
long main(){
    return a(1);
}
long a(long b) {
    return b + 15;
}
    ",
        16,
        "forward_declare",
    );
}

#[test]
fn call_malloc() {
    // language=c
    let src = "
void* malloc(long size);
void free(void* ptr);

long main(){
    long* ptr = malloc(sizeof(long));
    free(ptr);
    return 0;
}
    ";

    no_args_run_main(src, 0, "call_malloc");
}

#[test]
fn float_math() {
    // language=c
    let src = "
double main(){
    double x = 1.0;
    double y = 4.0 + x;
    double z = x / y;  // 0.2
    double a = 3.0 * 0.5;  // 1.5
    return z + a;
}
    ";
    no_arg_to_double_run_main(src, 1.7, "float_math");
}

#[test]
fn string_constant() {
    // language=c
    no_args_run_main(
        "
long main(){
    char* data = \"Hello World!\";
    long x = data[1];
    return x;
}
    ",
        'e' as u64,
        "string_constant",
    );
}

// This tests use of load_byte and store_byte in asm backend.
// The many unused chars
#[test]
fn load_store_char() {
    // language=c
    no_args_run_main(
        "
long main(){
    char _temp1 = 1;  // make sure there's junk on the stack
    char _temp2 = 2;
    char _temp3 = 3;
    char b = 101;
    long a = 18446744073709551615;
    a = b;
    return a;
}
    ",
        101,
        "load_store_char",
    );
}

#[test]
fn src_to_ast_to_ir() {
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
}

#[test]
fn if_statement() {
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
}

#[test]
fn if_statement_with_mutation() {
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
    no_args_run_main(&greater, 1, "if_statement_with_mutation_2");
}

#[test]
fn simple_if() {
    // language=c
    let src = "
long main(){
    if (COND) {
        return 4;
    } else {
        return 5;
    }
}
    ";
    let tgt = src.replace("COND", "15 > 5");
    let fgt = src.replace("COND", "5 > 15");
    let flt = src.replace("COND", "15 < 5");
    let tlt = src.replace("COND", "5 < 15");
    no_args_run_main(&tgt, 4, "simple_if_true_gt");
    no_args_run_main(&fgt, 5, "simple_if_false_gt");
    no_args_run_main(&tlt, 4, "simple_if_true_lt");
    no_args_run_main(&flt, 5, "simple_if_false_lt");
}

#[test]
fn scopes() {
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
}

#[test]
fn function_args() {
    // language=c
    let src = "
long main(long a, long b){
    if (a > b) {
        return a;
    } else {
        return b;
    }
}
    ";

    two_ints_to_int_run_main(src, 155, 20, 155, "function_args");
    two_ints_to_int_run_main(src, 15, 200, 200, "function_args2");
}

#[test]
fn nested_ifs() {
    // This failed when I was mutating the block pointer incorrectly.
    // language=c
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

    int_to_int_run_main(src, 5, 17, "nested_ifs");
}

#[test]
fn dont_emit_phi_nodes_referencing_blocks_that_jump_instead_of_falling_through() {
    // LLVM validation failed with "PHINode should have one entry for each predecessor of its parent basic block!\n  %6 = phi i64 [ %5, %.b4 ], [ 7, %.b5 ]"
    // language=c
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
    int_to_int_run_main(
        src,
        5,
        999,
        "dont_emit_phi_nodes_referencing_blocks_that_jump_instead_of_falling_through",
    );
}

#[test]
fn function_calls() {
    // language=c
    let src = "
long max(long a, long b){
    if (a > b) {
        return a;
    } else {
        return b;
    }
}
long main(long a, long b, long c){
    return max(max(a, b), c);
}
    ";

    three_ints_to_int_run_main(src, 1, 2, 4, 4, "function_calls");
    three_ints_to_int_run_main(src, 10, 20, 5, 20, "function_calls2");
}

#[test]
fn recursion() {
    // language=c
    let src = "
// fib
long main(long n){
    if (n < 2) return 1;
    return main(n - 1) + main(n - 2);
}
    ";

    // 1 1 2 3 5 8
    int_to_int_run_main(src, 5, 8, "recursion");
}

#[test]
fn pointers() {
    // language=c
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
}

#[test]
fn if_statement_with_mutation_in_else() {
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
}

#[test]
fn declare_in_else() {
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
}

#[test]
fn while_loop() {
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
}

#[test]
fn nested_while_loop_var() {
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
}

#[test]
fn mutate_in_if_condition() {
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
}

#[test]
fn mutate_in_nested_if_condition() {
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
}

#[test]
fn mutate_in_while_condition() {
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
}

#[test]
fn false_loop_condition_mutates() {
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
}

#[test]
fn body_sees_conditions_changes() {
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
}

#[test]
fn loop_condition_body_mutations_overlap() {
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
}

#[test]
fn struct_defs() {
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
}

#[test]
fn struct_decl_as_var_type() {
    // language=c
    let src = "
long main(){
    struct { int a; } b;
    b.a = 15;
    return b.a;
}
    ";
    no_args_run_main(src, 15, "struct_decl_as_var_type");
}

#[test]
fn struct_field_addr() {
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
}

#[cfg(not(feature = "cranelift"))]
#[test]
fn printf_variadic_args() {
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
}

#[test]
fn math_dot_h_sin() {
    let src = "
double sin(double value);
double main(){
    double r = sin(3.1415926525897);
    double max = 0.001;
    double min = 0.0 - max;
    if (r > min) {
        if (r < max) {
            return 0.1;
        }
    }
    return 999.0;
}
    ";

    no_arg_to_double_run_main(src, 0.1, "math_dot_h_sin");
}

#[test]
fn int_cast() {
    // language=c
    let src = "
long main(long start){
    int a = (float) start;
    double b = 300 + a;
    a = a + b;
    char c = a + 0;
    return c;
}";
    int_to_int_run_main(src, 5, 54, "int_cast");
}

#[test]
fn float_compare() {
    // language=c
    let src = "
long main(double a){
    if (a > 0.5) {
        return 3;
    } else {
        return 2;
    }
}
    ";

    double_to_int_run_main(src, 0.1, 2, "float_compare");
}

#[test]
fn mul_div() {
    // language=c
    let src = "
long main(){
    return (2 * 3) / 6;
}
    ";

    no_args_run_main(src, 1, "mul_div");
}

#[test]
fn sizeof() {
    // language=c
    let src = "
long main(){
    // TODO: strange implicit casting if you try to add these together in one expression?
    int a = (sizeof(long) == 8);
    int b = (sizeof(int) == 4);
    int c = (sizeof(double) == 8);
    int d = (sizeof(float) == 4);
    return a + b + c + d;
}
    ";

    no_args_run_main(src, 4, "sizeof");
}

// this was broken when i didn't have it resolving (==) as a bool
#[test]
fn implicit_cast_bool_to_long() {
    // language=c
    let src = "
long main(){
    long x = sizeof(long) == 8;
    return x;
}
    ";

    no_args_run_main(src, 1, "broken_implicit_cast");
}

#[test]
fn allocation() {
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
}

#[test]
fn ptr_math() {
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
}

#[test]
fn ptr_to_struct() {
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
}

#[test]
fn typedef() {
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
    z.a = 1;
    return z.b + z.a;
}
    ";
    no_args_run_main(src, 6, "typedef");
}

#[test]
fn array_list() {
    no_args_run_main(include_str!("../tests/array_list.c"), 0, "array_list");
}

#[test]
fn return_a_double() {
    // language=c
    let src = "
double main(){
    return 0.1;
}
    ";

    no_arg_to_double_run_main(src, 0.1, "return_a_double");
}

#[test]
fn big_constant() {
    // language=c
    let src = "
long main(long x){
    return 18446744073709551615;
}
    ";

    int_to_int_run_main(src, 0, 18446744073709551615, "big_constant");
}

#[test]
fn array_index_syntax_on_pointers() {
    // language=c
    let src = "
void* malloc(long size);
void free(void* ptr);
long main() {
    long* x = malloc(sizeof(long) * 10);
    x[2] = 10;
    long* y = &x[3];
    *y = 5;
    long result = x[2] + x[3];
    free(x);
    return result;
}
    ";

    no_args_run_main(src, 15, "array_index_syntax_on_pointers");
}

#[test]
fn heap_long() {
    // language=c
    let src = "
void* malloc(long size);
void free(void* ptr);
long main() {
    long* x = malloc(sizeof(long) * 10);
    long* z = malloc(sizeof(long));
    *z = 10;
    x[2] = *z;
    long* y = &x[3];
    *y = 5;
    long result = x[2] + x[3];
    free(x);
    free(z);
    return result;
}
    ";

    no_args_run_main(src, 15, "heap_long");
}

#[test]
fn for_loop() {
    // language=c
    let src = "
long main(){
    long j = 0;
    for (long i=0;i<10;i=i+1) {
        long k = 1;
        j = i + k;
    }
    return j;
}
    ";

    no_args_run_main(src, 10, "for_loop");
}

#[test]
fn do_while_loop() {
    // language=c
    let src = "
long main(){
    long i = 0;
    do {
        i = i + 1;
    } while (i < 10);
    return i;
}
    ";

    no_args_run_main(src, 10, "do_while_loop");
}

#[test]
fn int_as_condition() {
    // language=c
    let src = "
long main(){
    long one = 1 <= 10;
    long x = 10;
    while (x) {
        x = x - one;
    }
    return x;
}
    ";
    no_args_run_main(src, 0, "while_loop");
}

#[test]
fn while_loop_continue() {
    // language=c
    let src = "
long main(){
    long x = 0;
    long y = 0;
    while (x < 10) {
        x = x + 1;
        if (x > 5) {
            continue;
        }
        y = y + 1;
    }
    return y;
}
    ";
    no_args_run_main(src, 5, "while_loop_continue");
}

#[test]
fn while_loop_break() {
    // language=c
    let src = "
long main(){
    long x = 0;
    while (x < 10) {
        x = x + 1;
        if (x > 5) {
            break;
        }
    }
    return x;
}
    ";
    no_args_run_main(src, 6, "while_loop_break");
}

#[test]
fn for_loop_break() {
    // language=c
    let src = "
long main(){
    long x;
    for (x=0;x<10;x=x+1){
        if (x > 5) {
            break;
        }
    }
    return x;
}
    ";
    no_args_run_main(src, 6, "for_loop_break");
}

#[test]
fn for_loop_continue() {
    // language=c
    let src = "
long main(){
    long y = 0;
    for (long x=0;x<10;x=x+1){
        y = y + 1;
        if (x > 5) {
            continue;
        }
        
        x = x + 1;
    }
    return y;
}
    ";
    no_args_run_main(src, 7, "for_loop_continue");
}

#[test]
fn stack_array() {
    // language=c
    let src = "
int main(){
    float arr[2];

	arr[0] = 1;
	arr[1] = 2;

	return (arr[0] + arr[1]) - 3;
}
    ";
    no_args_run_main(src, 0, "stack_array");
}

#[test]
fn stack_array_structs() {
    // language=c
    let src = "
struct Thing {
    long a;
    long* b;
};
int main(){
    struct Thing arr[2];

	arr[0].a = 10;
	arr[1].b = &arr[0].a;
    arr[1].a = *arr[1].b;
    *arr[1].b = 5;

	return (arr[0].a + arr[1].a) - 15;
}
    ";
    no_args_run_main(src, 0, "stack_array_structs");
}

// TODO
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
