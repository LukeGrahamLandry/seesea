use crate::asm::aarch64::build_asm;
#[cfg(feature = "cranelift")]
use crate::asm::cranelift::CraneLiftFuncGen;
#[cfg(feature = "llvm")]
use crate::asm::llvm::{null_terminate, RawLlvmFuncGen, TheContext};
use crate::ir::Module;
use crate::scanning::Scanner;
use crate::vm::{Vm, VmValue};
use crate::{ast, ir, log};
#[cfg(feature = "llvm")]
use llvm_sys::core::{LLVMContextCreate, LLVMDisposeMessage, LLVMModuleCreateWithNameInContext};
#[cfg(feature = "llvm")]
use llvm_sys::execution_engine::{
    LLVMCreateJITCompilerForModule, LLVMGetFunctionAddress, LLVMLinkInMCJIT,
};
#[cfg(feature = "llvm")]
use llvm_sys::target::{LLVM_InitializeNativeAsmPrinter, LLVM_InitializeNativeTarget};
use std::ffi::CStr;
use std::fs::File;
use std::io::Write;
use std::mem;
use std::mem::{size_of, MaybeUninit};
use std::process::Command;
use std::sync::Mutex;

// TODO: macro that you just give the function signature to
pub fn no_args_run_main(src: &str, expected: u64, name: &str) {
    let ir = compile_module(src, name);

    // VM
    assert_eq!(Vm::eval_int_args(&ir, "main", &[]).to_int(), expected);

    type Func = unsafe extern "C" fn() -> u64;
    #[cfg(feature = "llvm")]
    compile_and_run(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function();
            assert_eq!(answer, expected);
        };
    });

    #[cfg(feature = "cranelift")]
    compile_and_run_cranelift(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function();
            assert_eq!(answer, expected);
        };
    });

    // ASM
    run_asm_main(&ir, "() -> u64", "", &format!("{}", expected));
}

pub fn int_to_int_run_main(src: &str, input: u64, expected: u64, name: &str) {
    let ir = compile_module(src, name);

    // VM
    assert_eq!(Vm::eval_int_args(&ir, "main", &[input]).to_int(), expected);

    type Func = unsafe extern "C" fn(u64) -> u64;
    #[cfg(feature = "llvm")]
    compile_and_run(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input);
            assert_eq!(answer, expected);
        };
    });

    #[cfg(feature = "cranelift")]
    compile_and_run_cranelift(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input);
            assert_eq!(answer, expected);
        };
    });

    // ASM
    run_asm_main(
        &ir,
        "(a: u64) -> u64",
        &format!("{}", input),
        &format!("{}", expected),
    );
}

pub fn two_ints_to_int_run_main(src: &str, input_a: u64, input_b: u64, expected: u64, name: &str) {
    let ir = compile_module(src, name);

    // VM
    assert_eq!(
        Vm::eval_int_args(&ir, "main", &[input_a, input_b]).to_int(),
        expected
    );

    type Func = unsafe extern "C" fn(u64, u64) -> u64;
    #[cfg(feature = "llvm")]
    compile_and_run(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input_a, input_b);
            assert_eq!(answer, expected);
        };
    });

    #[cfg(feature = "cranelift")]
    compile_and_run_cranelift(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input_a, input_b);
            assert_eq!(answer, expected);
        };
    });

    // ASM
    run_asm_main(
        &ir,
        "(a: u64, b: u64) -> u64",
        &format!("{}, {}", input_a, input_b),
        &format!("{}", expected),
    );
}

pub fn three_ints_to_int_run_main(
    src: &str,
    input_a: u64,
    input_b: u64,
    input_c: u64,
    expected: u64,
    name: &str,
) {
    let ir = compile_module(src, name);

    // VM
    assert_eq!(
        Vm::eval_int_args(&ir, "main", &[input_a, input_b, input_c]).to_int(),
        expected
    );

    type Func = unsafe extern "C" fn(u64, u64, u64) -> u64;
    #[cfg(feature = "llvm")]
    compile_and_run(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input_a, input_b, input_c);
            assert_eq!(answer, expected);
        };
    });

    #[cfg(feature = "cranelift")]
    compile_and_run_cranelift(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input_a, input_b, input_c);
            assert_eq!(answer, expected);
        };
    });

    // ASM
    run_asm_main(
        &ir,
        "(a: u64, b: u64, c: u64) -> u64",
        &format!("{}, {}, {}", input_a, input_b, input_c),
        &format!("{}", expected),
    );
}

pub fn no_arg_to_double_run_main(src: &str, expected: f64, name: &str) {
    let ir = compile_module(src, name);

    // VM
    let answer = Vm::eval_int_args(&ir, "main", &[]).to_float();
    assert!((answer - expected).abs() < 0.000001);

    type Func = unsafe extern "C" fn() -> f64;
    #[cfg(feature = "llvm")]
    compile_and_run(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function();
            assert!((answer - expected).abs() < 0.000001);
        };
    });

    #[cfg(feature = "cranelift")]
    compile_and_run_cranelift(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function();
            assert!((answer - expected).abs() < 0.000001);
        };
    });

    // ASM
    run_asm_main(&ir, "() -> f64", "", &format!("{}", expected));
}

pub fn double_to_int_run_main(src: &str, input: f64, expected: u64, name: &str) {
    let ir = compile_module(src, name);

    // VM
    let answer = Vm::eval(&ir, "main", &[VmValue::F64(input)]).to_int();
    assert_eq!(answer, expected);

    type Func = unsafe extern "C" fn(f64) -> u64;
    #[cfg(feature = "llvm")]
    compile_and_run(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input);
            assert_eq!(answer, expected);
        };
    });

    #[cfg(feature = "cranelift")]
    compile_and_run_cranelift(&ir, "main", |function| {
        unsafe {
            let function: Func = mem::transmute(function);
            let answer = function(input);
            assert_eq!(answer, expected);
        };
    });

    // ASM
    run_asm_main(
        &ir,
        "(a: f64) -> u64",
        &format!("{}", input),
        &format!("{}", expected),
    );
}

static FILE_GUARD: Mutex<()> = Mutex::new(());

const NO_ASM: bool = true;

fn run_asm_main(ir: &Module, sig: &str, input: &str, output: &str) {
    if NO_ASM {
        return;
    }
    let asm = build_asm(ir);
    let generated = CODE_TEMPLATE
        .replace("$FUNC_NAME", "main")
        .replace("$SIG", sig)
        .replace("$INPUT", input)
        .replace("$OUTPUT", output)
        .replace("$ASM", &asm);

    let guard = FILE_GUARD.lock().unwrap();

    let path = format!("target/asm_tests_generated/src/{}.rs", ir.name);
    let mut file = File::create(&path).unwrap();
    file.write_all(generated.as_ref()).unwrap();

    // Note: this rewrites the lib path so forces it to be sequential (enforced by the mutex above).
    let path = "target/asm_tests_generated/src/lib.rs";
    let mut file = File::create(&path).unwrap();
    file.write_all(format!("mod {};", ir.name).as_ref())
        .unwrap();

    let output = Command::new("cargo")
        .arg("test")
        .arg(ir.name.as_ref())
        .arg("--")
        .arg("--nocapture")
        .current_dir("target/asm_tests_generated")
        .output();

    // Don't do the part that might panic while holding the mutex.
    drop(guard);

    // Not inheriting streams because that confuses the buffering and puts it above the other logging.
    let output = output.unwrap();
    println!("{}", String::from_utf8(output.stdout).unwrap());
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert!(output.status.success());
}

pub fn vm_run_cases(ir: &Module, func_name: &str, cases: &[(&[u64], u64)]) {
    for (args, answer) in cases {
        assert_eq!(Vm::eval_int_args(ir, func_name, args).to_int(), *answer);
    }
}

#[cfg(feature = "cranelift")]
pub fn compile_and_run_cranelift(ir: &Module, func_name: &str, action: impl FnOnce(u64)) {
    assert!(
        ir.get_internal_func(func_name).is_some(),
        "Function not found."
    );
    let mut module = CraneLiftFuncGen::new(ir);
    module.compile_all();
    let func = module.get_finalized_function(func_name).unwrap();
    action(func as usize as u64);
}

// This is unsafe! But since its just in tests and calling the function is unsafe anyway I don't really care.
// The caller MUST specify the right signature for F.
// TODO: is there a way I can reflect on the signature since I know what it should be from the ir? maybe make this a macro?
// F needs to be an unsafe extern "C" fn (?) -> ?
// TODO: ideally i could somehow get the asm into executable memory here and call action again with that function pointer
#[cfg(feature = "llvm")]
pub fn compile_and_run(ir: &Module, func_name: &str, action: impl FnOnce(u64)) {
    assert!(
        ir.get_internal_func(func_name).is_some(),
        "Function not found."
    );
    let func_name = null_terminate(func_name);
    unsafe {
        let context = LLVMContextCreate();
        let name = null_terminate(&ir.name);
        let module = LLVMModuleCreateWithNameInContext(name.as_ptr(), context);
        let mut the_context = TheContext { context, module };

        let mut execution_engine = MaybeUninit::uninit();
        let mut err = MaybeUninit::uninit();

        // Fixes: Unable to find target for this triple (no targets are registered)
        assert_eq!(LLVM_InitializeNativeTarget(), 0);
        // Fixes:  LLVM ERROR: Target does not support MC emission!
        assert_eq!(LLVM_InitializeNativeAsmPrinter(), 0);
        // Fixes: JIT has not been linked in.
        LLVMLinkInMCJIT();
        let failed = LLVMCreateJITCompilerForModule(
            execution_engine.as_mut_ptr(),
            module,
            0,
            err.as_mut_ptr(),
        );

        if failed != 0 {
            let err = err.assume_init();
            let msg = CStr::from_ptr(err).to_str().unwrap().to_string();
            LLVMDisposeMessage(err);
            panic!("{}", msg);
        }

        let execution_engine = execution_engine.assume_init();

        RawLlvmFuncGen::new(&mut the_context).compile_all(ir);

        let function_ptr = LLVMGetFunctionAddress(execution_engine, func_name.as_ptr());
        assert_ne!(function_ptr, 0);
        assert_eq!(
            size_of::<usize>(),
            size_of::<u64>(),
            "My transmutes are assuming that the int returned is the size of a function pointer."
        );
        action(function_ptr);

        // TODO: @Leak but in tests so who cares.
        //       Something fucks up the state of the context such that dropping it causes unpredictable memory related crashes.
        //       Removing these makes it better but still doesn't fix it.
        // LLVMDisposeExecutionEngine(execution_engine);
        // Doing this causes a SIGSEGV. The execution engine owns the module.
        // LLVMDisposeModule(module);
        // LLVMContextDispose(context);
    }
}

pub fn compile_module(src: &str, name: &str) -> Module {
    log!("{}", src);
    let scan = Scanner::new(src, name.into());
    log!("{:?}", scan);
    let ast = ast::Module::from(scan);
    log!("{:?}", ast);
    ir::Module::from(ast)
}

const CODE_TEMPLATE: &str = r#"

extern "C" {
    fn $FUNC_NAME$SIG;
}

#[test]
fn run_asm() {
    let result = unsafe { $FUNC_NAME($INPUT) };
    println!("ASM says: {}", result);
    assert_eq!(result, $OUTPUT);
}

std::arch::global_asm!("
$ASM");
"#;
