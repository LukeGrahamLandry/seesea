use crate::asm::aarch64::build_asm;
use crate::asm::aarch64_out::TextAsm;
use crate::ir::Module;
use crate::scanning::Scanner;
use crate::test_cases::get_tests;
use crate::{ast, ir, log};
use std::fs;
use std::fs::File;
use std::io::Write;
use std::panic::catch_unwind;
use std::process::{Command, ExitStatus, Stdio};

pub enum TestCase {
    NoArgsRunMain {
        src: String,
        expected: u64,
        name: String,
    },
    IntToIntRunMain {
        src: String,
        input: u64,
        expected: u64,
        name: String,
    },
}

#[test]
pub fn run_asm_tests() {
    generate_asm_rust_project();
    let status = Command::new("cargo")
        .arg("test")
        .current_dir("target/asm_tests_generated")
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .unwrap();
    assert!(status.success());
}

/// Since I'm not prepared to deal with figuring out how to assemble and link an executable yet,
/// I'm letting rust's global_asm macro do it for me.
/// This generates another crate with a bunch of tests that each call a function defined in inline asm.
// TODO: generate modules for [asm, llvm, vm] so all compiling happens here and all running happens in the generated tests
//       so one backend crashing doesn't kill all of them. compile the module once, can i serialize it somehow?
fn generate_asm_rust_project() {
    let path = format!("target/asm_tests_generated/cargo.toml");
    fs::remove_dir_all("target/asm_tests_generated/src").unwrap();
    fs::create_dir_all("target/asm_tests_generated/src").unwrap();
    let mut file = File::create(&path).unwrap();
    file.write_all(CARGO_TOML.as_ref()).unwrap();

    let mut lib_file = String::new();
    for test_case in &get_tests() {
        match test_case {
            TestCase::NoArgsRunMain {
                src,
                expected,
                name,
            } => {
                let result = catch_unwind(|| {
                    let ir = compile_module(src, name);
                    let asm = build_asm::<TextAsm>(&ir).get_text();
                    log!("==== Direct Aarch64 =====");
                    log!("{}", asm);
                    log!("============");
                    (ir, asm)
                });

                let path = format!("target/asm_tests_generated/src/{}.rs", name);
                let mut file = File::create(&path).unwrap();
                if let Ok((ir, asm)) = result {
                    let generated = NO_ARGS_MAIN_TEMPLATE
                        .replace("$FUNC_NAME", &format!("{}_main", ir.name))
                        .replace("$OUTPUT", &format!("{}", *expected))
                        .replace("$ASM", &asm);

                    file.write_all(generated.as_ref()).unwrap();
                } else {
                    file.write_all(
                        FAILED_TEMPLATE
                            .replace("$FUNC_NAME", &format!("{}_main", name))
                            .as_ref(),
                    )
                    .unwrap();
                }

                lib_file += &format!("mod {};\n", name);
            }
            TestCase::IntToIntRunMain {
                src,
                input,
                expected,
                name,
            } => {
                let result = catch_unwind(|| {
                    let ir = compile_module(src, name);
                    let asm = build_asm::<TextAsm>(&ir).get_text();
                    log!("==== Direct Aarch64 =====");
                    log!("{}", asm);
                    log!("============");
                    (ir, asm)
                });

                let path = format!("target/asm_tests_generated/src/{}.rs", name);
                let mut file = File::create(&path).unwrap();
                if let Ok((ir, asm)) = result {
                    let generated = INT_TO_INT_TEMPLATE
                        .replace("$FUNC_NAME", &format!("{}_main", ir.name))
                        .replace("$OUTPUT", &format!("{}", *expected))
                        .replace("$INPUT", &format!("{}", *input))
                        .replace("$ASM", &asm);

                    file.write_all(generated.as_ref()).unwrap();
                } else {
                    file.write_all(
                        FAILED_TEMPLATE
                            .replace("$FUNC_NAME", &format!("{}_main", name))
                            .as_ref(),
                    )
                    .unwrap();
                }

                lib_file += &format!("mod {};\n", name);
            }
        }
    }

    let path = "target/asm_tests_generated/src/lib.rs";
    let mut file = File::create(path).unwrap();
    file.write_all(lib_file.as_ref()).unwrap();
}

pub fn compile_module(src: &str, name: &str) -> ir::Module {
    log!("{}", src);
    let scan = Scanner::new(src, name.into());
    log!("{:?}", scan);
    let ast = ast::Module::from(scan);
    log!("{:?}", ast);
    ir::Module::from(ast)
}

const INT_TO_INT_TEMPLATE: &str = r#"
extern "C" {
    fn $FUNC_NAME(a: u64) -> u64;
}

#[test]
fn run_asm() {
    let result = unsafe { $FUNC_NAME($INPUT) };
    println!("ASM says: {}", result);
    assert_eq!(result, $OUTPUT);
}

std::arch::global_asm!("$ASM");
"#;

const NO_ARGS_MAIN_TEMPLATE: &str = r#"
extern "C" {
    fn $FUNC_NAME() -> u64;
}

#[test]
fn run_asm() {
    let result = unsafe { $FUNC_NAME() };
    println!("ASM says: {}", result);
    assert_eq!(result, $OUTPUT);
}

std::arch::global_asm!("$ASM");
"#;

const FAILED_TEMPLATE: &str = r#"
#[test]
fn run_asm() {
    panic!("Failed to compile ASM.");
}
"#;

const CARGO_TOML: &str = r#"
[package]
name = "seesea_generated"
version = "0.1.0"
edition = "2021"
"#;
