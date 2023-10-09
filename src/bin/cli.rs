//! A simple CLI for running the compiler on a single c file. Can run with various backends or output llvm ir. 

use std::env;
use std::fs;
use seesea::ir;
use seesea::test_logic::compile_module;
use seesea::vm::Vm;

// TODO: allow input from stdin as well.
fn main() {
    let mut args = env::args();
    let _self = args.next();
    if let Some(action) = args.next() {
        match action.as_str() {
            "run_vm" => {
                let module = compile_from_input(args.next());
                expect_empty(args);
                let status = Vm::eval(&module, "main", &[]).to_int();
                std::process::exit(status as i32);
            }
            "ir_vm" => {  // TODO: option for printing ast? 
                let module = compile_from_input(args.next());
                for struc in &module.structs {
                    println!("{struc:?}\n");  // TODO: better formatting (impl Debug)
                }
                for func in &module.functions {
                    println!("{func:?}");
                }
                expect_empty(args);
            }
            "run_llvm" | "ir_llvm" => {
                let _module = compile_from_input(args.next());
                todo!("Finish cli.");
            }
            _ => {
                println!("Unrecognised option '{action}'. {USAGE}");
            }
        }
    } else {
        println!("{USAGE}");
    }
}

fn compile_from_input(arg: Option<String>) -> ir::Module {
    let input_filepath = arg.unwrap_or_else(|| {
        panic!("Missing input filepath.");
    });
    let src = fs::read_to_string(&input_filepath).unwrap_or_else(|err| {
        println!("CWD={:?}", env::current_dir());
        panic!("{err} {input_filepath}");
    });

    compile_module(&src, &input_filepath)
}

// TODO: when running, pass to args the program instead. 
fn expect_empty(mut args: env::Args) {
    if let Some(arg) = args.next() {
        println!("{USAGE}");
        panic!("Unexpected argument '{arg}'.");
    }
}

const USAGE: &str = "
Usage: seesea [action]_[backend] file.c
    Actions: run, ir
        - run: execute the program
        - ir: print intermediary representation to stdout
    Backend: llvm, vm

NOTE: Seesea accepts only a single source file. It does not include a preprecessor. You must run that yourself. 
";
