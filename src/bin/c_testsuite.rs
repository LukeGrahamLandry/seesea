//! A runner for https://github.com/c-testsuite/c-testsuite

use seesea::test_logic::{compile_and_run, compile_module};
use std::panic::catch_unwind;
use std::sync::mpsc;
use std::sync::mpsc::RecvTimeoutError;
use std::time::Duration;
use std::{env, fs, mem, thread};

fn main() {
    let dir = env::current_dir().unwrap();
    println!("CWD: {:?}", dir);
    let mut passed = 0;
    let mut timeout = 0;
    let mut panicked = 0;
    let mut wrong_exitcode = 0;
    let mut total = 0;
    'outer: for i in 1..221 {
        let path = format!("c-testsuite/tests/single-exec/{:05}.c", i);
        println!("=== {path} ===");
        let src = match fs::read_to_string(&path) {
            Ok(s) => s,
            Err(_) => {
                panic!("Test file not found. Please 'git clone https://github.com/c-testsuite/c-testsuite.git'");
            }
        };

        // TODO: run a pre-processor
        let tags =
            fs::read_to_string(&format!("c-testsuite/tests/single-exec/{:05}.c.tags", i)).unwrap();
        let skip = tags
            .split_ascii_whitespace()
            .any(|s| s == "needs-cpp" || s == "needs-libc");
        if skip {
            println!("Skip. (needs-libc or needs-cpp)");
            continue;
        }

        for s in UNIMPLEMENTED {
            if src.contains(s) {
                println!("TODO: Found unimplemented token '{s}'. Skipping.");
                continue 'outer;
            }
        }

        total += 1;
        let status = catch_unwind(|| {
            let src = src.clone();
            run_with_timeout(
                move || {
                    let ir = compile_module(&src, &path);
                    type Func = unsafe extern "C" fn() -> i32;
                    let mut result = 1;
                    compile_and_run(&ir, "main", |function| {
                        unsafe {
                            let function: Func = mem::transmute(function);
                            result = function();
                        };
                    });
                    result
                },
                Duration::from_secs(1),
            )
        });

        if !matches!(status, Ok(Ok(0))) {
            println!("{}", src);
        }
        match status {
            Ok(Ok(0)) => {
                println!("{i:05}: PASSED");
                passed += 1
            }
            Ok(Err(TimeoutError)) => {
                println!("{i:05}: TIMEOUT");
                timeout += 1
            }
            Err(_) => {
                println!("{i:05}: PANIC");
                panicked += 1
            }
            Ok(Ok(e)) => {
                println!("{i:05}: EXITCODE ({e}) != 0");
                wrong_exitcode += 1
            }
        }
    }

    println!("=== RESULTS ===");
    println!("total={total} passed={passed} wrong_exitcode={wrong_exitcode} panicked={panicked} timeout={timeout}.",);
}

// TODO: implement these. This is a nice place to keep a list.
const UNIMPLEMENTED: [&str; 10] = [
    "enum",
    "union",
    "goto",
    "static",
    "%",
    "__builtin_expect",
    "main(void)", // K&R
    "{[",         // labeled array initialization
    "~",          // bitwise not
    "!=",
];
// Not lexically obvious: should do the parser part at least so it can give a good error message
//   - function pointers
//   - global variables
//   - comma in var declaration
//   - array/struct init list
//   - anon-structs
//   - static array variable

// https://stackoverflow.com/questions/36181719/what-is-the-correct-way-in-rust-to-create-a-timeout-for-a-thread-or-a-function
fn run_with_timeout<F, T>(f: F, timeout: Duration) -> Result<T, TimeoutError>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    let _ = thread::spawn(move || {
        let result = f();
        match tx.send(result) {
            Ok(()) => {} // everything good
            Err(_) => {} // we have been released, don't panic
        }
    });

    match rx.recv_timeout(timeout) {
        Ok(result) => Ok(result),
        Err(RecvTimeoutError::Timeout) => Err(TimeoutError),
        Err(RecvTimeoutError::Disconnected) => unreachable!(),
    }
}

#[derive(Debug)]
struct TimeoutError;
