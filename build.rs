use std::fs;
use std::fs::File;
use std::io::Write;

fn main() {
    // Create an empty folder for generated asm tests.
    // TODO: Remove this when I progress past using Rust's inline asm as the assembler/linker
    fs::create_dir_all(&format!("{GEN_CRATE_PATH}/src")).unwrap();
    let mut file = File::create(&format!("{GEN_CRATE_PATH}/Cargo.toml")).unwrap();
    file.write_all(CARGO_TOML.as_ref()).unwrap();
}

const GEN_CRATE_PATH: &str = "target/asm_tests_generated";

const CARGO_TOML: &str = r#"
[package]
name = "seesea_generated"
version = "0.1.0"
edition = "2021"
"#;
