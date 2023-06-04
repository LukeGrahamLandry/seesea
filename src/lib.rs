pub mod asm;
pub mod ast;
pub mod ir;
pub mod scanning;

mod macros;
mod resolve;
#[cfg(test)]
mod tests;
mod vm;

pub const KEEP_IR_DEBUG_NAMES: bool = true;

macro_rules! log {
    ($($arg:tt)*) => {{
        println!($($arg)*);
    }};
}

pub(crate) use log;
