pub mod asm;
pub mod ast;
pub mod ir;
pub mod scanning;

mod macros;
mod resolve;
#[cfg(test)]
pub mod tests;
mod vm;

pub const KEEP_IR_DEBUG_NAMES: bool = true;
pub const DO_LOGGING: bool = true;

macro_rules! log {
    ($($arg:tt)*) => {{
        if $crate::DO_LOGGING {
            println!($($arg)*);
        }
    }};
}

pub(crate) use log;
