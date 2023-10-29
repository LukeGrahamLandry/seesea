pub mod asm;
pub mod ast;
pub mod ir;
pub mod scanning;
pub mod vm;
#[cfg(test)]
pub mod test_logic;
#[cfg(test)]
pub mod tests;
mod util;

pub const KEEP_IR_DEBUG_NAMES: bool = true;
macro_rules! log {
    // Using cfg!(...) instead of #[cfg(...)] to avoid unused var warnings.
    ($($arg:tt)*) => {{
        if cfg!(feature = "logging") {
            println!($($arg)*);
        }
    }};
}

pub(crate) use log;
