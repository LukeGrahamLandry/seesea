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
        // works
        // println!($($arg)*);
        // std::thread::sleep(std::time::Duration::from_millis(1));
        // std::thread::sleep(std::time::Duration::from_micros(54));

        // crashes
        // std::thread::sleep(std::time::Duration::from_micros(50));
        // std::thread::yield_now();
    }};
}

pub(crate) use log;
