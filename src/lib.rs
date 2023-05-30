pub mod asm;
pub mod ast;
pub mod ir;
pub mod scanning;

mod macros;
#[cfg(test)]
mod tests;
mod vm;

pub const KEEP_IR_DEBUG_NAMES: bool = true;
