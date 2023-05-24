use crate::asm::llvm::add_numbers;
use crate::scanning::TokenType;
use logos::Logos;

mod asm;
mod ir;
mod ast;
mod scanning;

fn main() {
    // let src = "int x = 5;";
    // let tokens = TokenType::lexer(src).spanned();
    // tokens.for_each(|t| println!("{:?}", t));
    add_numbers();
}

#[test]
fn count_scanned_tokens() {
    assert_eq!(TokenType::lexer("int x = 5;").count(), 5);
}
