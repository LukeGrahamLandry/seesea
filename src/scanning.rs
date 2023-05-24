use logos::{Lexer, Logos};

#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
pub enum TokenType {
    #[token(".")]
    Period,

    #[regex("[_a-zA-Z][_a-zA-Z0-9]*")]
    Identifier,

    #[regex("[0-9]+", |lex| lex.slice().parse().ok())]
    DecimalInt(u64),

    #[token("=")]
    Equal,
    #[token("+")]
    Plus,
    #[token(";")]
    Semicolon,
}

pub struct Token<'src> {
    pub kind: TokenType,
    pub lexeme: &'src str,
}

pub struct Scanner<'src> {
    lex: Lexer<'src, TokenType>,
}

impl<'src> Scanner<'src> {
    pub fn new(src: &'src str) -> Scanner {
        Scanner {
            lex: TokenType::lexer(src),
        }
    }

    pub fn next(&mut self) -> Option<Token> {
        let lexeme = self.lex.slice();
        self.lex.next().map(|token| Token {
            lexeme,
            kind: token.unwrap(),
        })
    }
}
