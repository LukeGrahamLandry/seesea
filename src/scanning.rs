use logos::{Lexer, Logos};
use std::collections::VecDeque;
use std::fmt::{Debug, Formatter};

#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
pub enum TokenType {
    #[token(".")]
    Period,

    #[regex("[_a-zA-Z][_a-zA-Z0-9]*")]
    Identifier,

    // TODO: kinda annoying that this has data so i cant pass it around to match against.
    //       i should just parse it from the lexeme as needed.
    #[regex("[0-9]+", |lex| lex.slice().parse().ok())]
    DecimalInt(u64),

    #[token("=")]
    Equal,

    #[token("+")]
    Plus,

    #[token(";")]
    Semicolon,

    #[token("(")]
    LeftParen,

    #[token(")")]
    RightParen,

    #[token("{")]
    LeftBrace,

    #[token("}")]
    RightBrace,

    #[token("return")]
    Return,

    #[token("if")]
    If,

    #[token("else")]
    Else,

    #[token(">")]
    Greater,

    #[token("<")]
    Less,

    #[token(",")]
    Comma,

    #[token("-")]
    Minus,

    #[token("*")]
    Star,

    #[token("&")]
    Ampersand,

    Eof,
}

#[derive(Copy, Clone)]
pub struct Token<'src> {
    pub kind: TokenType,
    pub lexeme: &'src str,
    pub index: usize,
}

pub struct Scanner<'src> {
    src: &'src str,
    lex: Lexer<'src, TokenType>,
    cache: VecDeque<Token<'src>>, // @Speed: this should be a small static array
    pub(crate) index: usize,
    pub(crate) name: String,
}

// TODO: It feels like this should be a real iterator but I worry that the way I want to write the
//       parser recursively couldn't cope with having an outer loop holding a mutable reference.
//       Maybe still nice just can't iterate at the top level.
//       There's peekable but I don't think it will let you look more than one forward.
impl<'src> Scanner<'src> {
    pub fn new(src: &'src str, name: String) -> Scanner {
        let mut s = Scanner {
            src,
            lex: TokenType::lexer(src),
            cache: VecDeque::new(),
            index: 0,
            name,
        };
        s.refresh();
        s
    }

    fn refresh(&mut self) {
        while self.cache.len() < 5 {
            let token = self.lex_another();
            self.cache.push_back(token);
        }
    }

    fn lex_another(&mut self) -> Token<'src> {
        self.lex
            .next()
            .map(|token| {
                self.index += 1;
                let lexeme = self.lex.slice();
                Token {
                    lexeme,
                    kind: token.unwrap(),
                    index: self.index,
                }
            })
            .unwrap_or_else(|| Token {
                kind: TokenType::Eof,
                lexeme: "",
                index: self.index,
            })
    }

    #[must_use]
    pub fn next(&mut self) -> Token<'src> {
        let token = self.cache.pop_front().unwrap();
        self.refresh();
        token
    }

    pub fn has_next(&mut self) -> bool {
        !matches!(self.peek(), TokenType::Eof)
    }

    pub fn peek(&self) -> TokenType {
        self.cache[0].kind
    }

    pub fn peek_next(&self) -> TokenType {
        self.cache[1].kind
    }

    /// If the next token matches ty, consume it and return true.
    pub fn matches(&mut self, ty: TokenType) -> bool {
        // println!(
        //     "{:?}, {:?} {:?} {:?}",
        //     ty,
        //     self.peek(),
        //     matches!(self.peek(), ty),
        //     self.peek() == ty
        // ); // TODO: WTF
        if self.peek() == ty {
            self.advance();
            true
        } else {
            false
        }
    }

    pub fn consume(&mut self, ty: TokenType) -> Token {
        assert_eq!(self.peek(), ty);
        self.next()
    }

    pub fn advance(&mut self) {
        let _ = self.next();
    }

    // This can be super slow because it's just used for error messages.
    pub fn line_number(&self, token: Token) -> usize {
        let mut line = 0;
        let count = token.lexeme.as_ptr() as usize - self.src.as_ptr() as usize;
        for (i, c) in self.src.chars().enumerate() {
            if c == '\n' {
                line += 1;
            }
            if i == count {
                break;
            }
        }
        line
    }
}

impl<'src> Debug for Scanner<'src> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "=== Scanner at {} ===", self.index - self.cache.len())?;
        let mut temp = Scanner::new(self.src, self.name.clone());
        while temp.has_next() {
            let i = temp.index;
            write!(f, "{:?}, ", temp.next())?;
        }
        writeln!(f, "\n========")
    }
}

impl<'src> Debug for Token<'src> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "[{}. {:?} \"{}\"]", self.index, self.kind, self.lexeme)
    }
}
