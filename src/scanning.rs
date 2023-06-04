use logos::{Lexer, Logos};
use std::collections::VecDeque;
use std::fmt::{Debug, Formatter};

// I probably want to manually write the lexer at some point because its cool if I wrote the whole thing.
// But also I really just don't care right now cause its boring.
#[derive(Logos, Copy, Clone, Debug, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
#[logos(skip r"//.*\n")]
pub enum TokenType {
    #[token(".")]
    Period,

    #[token("...")]
    ThreeDots,

    #[regex("[_a-zA-Z][_a-zA-Z0-9]*")]
    Identifier,

    #[regex(r#""([^"\\]|\\t|\\u|\\n|\\")*""#)]
    StringLiteral,

    // TODO: kinda annoying that this has data so i cant pass it around to match against.
    //       i should just parse it from the lexeme as needed.
    #[regex("[0-9]+", |lex| lex.slice().parse().ok())]
    DecimalInt(u64),

    #[regex("[0-9]+\\.[0-9]+", |lex| lex.slice().parse().ok())]
    DecimalFloat(f64),

    #[token("=")]
    Equal,

    #[token("+")]
    Plus,

    #[token("++")]
    PlusPlus,

    #[token("--")]
    MinusMinus,

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

    #[token("[")]
    LeftBracket,

    #[token("]")]
    RightBracket,

    #[token("return")]
    Return,

    #[token("typedef")]
    TypeDef,

    #[token("if")]
    If,

    #[token("else")]
    Else,

    #[token("while")]
    While,

    #[token("for")]
    For,

    #[token("do")]
    Do,

    #[token("break")]
    Break,

    #[token("continue")]
    Continue,

    #[token("struct")]
    Struct,

    #[token(">")]
    Greater,

    #[token("<")]
    Less,

    #[token(">=")]
    GreaterEqual,

    #[token("<=")]
    LessEqual,

    #[token("->")]
    Arrow,

    #[token(",")]
    Comma,

    #[token("-")]
    Minus,

    #[token("*")]
    Star,

    #[token("&")]
    Ampersand,

    #[token("/")]
    Slash,

    #[token("sizeof")]
    SizeOf,

    Eof,
}

#[derive(Copy, Clone)]
pub struct Token<'src> {
    pub kind: TokenType,
    pub lexeme: &'src str,
    pub index: usize,
    pub line: usize,
}

pub struct Scanner<'src> {
    src: &'src str,
    lex: Lexer<'src, TokenType>,
    cache: VecDeque<Token<'src>>, // @Speed: this should be a small static array
    pub(crate) index: usize,
    pub(crate) name: String,
    prev: Option<Token<'src>>,
    line: usize,
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
            prev: None,
            line: 0,
        };
        s.refresh();
        s
    }

    pub(crate) fn prev(&self) -> Token<'src> {
        self.prev.unwrap()
    }

    fn refresh(&mut self) {
        while self.cache.len() < 15 {
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
                let t = Token {
                    lexeme,
                    kind: token.unwrap(),
                    index: self.index,
                    line: 12345,
                };
                t
            })
            .unwrap_or_else(|| Token {
                kind: TokenType::Eof,
                lexeme: "",
                index: self.index,
                line: 12345,
            })
    }

    #[must_use]
    pub fn take(&mut self) -> Token<'src> {
        let mut token = self.cache.pop_front().unwrap();
        match self.prev {
            None => {}
            Some(prev) => {
                // TODO: move this to lex_another because this is wrong if you use replace
                let start = prev.lexeme.as_ptr() as usize - self.src.as_ptr() as usize;
                let end = token.lexeme.as_ptr() as usize - self.src.as_ptr() as usize;
                // TODO: utf8?
                let bytes = self.src.as_bytes();
                assert!(end > start);
                for i in start..end {
                    if bytes[i] == b'\n' {
                        self.line += 1;
                    }
                }
                token.line = self.line;
            }
        }

        self.refresh();
        self.prev = Some(token);
        token
    }

    pub fn replace(&mut self, token: Token<'src>) {
        self.cache.push_front(token)
    }

    pub fn has_next(&mut self) -> bool {
        !matches!(self.peek(), TokenType::Eof)
    }

    pub fn peek(&self) -> TokenType {
        self.peek_n(0).kind
    }

    pub fn peek_next(&self) -> TokenType {
        self.peek_n(1).kind
    }

    pub fn peek_n(&self, n: usize) -> Token<'src> {
        self.cache[n]
    }

    /// If the next token matches ty, consume it and return true.
    pub fn matches(&mut self, ty: TokenType) -> bool {
        // log!(
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

    pub fn consume(&mut self, ty: TokenType) -> Token<'src> {
        assert_eq!(self.peek(), ty);
        self.take()
    }

    pub fn advance(&mut self) -> Token<'src> {
        self.take()
    }
}

impl<'src> Debug for Scanner<'src> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "=== Scanner at ===")?;
        let mut temp = Scanner::new(self.src, self.name.clone());
        while temp.has_next() {
            write!(f, "{:?}, ", temp.take())?;
        }
        writeln!(f, "\n========")
    }
}

impl<'src> Debug for Token<'src> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "[{}. {:?} \"{}\"]", self.index, self.kind, self.lexeme)
    }
}
