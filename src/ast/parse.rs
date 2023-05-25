//! TOKENS -> AST

use crate::ast::{BinaryOp, Expr, FuncSignature, Function, LiteralValue, Program, Stmt, ValueType};
use crate::scanning::{Scanner, TokenType};

impl<'src> From<Scanner<'src>> for Program {
    fn from(scanner: Scanner) -> Self {
        let mut parser = Parser {
            scanner,
            program: Program { functions: vec![] },
        };
        parser.run();
        parser.program
    }
}

struct Parser<'src> {
    scanner: Scanner<'src>,
    program: Program,
}

impl<'src> Parser<'src> {
    fn run(&mut self) {
        while self.scanner.has_next() {
            self.parse_function();
        }
    }

    // TYPE NAME() STMT
    fn parse_function(&mut self) {
        let returns = self.read_type("expected function declaration");
        let name = self.read_ident("expected function name");
        self.scanner.consume(TokenType::LeftParen);
        self.scanner.consume(TokenType::RightParen);
        let body = self.parse_stmt();
        self.program.functions.push(Function {
            body,
            signature: FuncSignature {
                args: vec![],
                returns,
                name,
            },
        })
    }

    // STMT
    fn parse_stmt(&mut self) -> Stmt {
        // { STMT* }
        if self.scanner.matches(TokenType::LeftBrace) {
            let mut body = vec![];
            while !self.scanner.matches(TokenType::RightBrace) {
                body.push(self.parse_stmt());
            }
            return Stmt::Block { body };
        }

        // TYPE NAME = EXPR?;
        let is_decl = self.scanner.peek() == TokenType::Identifier
            && self.scanner.peek_next() == TokenType::Identifier;
        if is_decl {
            let kind = self.read_type("assert var type");
            let name = self.read_ident("assert var name");
            self.scanner.consume(TokenType::Equal);
            let value = if self.scanner.matches(TokenType::Semicolon) {
                Expr::Default(kind)
            } else {
                let value = self.parse_expr();
                self.scanner.consume(TokenType::Semicolon);
                value
            };
            return Stmt::DeclareVar {
                name,
                kind,
                value: Box::new(value),
            };
        }

        // return EXPR?;
        if self.scanner.matches(TokenType::Return) {
            let value = if self.scanner.matches(TokenType::Semicolon) {
                None
            } else {
                let value = self.parse_expr();
                self.scanner.consume(TokenType::Semicolon);
                Some(Box::new(value))
            };
            return Stmt::Return { value };
        }

        unreachable!("Expected statement.")
    }

    // EXPR
    fn parse_expr(&mut self) -> Expr {
        let left = self.parse_primary();
        if self.scanner.matches(TokenType::Plus) {
            let right = self.parse_primary();
            Expr::Binary {
                left: Box::new(left),
                right: Box::new(right),
                op: BinaryOp::Add,
            }
        } else {
            left
        }

        // unreachable!("Expected expression.")
    }

    fn parse_primary(&mut self) -> Expr {
        let token = self.scanner.next();
        match token.kind {
            TokenType::DecimalInt(v) => Expr::Literal {
                value: LiteralValue::Number { value: v as f64 },
            },
            TokenType::Identifier => Expr::GetVar {
                name: token.lexeme.to_string(),
            },
            _ => unreachable!("Expected primary expr (number or var access)"),
        }
    }

    fn read_type(&mut self, msg: &str) -> ValueType {
        let token = self.scanner.next();
        if token.kind != TokenType::Identifier || token.lexeme != "long" {
            self.error(msg);
        }
        ValueType::U64
    }

    fn read_ident(&mut self, msg: &str) -> String {
        let token = self.scanner.next();
        if token.kind != TokenType::Identifier {
            self.error(msg);
        }
        token.lexeme.into()
    }

    fn error(&mut self, msg: &str) -> ! {
        let i = self.scanner.index;
        panic!("Parse error: {} at {}. {:?}", msg, i, self.scanner.next())
    }
}
