//! TOKENS -> AST

use crate::ast::{BinaryOp, Expr, FuncSignature, Function, LiteralValue, Module, Stmt, ValueType};
use crate::scanning::{Scanner, TokenType};

impl<'src> From<Scanner<'src>> for Module {
    fn from(scanner: Scanner) -> Self {
        let name = scanner.name.clone();
        let mut parser = Parser {
            scanner,
            program: Module {
                functions: vec![],
                name,
            },
        };
        parser.run();
        parser.program
    }
}

struct Parser<'src> {
    scanner: Scanner<'src>,
    program: Module,
}

impl<'src> Parser<'src> {
    fn run(&mut self) {
        while self.scanner.has_next() {
            self.parse_function();
        }
    }

    // TODO: separate the signature cause i need to support forward declarations
    /// TYPE NAME() STMT
    fn parse_function(&mut self) {
        let returns = self.read_type("expected function declaration");
        let name = self.read_ident("expected function name");
        self.scanner.consume(TokenType::LeftParen);
        let mut args = vec![];
        let mut names = vec![];
        while !self.scanner.matches(TokenType::RightParen) {
            args.push(self.read_type("Function arg requires type."));
            names.push(self.read_ident("Function arg requires name.")); // TODO: headers/forward defs dont
            if !self.scanner.matches(TokenType::Comma) {
                assert_eq!(
                    self.scanner.peek(),
                    TokenType::RightParen,
                    "Expected ')' or ',' after function arg."
                );
            }
        }
        let body = self.parse_stmt();
        self.program.functions.push(Function {
            body,
            signature: FuncSignature {
                param_types: args,
                param_names: names,
                return_type: returns,
                name,
            },
        })
    }

    /// STMT
    fn parse_stmt(&mut self) -> Stmt {
        // { STMT* }
        if self.scanner.matches(TokenType::LeftBrace) {
            let mut body = vec![];
            while !self.scanner.matches(TokenType::RightBrace) {
                body.push(self.parse_stmt());
            }
            return Stmt::Block { body, lines: None }; // TODO
        }

        let is_decl = self.scanner.peek() == TokenType::Identifier
            && self.scanner.peek_next() == TokenType::Identifier;
        if is_decl {
            return self.parse_declare_variable();
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

        if self.scanner.peek() == TokenType::If {
            return self.parse_if();
        }

        // Better error messages for tokens we know can't start expressions.
        if self.scanner.peek() == TokenType::Else {
            self.error(
                "Keyword 'else' must be preceded by 'if STMT' (maybe you forgot a closing '}')",
            )
        }

        // EXPR;
        let expr = self.parse_expr();
        if !self.scanner.matches(TokenType::Semicolon) {
            self.error("Expected semicolon terminating expression statement.")
        }
        Stmt::Expression {
            expr: Box::new(expr),
        }
    }

    /// TYPE NAME = EXPR?;
    fn parse_declare_variable(&mut self) -> Stmt {
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
        Stmt::DeclareVar {
            name,
            kind,
            value: Box::new(value),
        }
    }

    /// if (EXPR) STMT else? STMT?
    fn parse_if(&mut self) -> Stmt {
        self.scanner.consume(TokenType::If);
        self.scanner.consume(TokenType::LeftParen);
        let condition = self.parse_expr();
        self.scanner.consume(TokenType::RightParen);
        let if_true = self.parse_stmt();
        let if_false = if self.scanner.matches(TokenType::Else) {
            self.parse_stmt()
        } else {
            Stmt::Block {
                body: vec![],
                lines: None,
            }
        };
        Stmt::If {
            condition: Box::new(condition),
            then_body: Box::new(if_true),
            else_body: Box::new(if_false),
        }
    }

    /// EXPR
    fn parse_expr(&mut self) -> Expr {
        let left = self.parse_primary();
        let op = match self.scanner.peek() {
            TokenType::Plus => BinaryOp::Add,
            TokenType::Greater => BinaryOp::GreaterThan,
            TokenType::Less => BinaryOp::LessThan,
            TokenType::Equal => BinaryOp::Assign,
            TokenType::Minus => BinaryOp::Subtract,
            _ => return left, // todo: only some tokens are valid here
        };

        self.scanner.advance();
        let right = self.parse_expr();
        Expr::Binary {
            left: Box::new(left),
            right: Box::new(right),
            op,
        }
    }

    /// NAME | NUMBER | (EXPR)
    fn parse_primary(&mut self) -> Expr {
        let mut expr = self.parse_basic();
        loop {
            match self.scanner.peek() {
                TokenType::LeftParen => {
                    self.scanner.consume(TokenType::LeftParen);
                    let mut args = vec![];
                    while !self.scanner.matches(TokenType::RightParen) {
                        args.push(self.parse_expr());
                        if !self.scanner.matches(TokenType::Comma) {
                            assert_eq!(
                                self.scanner.peek(),
                                TokenType::RightParen,
                                "Expected ')' or ',' after function arg."
                            );
                        }
                    }

                    expr = Expr::Call {
                        func: Box::new(expr),
                        args,
                    }
                }
                _ => return expr,
            }
        }
    }

    fn parse_basic(&mut self) -> Expr {
        let token = self.scanner.next();
        match token.kind {
            TokenType::DecimalInt(v) => Expr::Literal {
                value: LiteralValue::Number { value: v as f64 },
            },
            TokenType::Identifier => Expr::GetVar {
                name: token.lexeme.to_string(),
            },
            TokenType::LeftParen => {
                let expr = self.parse_expr();
                self.scanner.consume(TokenType::RightParen);
                expr
            }
            _ => self.error("Expected primary expr (number or var access)"),
        }
    }

    /// TYPE
    fn read_type(&mut self, msg: &str) -> ValueType {
        let token = self.scanner.next();
        if token.kind != TokenType::Identifier || token.lexeme != "long" {
            self.error(msg);
        }
        ValueType::U64
    }

    /// NAME
    fn read_ident(&mut self, msg: &str) -> String {
        let token = self.scanner.next();
        if token.kind != TokenType::Identifier {
            self.error(msg);
        }
        token.lexeme.into()
    }

    fn error(&mut self, msg: &str) -> ! {
        let i = self.scanner.index;
        let token = self.scanner.next();
        let line = self.scanner.line_number(token);
        panic!(
            "Parse error on line {}: {} at {}. {:?}",
            line, msg, i, token
        );
    }
}
