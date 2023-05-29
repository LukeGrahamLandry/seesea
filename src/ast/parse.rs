//! TOKENS -> AST

use crate::ast::{
    BinaryOp, CType, Expr, FuncSignature, Function, LiteralValue, Module, Stmt, StructSignature,
    UnaryOp, ValueType,
};
use crate::scanning::{Scanner, Token, TokenType};
use std::collections::HashMap;

impl<'src> From<Scanner<'src>> for Module {
    fn from(scanner: Scanner) -> Self {
        let name = scanner.name.clone();
        let mut parser = Parser {
            scanner,
            program: Module {
                functions: vec![],
                structs: vec![],
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
            match self.scanner.peek() {
                TokenType::Struct => self.parse_struct_def(),
                _ => self.parse_function(),
            }
        }
    }

    fn parse_struct_def(&mut self) {
        self.expect(TokenType::Struct);
        let name = self.read_ident("Expected name in struct definition.");
        self.expect(TokenType::LeftBrace);
        let mut fields: Vec<(String, CType)> = vec![];

        while self.scanner.peek() != TokenType::RightBrace {
            let ty = self.read_type().expect("Expected type for struct field.");
            let name = self.read_ident("Expected name for struct field.");
            self.expect(TokenType::Semicolon);
            assert!(fields.iter().find(|f| f.0 == name).is_none());
            fields.push((name, ty));
        }
        let name = Box::leak(name.into_boxed_str());
        self.program.structs.push(StructSignature { name, fields });
        self.expect(TokenType::RightBrace);
        self.expect(TokenType::Semicolon);
    }

    // TODO: separate the signature cause i need to support forward declarations
    /// TYPE NAME() STMT
    fn parse_function(&mut self) {
        let returns = self.read_type().expect("expected function declaration");
        let name = self.read_ident("expected function name");
        self.expect(TokenType::LeftParen);
        let mut args = vec![];
        let mut names = vec![];
        while !self.scanner.matches(TokenType::RightParen) {
            args.push(self.read_type().expect("Function arg requires type."));
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

        let ty = self.read_type();
        if let Some(..) = ty {
            return self.parse_declare_variable(ty.unwrap());
        }

        // return EXPR?;
        if self.scanner.matches(TokenType::Return) {
            let value = if self.scanner.matches(TokenType::Semicolon) {
                None
            } else {
                let value = self.parse_expr();
                self.expect(TokenType::Semicolon);
                Some(Box::new(value))
            };
            return Stmt::Return { value };
        }

        if self.scanner.peek() == TokenType::If {
            return self.parse_if();
        }

        if self.scanner.peek() == TokenType::While {
            return self.parse_while_loop();
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
    fn parse_declare_variable(&mut self, kind: CType) -> Stmt {
        let name = self.read_ident("assert var name");

        let value = if self.scanner.matches(TokenType::Semicolon) {
            Expr::Default(kind)
        } else {
            self.expect(TokenType::Equal);
            let value = self.parse_expr();
            self.expect(TokenType::Semicolon);
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
        self.expect(TokenType::If);
        self.expect(TokenType::LeftParen);
        let condition = self.parse_expr();
        self.expect(TokenType::RightParen);
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

    /// while (EXPR) STMT
    fn parse_while_loop(&mut self) -> Stmt {
        self.expect(TokenType::While);
        self.expect(TokenType::LeftParen);
        let condition = self.parse_expr();
        self.expect(TokenType::RightParen);
        let body = self.parse_stmt();
        Stmt::While {
            condition: Box::new(condition),
            body: Box::new(body),
        }
    }

    // TODO: it parses long* x = &a; as (long * x) = &a; because statement checker doesnt know long* is a type
    /// EXPR
    fn parse_expr(&mut self) -> Expr {
        let left = self.parse_unary();
        let op = match self.scanner.peek() {
            TokenType::Plus => BinaryOp::Add,
            TokenType::Greater => BinaryOp::GreaterThan,
            TokenType::Less => BinaryOp::LessThan,
            TokenType::Equal => BinaryOp::Assign,
            TokenType::Minus => BinaryOp::Subtract,
            TokenType::Star => BinaryOp::Multiply,
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

    fn parse_unary(&mut self) -> Expr {
        let op = match self.scanner.peek() {
            TokenType::Minus => Some(UnaryOp::Negate),
            TokenType::Star => Some(UnaryOp::Deref),
            TokenType::Ampersand => Some(UnaryOp::AddressOf),
            _ => None,
        };

        match op {
            None => self.parse_primary(),
            Some(op) => {
                self.scanner.advance();
                Expr::Unary {
                    value: Box::new(self.parse_unary()),
                    op,
                }
            }
        }
    }

    fn parse_primary(&mut self) -> Expr {
        let mut expr = self.parse_basic();
        loop {
            match self.scanner.peek() {
                TokenType::LeftParen => {
                    self.expect(TokenType::LeftParen);
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
                TokenType::Period => {
                    self.expect(TokenType::Period);
                    let name = self.read_ident("Expected field name.");
                    expr = Expr::GetField {
                        object: Box::new(expr),
                        name,
                    }
                }
                _ => return expr,
            }
        }
    }

    /// NAME | NUMBER | (EXPR)
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
                self.expect(TokenType::RightParen);
                expr
            }
            _ => self.err("Expected primary expr (number or var access)", token),
        }
    }

    /// TYPE
    #[must_use]
    fn read_type(&mut self) -> Option<CType> {
        let token = self.scanner.peek_n(0);
        let mut ty = match token.kind {
            TokenType::Struct => {
                self.expect(TokenType::Struct);
                let name_token = self.scanner.peek_n(0);
                let name = self.read_ident("Expected identifier of struct.");
                let s = self.program.structs.iter().find(|s| s.name == name);
                let s = match s {
                    None => self.err("Undeclared struct", name_token),
                    Some(s) => s,
                };
                CType {
                    ty: ValueType::Struct(s.name),
                    depth: 0,
                }
            }
            TokenType::Identifier => {
                if token.lexeme != "long" {
                    return None;
                }

                self.expect(TokenType::Identifier);
                CType {
                    ty: ValueType::U64,
                    depth: 0,
                }
            }
            _ => return None,
        };

        while self.scanner.matches(TokenType::Star) {
            ty = ty.ref_type();
        }
        println!("found type {:?} next: {:?}", ty, self.scanner.peek());
        Some(ty)
    }

    /// NAME
    fn read_ident(&mut self, msg: &str) -> String {
        let token = self.scanner.next();
        if token.kind != TokenType::Identifier {
            self.err(msg, token);
        }
        token.lexeme.into()
    }

    fn expect(&mut self, kind: TokenType) {
        let token = self.scanner.next();
        if token.kind != kind {
            self.err(&format!("Expected {:?}", kind), token);
        }
    }

    fn err(&mut self, msg: &str, token: Token) -> ! {
        let line = self.scanner.line_number(token);
        panic!("Parse error on line {}: {}. {:?}", line, msg, token);
    }

    fn error(&mut self, msg: &str) -> ! {
        let token = self.scanner.next();
        let line = self.scanner.line_number(token);
        panic!("Parse error on line {}: {} . {:?}", line, msg, token);
    }
}
