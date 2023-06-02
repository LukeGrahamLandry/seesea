//! TOKENS -> AST

use crate::ast::{
    BinaryOp, CType, FuncSignature, Function, LiteralValue, MetaExpr, Module, RawExpr, Stmt,
    StructSignature, ValueType,
};
use crate::scanning::{Scanner, Token, TokenType};
use std::rc::Rc;

impl<'src> From<Scanner<'src>> for Module {
    fn from(scanner: Scanner) -> Self {
        let name = scanner.name.clone();
        let mut parser = Parser {
            scanner,
            program: Module::new(name),
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
                // TODO: function returning struct without typedef
                TokenType::Struct => {
                    self.parse_struct_def();
                    self.expect(TokenType::Semicolon);
                }
                TokenType::TypeDef => self.parse_type_def(),
                _ => self.parse_function(),
            }
        }
    }

    fn parse_type_def(&mut self) {
        self.expect(TokenType::TypeDef);

        let is_def = self.scanner.peek_n(0).kind == TokenType::Struct
            && self.scanner.peek_n(1).kind == TokenType::Identifier
            && self.scanner.peek_n(2).kind == TokenType::LeftBrace;

        let ty = if !is_def {
            self.read_type().unwrap()
        } else {
            let name = self.parse_struct_def();
            CType::direct(ValueType::Struct(name))
        };
        let alias = self.read_ident("Expected alias after 'typedef <type>'");
        self.program.type_defs.insert(alias.into(), ty);
        self.expect(TokenType::Semicolon);
    }

    /// struct IDENT { TYPE IDENT }
    fn parse_struct_def(&mut self) -> Rc<str> {
        self.expect(TokenType::Struct);
        let name = self.read_ident("Expected name in struct definition.");
        self.expect(TokenType::LeftBrace);
        let mut fields: Vec<(String, CType)> = vec![];

        while self.scanner.peek() != TokenType::RightBrace {
            let ty = self.read_type().expect("Expected type for struct field.");
            let name = self.read_ident("Expected name for struct field.");
            self.expect(TokenType::Semicolon);
            assert!(!fields.iter().any(|f| f.0 == name));
            fields.push((name, ty));
        }
        let name: Rc<str> = name.into();
        self.program.structs.push(StructSignature {
            name: name.clone(),
            fields,
        });
        self.expect(TokenType::RightBrace);
        name
    }

    /// TYPE NAME() STMT
    fn parse_function(&mut self) {
        let returns = self.read_type().expect("expected function declaration");
        let name = self.read_ident("expected function name");
        self.expect(TokenType::LeftParen);
        let mut args = vec![];
        let mut names = vec![];
        let mut has_var_args = false;
        while !self.scanner.matches(TokenType::RightParen) {
            if self.scanner.matches(TokenType::ThreeDots) {
                self.scanner.consume(TokenType::RightParen);
                has_var_args = true;
                break;
            }
            args.push(self.read_type().expect("Function arg requires type."));
            names.push(self.read_ident("Function arg requires name.").into()); // TODO: headers/forward defs dont
            if !self.scanner.matches(TokenType::Comma) {
                assert_eq!(
                    self.scanner.peek(),
                    TokenType::RightParen,
                    "Expected ')' or ',' after function arg."
                );
            }
        }

        let signature = FuncSignature {
            param_types: args,
            param_names: names,
            return_type: returns,
            name: name.into(),
            has_var_args,
        };

        if self.scanner.matches(TokenType::Semicolon) {
            self.program.forward_declarations.push(signature);
        } else {
            let body = self.parse_stmt();
            self.program.functions.push(Function {
                body,
                signature,
                arg_vars: None,
            });
        }
    }

    /// STMT
    fn parse_stmt(&mut self) -> Stmt {
        // { STMT* }
        if self.scanner.matches(TokenType::LeftBrace) {
            let mut body = vec![];
            while !self.scanner.matches(TokenType::RightBrace) {
                body.push(self.parse_stmt());
            }
            return Stmt::Block { body };
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

        if self.scanner.peek() == TokenType::For {
            return self.parse_for_loop();
        }

        // ;
        if self.scanner.matches(TokenType::Semicolon) {
            return Stmt::Nothing;
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
            RawExpr::Default(kind.clone()).debug(self.scanner.prev())
        } else {
            self.expect(TokenType::Equal);
            let value = self.parse_expr();
            self.expect(TokenType::Semicolon);
            value
        };
        Stmt::DeclareVar {
            name: name.into(),
            kind: kind.clone(),
            value: Box::new(value),
            variable: None,
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
            Stmt::Block { body: vec![] }
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

    /// for (STMT? EXPR? EXPR?) STMT
    fn parse_for_loop(&mut self) -> Stmt {
        self.expect(TokenType::For);
        self.expect(TokenType::LeftParen);
        let initializer = self.parse_stmt();
        let condition = self.parse_stmt();
        let condition = match condition {
            Stmt::Expression { expr } => expr,
            Stmt::Nothing => {
                RawExpr::Literal(LiteralValue::IntNumber(1)).boxed(self.scanner.prev())
            }
            _ => self.error("For loop condition must be expr or nothing."),
        };

        let increment = if self.scanner.peek() == TokenType::RightParen {
            RawExpr::Literal(LiteralValue::IntNumber(0)).debug(self.scanner.peek_n(0))
        } else {
            self.parse_expr()
        };
        self.expect(TokenType::RightParen);
        let body = self.parse_stmt();
        Stmt::For {
            initializer: Box::new(initializer),
            condition,
            increment: Box::new(increment),
            body: Box::new(body),
        }
    }

    // TODO: it parses long* x = &a; as (long * x) = &a; because statement checker doesnt know long* is a type
    /// EXPR
    fn parse_expr(&mut self) -> MetaExpr {
        let left = self.parse_unary();
        let op = match self.scanner.peek() {
            TokenType::Plus => BinaryOp::Add,
            TokenType::Greater => BinaryOp::GreaterThan,
            TokenType::Less => BinaryOp::LessThan,
            TokenType::Equal => {
                let op_token = self.scanner.advance();
                let right = self.parse_expr();
                return RawExpr::Assign(Box::new(left), Box::new(right)).debug(op_token);
            }
            TokenType::Minus => BinaryOp::Subtract,
            TokenType::Star => BinaryOp::Multiply,
            TokenType::Slash => BinaryOp::Divide,
            TokenType::GreaterEqual => BinaryOp::GreaterOrEqual,
            TokenType::LessEqual => BinaryOp::LessOrEqual,
            _ => return left, // todo: only some tokens are valid here
        };

        let op_token = self.scanner.advance();
        let right = self.parse_expr();
        RawExpr::Binary {
            left: Box::new(left),
            right: Box::new(right),
            op,
        }
        .debug(op_token)
    }

    fn parse_unary(&mut self) -> MetaExpr {
        let token = self.scanner.peek_n(0);
        match self.scanner.peek() {
            TokenType::Minus => {
                self.scanner.advance();
                RawExpr::Binary {
                    left: RawExpr::Literal(LiteralValue::IntNumber(0)).boxed(token),
                    right: Box::new(self.parse_unary()),
                    op: BinaryOp::Subtract,
                }
                .debug(token)
            }
            TokenType::Star => {
                self.scanner.advance();
                RawExpr::DerefPtr(Box::new(self.parse_unary())).debug(token)
            }
            TokenType::Ampersand => {
                self.scanner.advance();
                RawExpr::AddressOf(Box::new(self.parse_unary())).debug(token)
            }
            TokenType::SizeOf => {
                let so = self.expect(TokenType::SizeOf);
                let t = self.expect(TokenType::LeftParen);
                if let Some(ty) = self.read_type() {
                    self.expect(TokenType::RightParen);
                    RawExpr::SizeOfType(ty).debug(token)
                } else {
                    self.scanner.replace(t);
                    self.scanner.replace(so);
                    todo!()
                }
            }
            _ => self.parse_primary(),
        }
    }

    fn parse_primary(&mut self) -> MetaExpr {
        let mut expr = self.parse_basic();
        loop {
            let token = self.scanner.peek_n(0);
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

                    expr = RawExpr::Call {
                        func: Box::new(expr),
                        args,
                    }
                    .debug(token)
                }
                TokenType::Period => {
                    self.expect(TokenType::Period);
                    let name = self.read_ident("Expected field name.");
                    expr = RawExpr::GetField(Box::new(expr), name.into()).debug(token)
                }
                TokenType::Arrow => {
                    self.expect(TokenType::Arrow);
                    let name = self.scanner.consume(TokenType::Identifier);
                    expr = RawExpr::DerefPtr(Box::new(expr)).debug(token);
                    expr = RawExpr::GetField(Box::new(expr), name.lexeme.into()).debug(name);
                }
                _ => return expr,
            }
        }
    }

    /// NAME | NUMBER | (EXPR)
    fn parse_basic(&mut self) -> MetaExpr {
        let token = self.scanner.next();
        match token.kind {
            TokenType::DecimalInt(v) => RawExpr::Literal(LiteralValue::IntNumber(v)),
            TokenType::DecimalFloat(v) => RawExpr::Literal(LiteralValue::FloatNumber(v)),
            // TODO: all should share the same Rc (same for field accesses)
            TokenType::Identifier => RawExpr::GetVar(token.lexeme.into()),
            TokenType::LeftParen => match self.read_type() {
                None => {
                    let expr = self.parse_expr();
                    self.expect(TokenType::RightParen);
                    expr.expr
                }
                Some(target) => {
                    self.expect(TokenType::RightParen);
                    let expr = self.parse_expr();
                    RawExpr::LooseCast(Box::new(expr), target)
                }
            },
            TokenType::StringLiteral => RawExpr::Literal(LiteralValue::StringBytes(
                token.lexeme[1..(token.lexeme.len() - 1)].to_string().into(),
            )),
            _ => self.err("Expected primary expr (number or var access)", token),
        }
        .debug(token)
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
                let s = self
                    .program
                    .structs
                    .iter()
                    .find(|s| s.name.as_ref() == name);
                let s = match s {
                    None => self.err("Undeclared struct", name_token),
                    Some(s) => s,
                };
                CType {
                    ty: ValueType::Struct(s.name.clone()),
                    depth: 0,
                }
            }
            TokenType::Identifier => {
                if let Some(ty) = self.program.type_defs.get(token.lexeme).cloned() {
                    self.expect(TokenType::Identifier);
                    ty
                } else {
                    let ty = match token.lexeme {
                        "long" => ValueType::U64,
                        "int" => ValueType::U32,
                        "char" => ValueType::U8,
                        "double" => ValueType::F64,
                        "float" => ValueType::F32,
                        "void" => ValueType::Void,
                        _ => return None,
                    };

                    self.expect(TokenType::Identifier);
                    CType { ty, depth: 0 }
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

    fn expect(&mut self, kind: TokenType) -> Token<'src> {
        let token = self.scanner.next();
        if token.kind != kind {
            self.err(&format!("Expected {:?}", kind), token);
        }
        token
    }

    fn err(&mut self, msg: &str, token: Token) -> ! {
        let line = self.scanner.line_number(token);
        panic!("Parse error on line {}: {}. {:?}", line + 1, msg, token);
    }

    fn error(&mut self, msg: &str) -> ! {
        let token = self.scanner.next();
        let line = self.scanner.line_number(token);
        panic!("Parse error on line {}: {} . {:?}", line + 1, msg, token);
    }
}
