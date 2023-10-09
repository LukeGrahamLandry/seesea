//! TOKENS -> AST

use crate::ast::{
    AnyStmt, BinaryOp, CType, FuncSignature, Function, LiteralValue, MetaExpr, Module, RawExpr,
    StructSignature, ValueType,
};
use crate::scanning::{Scanner, Token, TokenType};
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

pub type Stmt = AnyStmt<MetaExpr>;

impl<'src> From<Scanner<'src>> for Module {
    fn from(scanner: Scanner) -> Self {
        let name = scanner.name.clone().into();
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

// TODO: should clean up the advancing and be more constant in how i check the next token but also this is the boring part.
//       need to care more about error messages, scanner should never panic
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

    // typedef syntax is the same as variable declaration
    // `typedef struct { ... }* name[3];` makes "name" an alias for the type s*[3]
    // `struct { ... }* name[3];` makes "name" a variable with the type s*[3]
    // Function return types are also the same but can't be arrays.  `struct { ... } func(...)`
    // As a type, you can use `struct { int a; }` or `struct Name1` or `Name2`
    // No structural equivalence. If you declare a named struct, you can't use a different one with the same fields.
    // Typedefs don't create new types, just aliases.
    // Names can't conflict but typedefs and struct Whatever have different namespaces.
    // Nested structs can have names `struct A { struct B { int c; } d; }`

    // sizeof(Type) -> take, read_prefix_type
    // Type Name = Value -> read_name_and_type, take, parse_expr
    // (Type) Value -> read_prefix_type, parse_expr

    // TODO: maybe instead of this. split on (base)+(name and modifiers) then can use that for var decl like `int *a, b`
    // This is separate because of casts and sizeof.
    /// Reads the part of a type before the name (base + pointer).
    fn read_prefix_type(&mut self) -> Option<CType> {
        if !self.looking_at_start_of_type() {
            return None;
        }
        let first = self.scanner.peek_n(0);

        let mut ty = match first.kind {
            TokenType::Struct => self.parse_struct_type(),
            TokenType::Identifier => self.read_type_identifier(),
            _ => unreachable!("looking_at_start_of_type was wrong!"),
        };

        // Now read any number of pointers.
        while self.scanner.matches(TokenType::Star) {
            ty = ty.ref_type();
        }

        Some(ty)
    }

    fn read_name_and_type(&mut self) -> Option<(String, CType)> {
        let mut ty = match self.read_prefix_type() {
            None => return None,
            Some(ty) => ty,
        };

        let name = self.read_ident("Expected name after type.");

        // Maybe this is an array.
        if self.scanner.matches(TokenType::LeftSquareBracket) {
            if ty.count != 1 {
                self.err(
                    "TODO: Nested arrays are not supported.",
                    self.scanner.peek_n(0),
                );
            }
            let size = self.parse_expr();
            self.expect(TokenType::RightSquareBracket);
            ty.count = size.comptime_usize().unwrap_or_else(|| {
                self.err(
                    "Static array size must be an integer literal.",
                    self.scanner.peek_n(0),
                );
            });
        }

        Some((name, ty))
    }

    /// `struct Name` or `struct { ... }` or `struct Name { ... }`
    fn parse_struct_type(&mut self) -> CType {
        let second = self.scanner.peek_n(1);
        let third = self.scanner.peek_n(2).kind;

        // Anon struct decl, give it a random internal name that can't be referred to.
        // TODO: this seems dumb. use indexes everywhere instead? then ValueType doesn't need an Rc.
        let name = if second.kind == TokenType::LeftBrace {
            self.expect(TokenType::Struct);
            let fields = self.parse_struct_fields();
            let name = Parser::random_str();
            self.program.structs.push(StructSignature {
                name: name.clone(),
                fields,
            });
            name
        } else if second.kind == TokenType::Identifier && third == TokenType::LeftBrace {
            // Named struct decl. Make sure no collide.
            let name = second.lexeme;
            if self.program.get_struct_by_name(name).is_some() {
                self.error(&format!("Name collision of struct {}", name))
            }
            self.parse_struct_def()
        } else if second.kind == TokenType::Identifier {
            // Reference prev struct
            self.expect(TokenType::Struct);
            let id = self.read_ident("unreachable");
            if self.program.get_struct_by_name(&id).is_some() {
                id.into()
            } else {
                self.error(&format!("Undefined struct {}", id))
            }
        } else {
            self.error("Expected `struct Name` or `struct { ... }` or `struct Name { ... }`");
        };

        CType::direct(ValueType::Struct(name))
    }

    fn random_str() -> Rc<str> {
        let ts = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("Time went backwards");
        format!("__{}", ts.as_micros()).into()
    }

    const BUILTIN_TYPES: &'static [&'static str] =
        &["char", "long", "int", "float", "double", "void"];

    // Only certain tokens can be the start of a type.
    // Need to recognise these without consuming tokens to know if we're declaring a variable.
    fn looking_at_start_of_type(&self) -> bool {
        let first = self.scanner.peek_n(0);
        match first.kind {
            TokenType::Struct => true,
            TokenType::Identifier => {
                // Might be an expression
                self.program.type_defs.contains_key(first.lexeme)
                    || Parser::BUILTIN_TYPES.contains(&first.lexeme)
            }
            _ => false,
        }
    }

    fn parse_type_def(&mut self) {
        self.expect(TokenType::TypeDef);
        let (alias, ty) = self
            .read_name_and_type()
            .expect("Expected Type name; after typedef");
        let prev = self.program.type_defs.get(alias.as_str());
        if let Some(prev) = prev {
            self.error(&format!(
                "typedef collision {}\n old: {:?} \n new: {:?} ",
                alias, prev, ty
            ))
        }
        self.program.type_defs.insert(alias.into(), ty);
        self.expect(TokenType::Semicolon);
    }

    /// struct IDENT { TYPE IDENT }
    fn parse_struct_def(&mut self) -> Rc<str> {
        self.expect(TokenType::Struct);
        let name = self.read_ident("Expected name in struct definition.");
        let fields = self.parse_struct_fields();
        let name: Rc<str> = name.into();
        self.program.structs.push(StructSignature {
            name: name.clone(),
            fields,
        });
        name
    }

    /// { TYPE IDENT }
    fn parse_struct_fields(&mut self) -> Vec<(String, CType)> {
        self.expect(TokenType::LeftBrace);
        let mut fields: Vec<(String, CType)> = vec![];

        while self.scanner.peek() != TokenType::RightBrace {
            let (name, ty) = self
                .read_name_and_type()
                .expect("Expected Type Name; inside struct");
            self.expect(TokenType::Semicolon);
            assert!(
                !fields.iter().any(|f| f.0 == name),
                "field name collision {}",
                name
            );
            fields.push((name, ty));
        }
        self.expect(TokenType::RightBrace);

        fields
    }

    // TODO: macro for unwrapping an option and giving error message with token context.

    /// TYPE NAME() STMT
    fn parse_function(&mut self) {
        // TODO: function cant return an array like `int foo[](...args){}`
        let (name, returns) = self
            .read_name_and_type()
            .expect("Expected Type Name(...) for function decl.");
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
            // TODO: headers/forward defs dont require a name.
            let (name, ty) = self
                .read_name_and_type()
                .expect("Expected func arg Type Name. (even for forward def, TODO: fix)");
            args.push(ty);
            names.push(name.into());
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
        return match self.scanner.peek() {
            // { STMT* }
            TokenType::LeftBrace => {
                self.scanner.advance();
                let mut body = vec![];
                while !self.scanner.matches(TokenType::RightBrace) {
                    body.push(self.parse_stmt());
                }
                Stmt::Block { body }
            }
            // return EXPR?;
            TokenType::Return => {
                self.scanner.advance();
                let value = if self.scanner.matches(TokenType::Semicolon) {
                    None
                } else {
                    let value = self.parse_expr();
                    self.expect(TokenType::Semicolon);
                    Some(value)
                };
                Stmt::Return { value }
            }
            TokenType::If => self.parse_if(),
            TokenType::While => self.parse_while_loop(),
            TokenType::For => self.parse_for_loop(),
            TokenType::Do => self.parse_do_while_loop(),
            TokenType::Semicolon => {
                self.scanner.advance();
                Stmt::Nothing
            }
            TokenType::Else => self.error(
                "Keyword 'else' must be preceded by 'if STMT' (maybe you forgot a closing '}')",
            ),
            TokenType::Break => {
                self.scanner.advance();
                self.scanner.consume(TokenType::Semicolon);
                Stmt::Break
            }
            TokenType::Continue => {
                self.scanner.advance();
                self.scanner.consume(TokenType::Semicolon);
                Stmt::Continue
            }
            _ => {
                if self.looking_at_start_of_type() {
                    self.parse_declare_variable()
                } else {
                    // EXPR;
                    let expr = self.parse_expr();
                    if !self.scanner.matches(TokenType::Semicolon) {
                        self.error("Expected semicolon terminating expression statement.")
                    }
                    Stmt::Expression { expr }
                }
            }
        };
    }

    /// TYPE NAME = EXPR?;
    fn parse_declare_variable(&mut self) -> Stmt {
        let (name, ty) = self
            .read_name_and_type()
            .expect("Expected variable declaration");
        let value = match self.scanner.peek() {
            TokenType::Semicolon => {
                self.scanner.advance();
                RawExpr::Default(ty.clone()).debug(self.scanner.prev())
            }
            TokenType::Equal => {
                self.scanner.advance();
                let value = self.parse_expr();
                self.expect(TokenType::Semicolon);
                value
            }
            // This is a pain because *[] modifies the name not the type.
            TokenType::Comma => self.error("TODO: multiple var decl with commas. "),
            _ => self.err(
                "Unexpected token after variable declaration.",
                self.scanner.peek_n(0),
            ),
        };
        Stmt::DeclareVar {
            name: name.into(),
            kind: ty,
            value,
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
            condition,
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
            condition,
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
                RawExpr::Literal(LiteralValue::IntNumber(1)).debug(self.scanner.prev())
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
            increment,
            body: Box::new(body),
        }
    }

    /// do STMT while (EXPR);
    fn parse_do_while_loop(&mut self) -> Stmt {
        self.expect(TokenType::Do);
        let body = self.parse_stmt();
        self.expect(TokenType::While);
        self.expect(TokenType::LeftParen);
        let condition = self.parse_expr();
        self.expect(TokenType::RightParen);
        self.expect(TokenType::Semicolon);
        Stmt::DoWhile {
            condition,
            body: Box::new(body),
        }
    }

    // TODO: operator precedence. everything has a priority value so you can check if the next thing is smaller than yours and you can take it
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
            TokenType::EqualEqual => BinaryOp::Equality,
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
                if self.looking_at_start_of_type() {
                    let ty = self.read_prefix_type().unwrap();
                    self.expect(TokenType::RightParen);
                    RawExpr::SizeOfType(ty).debug(token)
                } else {
                    self.scanner.replace(t);
                    self.scanner.replace(so);
                    todo!("typeof expression but dont eval just type check it")
                }
            }
            _ => self.parse_primary(),
        }
    }

    /// EXPR(EXPR,*) | EXPR.IDENT | EXPR->IDENT | EXPR\[EXPR] | EXPR
    fn parse_primary(&mut self) -> MetaExpr {
        let mut expr = self.parse_basic();
        // I haven't thought about precedence yet so for now we just eat as many suffix-operators as possible.
        loop {
            let token = self.scanner.peek_n(0);
            match self.scanner.peek() {
                TokenType::LeftParen => {
                    let args =
                        self.comma_seperated_exprs(TokenType::LeftParen, TokenType::RightParen);

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
                    // This could have it's own node type but I think it's purely syntax sugar.
                    self.expect(TokenType::Arrow);
                    let name = self.scanner.consume(TokenType::Identifier);
                    expr = RawExpr::DerefPtr(Box::new(expr)).debug(token);
                    expr = RawExpr::GetField(Box::new(expr), name.lexeme.into()).debug(name);
                }
                TokenType::LeftSquareBracket => {
                    // This is sugar for incrementing the pointer by the size of elements but sizes are only known after resolving everything.
                    self.expect(TokenType::LeftSquareBracket);
                    let index = self.parse_expr();
                    self.expect(TokenType::RightSquareBracket);
                    expr = RawExpr::ArrayIndex {
                        ptr: Box::new(expr),
                        index: Box::new(index),
                    }
                    .debug(token);
                }
                _ => return expr,
            }
        }
    }

    fn comma_seperated_exprs(&mut self, first: TokenType, last: TokenType) -> Vec<MetaExpr> {
        self.expect(first);
        let mut args = vec![];
        while !self.scanner.matches(last) {
            args.push(self.parse_expr());
            if !self.scanner.matches(TokenType::Comma) {
                assert_eq!(
                    self.scanner.peek(),
                    TokenType::RightParen,
                    "Expected ')' or ',' after function arg."
                );
            }
        }
        args
    }

    /// NAME | NUMBER | "STRING" | (EXPR) | (TYPE) EXPR
    fn parse_basic(&mut self) -> MetaExpr {
        let token = self.scanner.take();
        match token.kind {
            TokenType::DecimalInt(v) => RawExpr::Literal(LiteralValue::IntNumber(v)),
            TokenType::DecimalFloat(v) => RawExpr::Literal(LiteralValue::FloatNumber(v)),
            // TODO: all should share the same Rc (same for field accesses)
            TokenType::Identifier => RawExpr::GetVar(token.lexeme.into()),
            TokenType::LeftParen => {
                // Either a sub-expression or a type cast.
                if self.looking_at_start_of_type() {
                    let target = self.read_prefix_type().unwrap();
                    self.expect(TokenType::RightParen);
                    let expr = self.parse_expr();
                    RawExpr::LooseCast(Box::new(expr), target)
                } else {
                    let expr = self.parse_expr();
                    self.expect(TokenType::RightParen);
                    expr.expr
                }
            }
            TokenType::StringLiteral => RawExpr::Literal(LiteralValue::StringBytes(
                token.lexeme[1..(token.lexeme.len() - 1)].to_string().into(),
            )),
            _ => self.err("Expected primary expr (number or var access)", token),
        }
        .debug(token)
    }

    // Reads a base type from the next identifier. ie. `float` or something typedef-ed.
    fn read_type_identifier(&mut self) -> CType {
        let name = self.expect(TokenType::Identifier).lexeme;
        if let Some(ty) = self.program.type_defs.get(name).cloned() {
            ty
        } else {
            let ty = match name {
                "long" => ValueType::U64,
                "int" => ValueType::U32,
                "char" => ValueType::U8,
                "double" => ValueType::F64,
                "float" => ValueType::F32,
                "void" => ValueType::Void,
                _ => self.error(&format!("Unknown type name '{}'", name)),
            };

            CType::direct(ty)
        }
    }

    /// NAME
    fn read_ident(&mut self, msg: &str) -> String {
        let token = self.scanner.take();
        if token.kind != TokenType::Identifier {
            self.err(msg, token);
        }
        token.lexeme.into()
    }

    fn expect(&mut self, kind: TokenType) -> Token<'src> {
        let token = self.scanner.take();
        if token.kind != kind {
            self.err(&format!("Expected {:?}", kind), token);
        }
        token
    }

    fn err(&mut self, msg: &str, token: Token) -> ! {
        panic!(
            "Parse error on line {}: {}. {:?}",
            token.line + 1,
            msg,
            token
        );
    }

    fn error(&mut self, msg: &str) -> ! {
        let token = self.scanner.take();
        panic!(
            "Parse error on line {}: {} . {:?}",
            token.line + 1,
            msg,
            token
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::parse::Parser;
    use crate::ast::{CType, Module, ValueType};
    use crate::scanning::Scanner;

    enum TypeSpec {
        Array(Box<TypeSpec>, usize),
        Pointer(Box<TypeSpec>),
        Struct(Option<String>, Vec<(String, TypeSpec)>),
        Primitive(ValueType),
    }

    #[test]
    fn parse_types() {
        expect_nat(
            "int *x",
            "x",
            TypeSpec::Pointer(Box::new(TypeSpec::Primitive(ValueType::U32))),
        );
        expect_nat(
            "int x[10]",
            "x",
            TypeSpec::Array(Box::new(TypeSpec::Primitive(ValueType::U32)), 10),
        );
        expect_nat(
            "struct C { long a; float *b; } test",
            "test",
            TypeSpec::Struct(
                Some("C".into()),
                vec![
                    ("a".into(), TypeSpec::Primitive(ValueType::U64)),
                    (
                        "b".into(),
                        TypeSpec::Pointer(Box::new(TypeSpec::Primitive(ValueType::F32))),
                    ),
                ],
            ),
        );
        expect_nat(
            "struct { double a; } test",
            "test",
            TypeSpec::Struct(
                None,
                vec![("a".into(), TypeSpec::Primitive(ValueType::F64))],
            ),
        );
        expect_nat(
            "struct c { struct { int b; } a; } d",
            "d",
            TypeSpec::Struct(
                Some("c".into()),
                vec![(
                    "a".into(),
                    TypeSpec::Struct(
                        None,
                        vec![("b".into(), TypeSpec::Primitive(ValueType::U32))],
                    ),
                )],
            ),
        );
    }

    fn expect_nat(src: &str, name: &str, ty: TypeSpec) {
        let mut parser = Parser {
            scanner: Scanner::new(src, "".into()),
            program: Module::new("".into()),
        };
        let (n, t) = parser.read_name_and_type().unwrap();
        let module = parser.program;
        assert_eq!(&n, name);
        eql(&module, &t, &ty);
    }

    fn eql(module: &Module, ty: &CType, expected: &TypeSpec) {
        match expected {
            TypeSpec::Array(elem, len) => {
                assert_eq!(*len, ty.count);
                let mut entries = ty.clone();
                entries.count = 1;
                eql(module, &entries, elem);
            }
            TypeSpec::Pointer(inner) => {
                eql(module, &ty.ref_type(), inner);
            }
            TypeSpec::Struct(name, fields) => {
                let found_struct = module.get_struct(ty);
                if let Some(name) = name {
                    assert_eq!(name.as_str(), found_struct.name.as_ref());
                }
                let it = found_struct.fields.iter().zip(fields.iter());
                for ((n1, t1), (n2, t2)) in it {
                    assert_eq!(n1, n2);
                    eql(module, t1, t2);
                }
            }
            TypeSpec::Primitive(prim) => {
                assert!(!matches!(prim, ValueType::Struct(_)));
                assert_eq!(*prim, ty.ty);
            }
        }
    }
}
