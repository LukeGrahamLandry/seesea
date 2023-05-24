mod parse;
mod print;

pub struct Program {
    pub functions: Vec<Function>,
}

pub struct Function {
    pub body: Stmt,
    pub signature: FuncSignature,
}

#[derive(Clone)]
pub struct FuncSignature {
    pub args: Vec<ValueType>,
    pub returns: ValueType,
    pub name: String,
}

pub enum Stmt {
    Block {
        body: Vec<Stmt>,
    },
    Expression {
        expr: Box<Expr>,
    },
    // If { condition: Box<Expr>, then_body: Box<Stmt>, else_body: Box<Stmt> },
    // While { condition: Box<Expr>, body: Box<Stmt> },
    // For { initializer: Box<Stmt>, condition: Box<Expr>, increment: Box<Expr>, body: Box<Stmt> },
    DeclareVar {
        name: String,
        value: Box<Expr>,
        kind: ValueType,
    },
    Return {
        value: Box<Expr>,
    },
}

pub enum Expr {
    Binary {
        left: Box<Expr>,
        right: Box<Expr>,
        op: BinaryOp,
    },
    Unary {
        value: Box<Expr>,
        op: UnaryOp,
    },
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    GetVar {
        name: String,
    },
    SetVar {
        name: String,
        value: Box<Expr>,
    },
    Literal {
        value: LiteralValue,
    },
    Default(ValueType),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Equal,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum UnaryOp {
    Negate,
    Not,
    Deref,
    AddressOf,
}

#[derive(Debug)]
pub enum LiteralValue {
    Number { value: f64 },
    String { value: String },
    Bool { value: bool },
    Null,
}

impl Expr {
    pub fn logical_not(self) -> Expr {
        UnaryOp::Not.apply(self)
    }

    pub fn get_type(&self) -> ValueType {
        todo!()
    }
}

impl BinaryOp {
    pub fn apply(self, left: Expr, right: Expr) -> Expr {
        Expr::Binary {
            left: Box::new(left),
            right: Box::new(right),
            op: self,
        }
    }
}

impl UnaryOp {
    pub fn apply(self, value: Expr) -> Expr {
        Expr::Unary {
            value: Box::new(value),
            op: self,
        }
    }
}

impl From<LiteralValue> for Expr {
    fn from(value: LiteralValue) -> Self {
        Expr::Literal { value }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ValueType {
    U64,
}

pub fn five_plus_ten() -> Function {
    let body = Stmt::Block {
        body: vec![
            Stmt::DeclareVar {
                name: "x".to_string(),
                value: Box::new(Expr::Literal {
                    value: LiteralValue::Number { value: 5.0 },
                }),
                kind: ValueType::U64,
            },
            Stmt::DeclareVar {
                name: "y".to_string(),
                value: Box::new(Expr::Literal {
                    value: LiteralValue::Number { value: 10.0 },
                }),
                kind: ValueType::U64,
            },
            Stmt::DeclareVar {
                name: "z".to_string(),
                value: Box::new(Expr::Binary {
                    left: Box::new(Expr::GetVar {
                        name: "x".to_string(),
                    }),
                    right: Box::new(Expr::GetVar {
                        name: "y".to_string(),
                    }),
                    op: BinaryOp::Add,
                }),
                kind: ValueType::U64,
            },
            Stmt::Return {
                value: Box::new(Expr::GetVar {
                    name: "z".to_string(),
                }),
            },
        ],
    };
    Function {
        body,
        signature: FuncSignature {
            args: vec![],
            returns: ValueType::U64,
            name: "five_plus_ten".to_string(),
        },
    }
}
