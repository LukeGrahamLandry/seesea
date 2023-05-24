mod print;

pub enum Stmt {
    Block { body: Vec<Stmt> },
    Expression { expr: Box<Expr> },
    // If { condition: Box<Expr>, then_body: Box<Stmt>, else_body: Box<Stmt> },
    // While { condition: Box<Expr>, body: Box<Stmt> },
    // For { initializer: Box<Stmt>, condition: Box<Expr>, increment: Box<Expr>, body: Box<Stmt> },
    DeclareVar { name: String, value: Box<Expr> },
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

#[derive(Debug)]
pub enum ValueType {
    Struct(String),
    Int,
}
