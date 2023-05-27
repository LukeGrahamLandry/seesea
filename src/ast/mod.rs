use crate::ir::Label;

mod parse;
mod print;

pub struct Module {
    pub functions: Vec<Function>,
    pub name: String,
}

pub struct Function {
    pub body: Stmt,
    pub signature: FuncSignature,
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct FuncSignature {
    pub param_types: Vec<CType>,
    pub return_type: CType,
    pub name: String,
    // The names are needed for parsing the body code. They don't live on to LLVM IR currently.
    pub param_names: Vec<String>,
}

// @Speed the expressions here dont need to be boxed
pub enum Stmt {
    Block {
        body: Vec<Stmt>,
        lines: Option<Vec<usize>>,
    },
    Expression {
        expr: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        then_body: Box<Stmt>,
        else_body: Box<Stmt>,
    },
    // While { condition: Box<Expr>, body: Box<Stmt> },
    // For { initializer: Box<Stmt>, condition: Box<Expr>, increment: Box<Expr>, body: Box<Stmt> },
    DeclareVar {
        name: String,
        value: Box<Expr>,
        kind: CType,
    },
    Return {
        value: Option<Box<Expr>>,
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
    Literal {
        value: LiteralValue,
    },
    Default(CType),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Equal,
    GreaterThan,
    LessThan,

    /// This is a fancy special case but since pointer derefs and stuff can be on the left
    /// this seems like a reasonable way to represent it. Not that much weirder than short circuiting bools.
    Assign,
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

#[derive(Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub enum ValueType {
    U64,
    // Struct
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct CType {
    pub ty: ValueType,
    pub depth: u8, // 0 -> not a pointer. if you have ?256 levels of indirection that's a skill issue
}

impl CType {
    #[must_use]
    pub fn deref_type(&self) -> CType {
        assert!(self.depth > 0, "Tried to dereference non-pointer type.");
        let mut other = *self;
        other.depth -= 1;
        other
    }

    #[must_use]
    pub fn ref_type(&self) -> CType {
        let mut other = *self;
        other.depth += 1;
        other
    }

    pub fn is_pointer_to(&self, value_type: &CType) -> bool {
        &self.deref_type() == value_type
    }
}
