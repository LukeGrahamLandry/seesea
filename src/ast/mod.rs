mod parse;
mod print;

pub struct Module {
    pub functions: Vec<Function>,
    pub structs: Vec<StructSignature>,
    pub name: String,
}

pub struct Function {
    pub body: Option<Stmt>,
    pub signature: FuncSignature,
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct FuncSignature {
    pub param_types: Vec<CType>,
    pub return_type: CType,
    pub name: String,
    // The names are needed for parsing the body code. They don't live on to LLVM IR currently.
    pub param_names: Vec<String>,
    pub has_var_args: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StructSignature {
    pub name: &'static str,
    pub fields: Vec<(String, CType)>,
}

impl StructSignature {
    pub fn field_type(&self, name: &str) -> CType {
        self.fields.iter().find(|f| f.0 == name).unwrap().1
    }

    pub fn field_index(&self, name: &str) -> usize {
        self.fields.iter().position(|f| f.0 == name).unwrap()
    }
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
    // Does the backend need different handling for while/for/do_while or should I just transform the ast so all become DoWhile
    While {
        condition: Box<Expr>,
        body: Box<Stmt>,
    },
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
    GetField {
        object: Box<Expr>,
        name: String,
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
    StringBytes { value: String },
}

#[derive(Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub enum ValueType {
    U64,
    U8,
    U32,
    Struct(&'static str),
}

// I'd really like these to stay Copy. Maybe give them an 'ast lifetime so they can reference struct prototypes.
#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct CType {
    pub ty: ValueType,
    pub depth: u8, // 0 -> not a pointer. if you have ?256 levels of indirection that's a skill issue
}

impl Module {
    // TODO: hash map?
    pub fn get_func(&self, name: &str) -> Option<&Function> {
        self.functions
            .iter()
            .find(|&func| func.signature.name == name)
    }

    pub fn get_struct(&self, name: &str) -> Option<&StructSignature> {
        self.structs.iter().find(|&func| func.name == name)
    }
}

impl Expr {
    pub fn logical_not(self) -> Expr {
        UnaryOp::Not.apply(self)
    }

    // TODO: I'm tempted to put type resolution logic here, separate from the IR generation.
    //       It would mean I could type check the program before starting IR stuff.
    //       But it's annoying to do an extra traversal here where the ir gen will do it again anyway.
    //       Convoluted visitor abstraction that let's you write the passes separately but run them in one traversal?
    //       But I think it would just be annoying to write code that way.
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

impl CType {
    pub fn int() -> CType {
        CType {
            ty: ValueType::U64,
            depth: 0,
        }
    }

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

    pub fn is_struct(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::Struct(_))
    }

    pub fn is_basic(&self) -> bool {
        self.depth > 0 || !matches!(self.ty, ValueType::Struct(_))
    }

    pub fn struct_name(&self) -> &str {
        assert!(self.is_struct());
        match self.ty {
            ValueType::Struct(name) => name,
            _ => unreachable!(),
        }
    }
}
