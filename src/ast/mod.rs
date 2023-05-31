use std::borrow::Borrow;
use std::mem::size_of;
use std::rc::Rc;

mod parse;
mod print;

pub struct EitherModule<Func: FuncRepr> {
    // Order matters (for not needing forward declarations)
    pub functions: Vec<Func>,
    pub structs: Vec<StructSignature>,
    pub name: String,
    pub forward_declarations: Vec<FuncSignature>,
}

pub type Module = EitherModule<Function>;

pub struct Function {
    pub body: Stmt,
    pub signature: FuncSignature,
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct FuncSignature {
    pub param_types: Vec<CType>,
    pub return_type: CType,
    pub name: Rc<str>,
    // The names are needed for parsing the body code. They don't live on to LLVM IR currently.
    pub param_names: Vec<Rc<str>>,
    pub has_var_args: bool,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct StructSignature {
    pub name: Rc<str>,
    pub fields: Vec<(String, CType)>,
}

impl StructSignature {
    pub fn field_type(&self, name: &str) -> &CType {
        &self.fields.iter().find(|f| f.0 == name).unwrap().1
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
        name: Rc<str>,
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
        name: Rc<str>,
    },
    GetVar {
        name: Rc<str>,
    },
    Literal {
        value: LiteralValue,
    },
    Default(CType),
    LooseCast {
        value: Box<Expr>,
        target: CType,
    },
    SizeOfType(CType),
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
    GreaterOrEqual,
    LessOrEqual,
    FollowPtr,

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

    // Decide what type the operand would be and return its size but don't evaluate it.
    NoEvalSizeOf,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LiteralValue {
    IntNumber(u64),
    FloatNumber(f64),
    StringBytes(Rc<str>),
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum ValueType {
    U64,
    U8,
    U32,
    F64,
    F32,
    Struct(Rc<str>),
    Void,
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct CType {
    pub ty: ValueType,
    pub depth: u8, // 0 -> not a pointer. if you have ?256 levels of indirection that's a skill issue
}

impl<Func: FuncRepr> EitherModule<Func> {
    pub fn new(name: String) -> Self {
        Self {
            functions: vec![],
            structs: vec![],
            name,
            forward_declarations: vec![],
        }
    }

    pub fn get_func(&self, name: &str) -> Option<&Func> {
        self.functions
            .iter()
            .find(|&func| func.get_signature().name.as_ref() == name)
    }

    pub fn get_func_signature(&self, name: &str) -> Option<&FuncSignature> {
        self.functions
            .iter()
            .map(FuncRepr::get_signature)
            .find(|&func| func.name.as_ref() == name)
            .or_else(|| {
                self.forward_declarations
                    .iter()
                    .find(|&func| func.name.as_ref() == name)
            })
    }

    pub fn get_struct(&self, name: impl AsRef<str>) -> Option<&StructSignature> {
        self.structs
            .iter()
            .find(|&func| func.name.as_ref() == name.as_ref())
    }

    pub fn size_of(&self, ty: impl Borrow<CType>) -> usize {
        let ty = ty.borrow();
        if ty.depth > 0 {
            assert_eq!(size_of::<usize>(), size_of::<u64>());
            return 8;
        }

        match &ty.ty {
            ValueType::U64 => 8,
            ValueType::U8 => 1,
            ValueType::U32 => 4,
            ValueType::F64 => 8,
            ValueType::F32 => 4,
            ValueType::Void => 0,
            ValueType::Struct(name) => {
                let def = self.get_struct(name).unwrap();
                let mut size = 0;
                for (_, field) in &def.fields {
                    size += self.size_of(field);
                }
                size
            }
        }
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

    pub fn direct(ty: ValueType) -> CType {
        CType { ty, depth: 0 }
    }

    #[must_use]
    pub fn deref_type(&self) -> CType {
        assert!(self.depth > 0, "Tried to dereference non-pointer type.");
        let mut other = self.clone();
        other.depth -= 1;
        other
    }

    #[must_use]
    pub fn ref_type(&self) -> CType {
        let mut other = self.clone();
        other.depth += 1;
        other
    }

    pub fn is_pointer_to(&self, value_type: impl Borrow<CType>) -> bool {
        &self.deref_type() == value_type.borrow()
    }

    pub fn is_struct(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::Struct(_))
    }

    pub fn is_basic(&self) -> bool {
        self.depth > 0 || !matches!(self.ty, ValueType::Struct(_))
    }

    pub fn is_raw_void(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::Void)
    }

    pub fn is_raw_int(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::U8 | ValueType::U32 | ValueType::U64)
    }

    pub fn is_raw_float(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::F32 | ValueType::F64)
    }

    pub fn is_ptr(&self) -> bool {
        self.depth > 0
    }

    pub fn struct_name(&self) -> &str {
        assert!(self.is_struct());
        match &self.ty {
            ValueType::Struct(name) => name.as_ref(),
            _ => unreachable!(),
        }
    }
}

pub trait FuncRepr {
    fn get_signature(&self) -> &FuncSignature;
}

impl FuncRepr for Function {
    fn get_signature(&self) -> &FuncSignature {
        &self.signature
    }
}
