use crate::resolve::VariableRef;
use crate::scanning::Token;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::mem::size_of;
use std::ops::Deref;
use std::rc::Rc;

mod parse;
pub mod print;

pub struct AnyModule<Func: FuncRepr> {
    // Order matters (for not needing forward declarations)
    pub functions: Vec<Func>,
    pub structs: Vec<StructSignature>,
    pub name: Rc<str>,
    pub forward_declarations: Vec<FuncSignature>,
    pub type_defs: HashMap<Rc<str>, CType>,
}

pub type Module = AnyModule<Function>;
pub type Function = AnyFunction<MetaExpr>;

pub struct AnyFunction<Expr> {
    pub body: AnyStmt<Expr>,
    pub signature: FuncSignature,
    pub arg_vars: Option<Vec<VariableRef>>,
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

pub enum AnyStmt<Expr> {
    Block {
        body: Vec<AnyStmt<Expr>>,
    },
    Expression {
        expr: Expr,
    },
    If {
        condition: Expr,
        then_body: Box<AnyStmt<Expr>>,
        else_body: Box<AnyStmt<Expr>>,
    },
    // Does the backend need different handling for while/for/do_while or should I just transform the ast so all become DoWhile
    While {
        condition: Expr,
        body: Box<AnyStmt<Expr>>,
    },
    For {
        initializer: Box<AnyStmt<Expr>>,
        condition: Expr,
        increment: Expr,
        body: Box<AnyStmt<Expr>>,
    },
    DeclareVar {
        name: Rc<str>,
        value: Expr,
        kind: CType,
        variable: Option<VariableRef>, // TODO clean this up
    },
    Return {
        value: Option<Expr>,
    },
    Nothing,
}

pub enum RawExpr {
    Binary {
        left: Box<MetaExpr>,
        right: Box<MetaExpr>,
        op: BinaryOp,
    },
    Unary(UnaryOp, Box<MetaExpr>),
    Call {
        func: Box<MetaExpr>,
        args: Vec<MetaExpr>,
    },
    GetField(Box<MetaExpr>, Rc<str>),
    GetVar(Rc<str>),
    Literal(LiteralValue),
    Default(CType),
    LooseCast(Box<MetaExpr>, CType),
    SizeOfType(CType),
    DerefPtr(Box<MetaExpr>),
    AddressOf(Box<MetaExpr>),
    Assign(Box<MetaExpr>, /* = */ Box<MetaExpr>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Equality,
    GreaterThan,
    LessThan,
    GreaterOrEqual,
    LessOrEqual,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum UnaryOp {
    Negate,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LiteralValue {
    IntNumber(u64),
    FloatNumber(f64),
    StringBytes(Rc<str>),
    UninitStruct,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum ValueType {
    U64,
    U8,
    U32,
    F64,
    F32,
    // should probably be an Rc<StructSignature>
    Struct(Rc<str>),
    Void,
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct CType {
    pub ty: ValueType,
    pub depth: u8, // 0 -> not a pointer. if you have ?256 levels of indirection that's a skill issue
}

impl<Func: FuncRepr> AnyModule<Func> {
    pub fn new(name: Rc<str>) -> Self {
        Self {
            functions: vec![],
            structs: vec![],
            name,
            forward_declarations: vec![],
            type_defs: Default::default(),
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
        assert!(
            self.depth > 0,
            "Tried to dereference non-pointer type {:?}.",
            self
        );
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

    /// Does this type fit in a register (ie. is not a struct)
    pub fn is_basic(&self) -> bool {
        self.depth > 0 || !matches!(self.ty, ValueType::Struct(_))
    }

    pub fn is_raw_void(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::Void)
    }

    pub fn is_void_ptr(&self) -> bool {
        self.depth > 0 && matches!(self.ty, ValueType::Void)
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

impl<T> FuncRepr for AnyFunction<T> {
    fn get_signature(&self) -> &FuncSignature {
        &self.signature
    }
}

pub type OpDebugInfo = i64;
pub struct MetaExpr {
    pub expr: RawExpr,
    line: i64,
}

impl RawExpr {
    pub fn debug(self, token: Token) -> MetaExpr {
        MetaExpr {
            expr: self,
            line: (token.line + 1) as i64,
        }
    }

    pub fn boxed(self, token: Token) -> Box<MetaExpr> {
        Box::new(MetaExpr {
            expr: self,
            line: (token.line + 1) as i64,
        })
    }
}

impl MetaExpr {
    pub fn info(&self) -> OpDebugInfo {
        self.line
    }
}

impl Deref for MetaExpr {
    type Target = RawExpr;

    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

impl AsRef<RawExpr> for MetaExpr {
    fn as_ref(&self) -> &RawExpr {
        self.deref()
    }
}

impl Debug for MetaExpr {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.expr.fmt(f)
    }
}
