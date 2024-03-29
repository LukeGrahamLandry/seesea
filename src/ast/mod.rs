use crate::ir::CastType;
use crate::scanning::Token;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::ffi::CStr;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::mem::size_of;
use std::ops::Deref;
use std::rc::Rc;

mod parse;
pub mod print;
pub mod resolve;

// TODO: I want to purge all the Rcs. I think they never actually alias.
//       Next step is a SrcStr type that's either a span from the code or an owned string.

pub struct AnyModule<Func: FuncRepr> {
    pub functions: Vec<Func>,
    pub structs: Vec<StructSignature>,
    pub name: Rc<str>,
    pub forward_declarations: Vec<FuncSignature>,
    pub type_defs: HashMap<Rc<str>, CType>,
    pub tagged_names: HashMap<Rc<str>, NameTagType>,
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
    pub index: usize,
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
    While {
        condition: Expr,
        body: Box<AnyStmt<Expr>>,
    },
    DoWhile {
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
        value: Expr,
        // TODO clean this up. but means raw and resolved would need different stmt types which is a bit annoying.
        // only while raw
        name: Rc<str>,
        kind: CType,
        // only once resolved
        variable: Option<VariableRef>,
    },
    Return {
        value: Option<Expr>,
    },
    Break,
    Continue,
    Nothing,
}

// TODO: If I really cared, it would probably be much faster to use an arena allocator for these boxes.
//       I think that would also allow using raw references by unsafely guaranteeing everything has the same lifetime.
//       Feels silly to obsess about allocations at this stage but would be fun.
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
    ArrayIndex {
        ptr: Box<MetaExpr>,
        index: Box<MetaExpr>,
    },
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
    StringBytes(Rc<CStr>),
    UninitStruct,
    UninitArray(CType, usize),
}

#[derive(Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub enum ValueType {
    Bool,
    U64,
    U8,
    U32,
    U16,
    F64,
    F32,
    // TODO: some thought required on how to support nested declarations but don't bring back the name:Rc<str>, that sucked!
    Struct(usize), // Index into Module.structs
    Void,
}

#[derive(Debug, Copy, Clone, PartialEq, Hash, Eq)]
pub enum NameTagType {
    Struct,
    Union,
    Enum,
}

#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct CType {
    pub ty: ValueType,
    pub depth: u8, // 0 -> not a pointer. if you have ?256 levels of indirection that's a skill issue

    // TODO: remove. I hate this since i throw it away anyway as soon as possible. feels like inviting invalid values.
    pub count: usize, // array size. this is awkward because struct fields have sized arrays but they decay to pointers when passed.
}

impl<Func: FuncRepr> AnyModule<Func> {
    pub fn new(name: Rc<str>) -> Self {
        Self {
            functions: vec![],
            structs: vec![],
            name,
            forward_declarations: vec![],
            type_defs: Default::default(),
            tagged_names: Default::default(),
        }
    }

    pub fn get_internal_func(&self, name: &str) -> Option<&Func> {
        self.functions
            .iter()
            .find(|&func| func.get_signature().name.as_ref() == name)
    }

    // TODO: filter out forward_declarations before putting in ir?
    pub fn iter_external_funcs(&self) -> impl Iterator<Item = &FuncSignature> {
        self.forward_declarations
            .iter() // TODO: O(n^2)
            .filter(|s| self.get_internal_func(&s.name).is_none())
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

    pub fn get_struct_by_name(&self, name: impl AsRef<str>) -> Option<&StructSignature> {
        self.structs
            .iter()
            .find(|&func| func.name.as_ref() == name.as_ref())
    }

    pub fn get_struct(&self, ty: impl Borrow<CType>) -> &StructSignature {
        match ty.borrow().ty {
            ValueType::Struct(id) => &self.structs[id],
            _ => panic!("Struct not found."),
        }
    }

    pub fn get_field_offset(&self, s: &StructSignature, index: usize) -> usize {
        assert!(index < s.fields.len());
        let mut offset = 0;
        for i in 0..index {
            offset += self.size_of(s.fields[i].1);
        }
        let field_ty = s.fields[index].1;
        let field_size = self.size_of(field_ty);
        assert_eq!(offset % field_size, 0); // check that my packing made a valid alignment
        offset
    }

    // TODO: assert(sizeof(size_t) == sizeof(uint64_t) == sizeof(unsigned long)))
    pub fn size_of(&self, ty: impl Borrow<CType>) -> usize {
        let ty = ty.borrow();
        if ty.depth > 0 {
            // this is checking at compile time when it should care about runtime but it will have to do for now.
            assert_eq!(size_of::<usize>(), size_of::<u64>());
            return 8 * (ty.count);
        }

        let size = match ty.ty {
            ValueType::U64 => 8,
            ValueType::U8 => 1,
            ValueType::U32 => 4,
            ValueType::F64 => 8,
            ValueType::F32 => 4,
            ValueType::Void => 0,
            ValueType::U16 => 2,
            ValueType::Struct(id) => {
                let def = &self.structs[id];
                let mut size = 0;
                for (_, field) in &def.fields {
                    size += self.size_of(field);
                }
                size
            }
            // TODO: custom backends are just treating these as u64 which is probably wrong but might not be observable until i let you say _Bool as a type.
            ValueType::Bool => 8,
        };
        size * (ty.count)
    }
}

impl CType {
    pub fn bool() -> CType {
        CType {
            ty: ValueType::Bool,
            depth: 0,
            count: 1,
        }
    }

    pub fn int() -> CType {
        CType {
            ty: ValueType::U64,
            depth: 0,
            count: 1,
        }
    }

    pub fn direct(ty: ValueType) -> CType {
        CType {
            ty,
            depth: 0,
            count: 1,
        }
    }

    #[must_use]
    pub fn deref_type(&self) -> CType {
        assert_eq!(self.count, 1, "no deref array. should auto decay");
        let mut other = self.clone();
        assert!(
            self.depth > 0,
            "Tried to dereference non-pointer type {:?}.",
            self
        );
        other.depth -= 1;

        other
    }

    #[must_use]
    pub fn ref_type(&self) -> CType {
        assert_eq!(self.count, 1, "no ref array. should auto decay");
        let mut other = self.clone();
        other.depth += 1;
        other.count = 1;
        other
    }

    pub fn is_pointer_to(&self, value_type: impl Borrow<CType>) -> bool {
        &self.deref_type() == value_type.borrow()
    }

    pub fn is_struct(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::Struct(_))
    }

    pub fn is_static_array(&self) -> bool {
        self.count != 1
    }

    /// Does this type fit in a register (ie. is not a struct)
    pub fn fits_in_register(&self) -> bool {
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

    pub fn is_raw_char(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::U8)
    }

    pub fn is_raw_bool(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::Bool)
    }

    pub fn is_raw_float(&self) -> bool {
        self.depth == 0 && matches!(self.ty, ValueType::F32 | ValueType::F64)
    }

    pub fn is_ptr(&self) -> bool {
        self.depth > 0
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
    pub(crate) line: OpDebugInfo,
}

#[derive(Clone)]
pub struct ResolvedExpr {
    pub(crate) expr: Operation,
    pub(crate) ty: CType,
    line: OpDebugInfo,
}

#[derive(Clone)]
pub enum Operation {
    Binary {
        left: Box<ResolvedExpr>,
        right: Box<ResolvedExpr>,
        op: BinaryOp,
    },
    Unary(UnaryOp, Box<ResolvedExpr>),
    Call {
        signature: FuncSignature,
        func: FuncSource,
        args: Vec<ResolvedExpr>,
    },
    // name is already resolved to a field index
    GetField(Box<ResolvedExpr>, usize),
    GetVar(Rc<Variable>),
    Literal(LiteralValue),
    Cast(Box<ResolvedExpr>, CType, CastType),
    DerefPtr(Box<ResolvedExpr>),
    AddressOf(Box<ResolvedExpr>),
    Assign(Box<ResolvedExpr>, /* = */ Box<ResolvedExpr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum FuncSource {
    Internal,
    External,
    // Pointer(Box<ResolvedExpr>),
}

// TODO: these should have an index number so ir stage doesn't need a hashmap
#[derive(Eq, PartialEq)]
pub struct Variable {
    pub(crate) name: Rc<str>,
    pub(crate) scope: LexScope,
    pub ty: CType,
}

pub type VariableRef = Rc<Variable>;

/// Uniquely identifies a lexical scope. These DO NOT correspond to depth of nesting (they are never reused).
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct LexScope(pub usize);

/// Uniquely identifies a variable declaration in the source code by noting which block it came from.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct Var<'ast>(pub &'ast str, pub LexScope);

impl ResolvedExpr {
    pub fn info(&self) -> OpDebugInfo {
        self.line
    }
}

impl Deref for ResolvedExpr {
    type Target = Operation;

    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

impl AsRef<Operation> for ResolvedExpr {
    fn as_ref(&self) -> &Operation {
        self.deref()
    }
}

impl Debug for ResolvedExpr {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.expr.fmt(f)
    }
}

impl Hash for Variable {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Not including the Cell because that can mutate (even tho it really shouldn't after resolving stage).
        // TODO: that makes the derived Eq impl wrong!
        self.scope.hash(state);
        self.ty.hash(state);
        self.name.hash(state);
    }
}

impl Operation {
    pub fn number(n: u64) -> Operation {
        Operation::Literal(LiteralValue::IntNumber(n))
    }
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

impl MetaExpr {
    pub fn comptime_usize(&self) -> Option<usize> {
        if let RawExpr::Literal(LiteralValue::IntNumber(n)) = self.expr {
            Some(n as usize)
        } else {
            None
        }
    }
}
