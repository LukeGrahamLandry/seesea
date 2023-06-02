//! The resolution pass handles many things...
//!     - deciding types for each expression (including implicit casts).
//!     - deciding which scope variables belong to and whether they need a stable stack address.
//!     - replacing implicit default values of variable declarations with literals.

use crate::ast::{BinaryOp, CType, FuncSignature, LiteralValue, OpDebugInfo, UnaryOp};
use crate::ir::CastType;
use std::cell::Cell;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

pub mod parse;

pub struct ResolvedExpr {
    expr: Operation,
    pub(crate) ty: CType,
    line: OpDebugInfo,
}

#[derive(Debug)]
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
    // These all need to refer to the same object so if it hits an AddressOf, it can update the needs_stack_alloc field.
    GetVar(Rc<Variable>),
    Literal(LiteralValue),
    Cast(Box<ResolvedExpr>, CType, CastType),
    DerefPtr(Box<ResolvedExpr>),
    AddressOf(Box<ResolvedExpr>),
    Assign(Box<ResolvedExpr>, /* = */ Box<ResolvedExpr>),
}

#[derive(Debug)]
pub enum FuncSource {
    Internal,
    Pointer(Box<ResolvedExpr>),
}

#[derive(Debug, Eq, PartialEq)]
pub struct Variable {
    pub(crate) name: Rc<str>,
    pub(crate) scope: LexScope,
    pub ty: CType,
    pub needs_stack_alloc: Cell<bool>,
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
        self.scope.hash(state);
        self.needs_stack_alloc.get().hash(state);
        self.ty.hash(state);
        self.name.hash(state);
    }
}
