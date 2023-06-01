//! The resolution pass handles
//!     - deciding types for each expression (including implicit casts).
//!     - deciding which scope variables belong to and whether they need a stable stack address.

use crate::ast::{BinaryOp, CType, FuncSignature, LiteralValue, OpDebugInfo, UnaryOp};
use crate::ir::CastType;
use crate::resolve::parse::LexScope;
use std::cell::Cell;
use std::rc::Rc;

pub mod allocs;
mod parse;

pub struct ResolvedExpr {
    expr: Operation,
    ty: CType,
    line: OpDebugInfo,
}

pub struct Variable {
    name: Rc<str>,
    scope: LexScope,
    ty: CType,
    needs_stack_alloc: Cell<bool>,
}

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

pub enum FuncSource {
    Internal,
    Pointer(Box<ResolvedExpr>),
}
