use crate::ast;
use crate::ast::FuncSignature;
use std::collections::HashMap;
use std::marker::PhantomData;

// TODO
/// Holds debug info relating opcodes back to AST nodes.
/// I'm doing a silly trick with using memory addresses as node identifiers,
/// so it relies on the original ast::Module being "pinned" to read any data out.
#[derive(Default)]
pub struct IrDebugInfo<'ast> {
    _sources: HashMap<&'ast FuncSignature, Vec<(AstRef, OpRef)>>,
    _phantom: PhantomData<&'ast ast::Module>, // dont need this if i keep the lifetimes in the hashmap keys
}

pub struct AstRef(usize);
pub struct OpRef(usize);
