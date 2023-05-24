//! TOKENS -> AST

use crate::ast::Program;
use crate::scanning::Scanner;

impl<'src> From<Scanner<'src>> for Program {
    fn from(scanner: Scanner) -> Self {
        let parser = Parser {
            scanner,
            program: Program { functions: vec![] },
        };
        parser.program
    }
}

struct Parser<'src> {
    scanner: Scanner<'src>,
    program: Program,
}

impl<'src> Parser<'src> {}
