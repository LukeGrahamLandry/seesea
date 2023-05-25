use inkwell::context::Context;
use inkwell::OptimizationLevel;
use logos::Logos;

use crate::asm::llvm::LlvmGen;
use crate::ast::{BinaryOp, Expr, FuncSignature, LiteralValue, Module, Stmt, ValueType};
use crate::ir::Op;
use crate::scanning::{Scanner, TokenType};
use crate::{ast, ir};

#[test]
fn count_scanned_tokens() {
    assert_eq!(TokenType::lexer("int x = 5;").count(), 5);
}

#[test]
fn just_ir() {
    eval_expect(ir_five_plus_ten(), 15);
}

#[test]
fn ast_to_ir() {
    let ast = ast_five_plus_ten();
    println!("{:?}", ast);
    let ir = ir::Module::from(Module {
        functions: vec![ast],
    });
    eval_expect(ir.functions[0].clone(), 15);
}

#[test]
fn src_to_ast_to_ir() {
    full_pipeline(
        "
long main(){
    long x = 5;
    long y = 10;
    long z = x + y;
    return z;
}
    ",
        15,
    );
}

#[test]
fn if_statement() {
    full_pipeline(
        "
long main(){
    long x = 5;
    long y = 10;
    long z = 15;
    if (x > y) {
        return x;
    } else {
        return y;
    }
}
    ",
        10,
    );
}

#[test]
fn if_statement_with_mutation() {
    full_pipeline(
        "
long main(){
    long x = 5;
    long y = 10;
    if (y < x) {
        x = 0;
    }
    return x;
}
    ",
        5,
    );
}

pub fn full_pipeline(src: &str, result: u64) {
    let scan = Scanner::new(src);
    println!("{:?}", scan);
    let ast = Module::from(scan);
    println!("{:?}", ast);
    let ir = ir::Module::from(ast);
    eval_expect(ir.functions[0].clone(), result);
}

pub fn eval_expect(ir: ir::Function, result: u64) {
    println!("{:?}", ir);
    let context = Context::create();
    let module = context.create_module("sum");
    let execution_engine = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .unwrap();
    let mut codegen = LlvmGen {
        context: &context,
        module,
        builder: context.create_builder(),
        execution_engine,
    };

    let answer = codegen.compile(ir);
    println!("=== LLVM IR ===");
    println!("{}", codegen.module.to_string());
    println!("========");
    assert_eq!(answer, result);
}

fn ir_five_plus_ten() -> ir::Function {
    let mut ir = ir::Function::new(FuncSignature {
        args: vec![],
        returns: ValueType::U64,
        name: "five_plus_ten".to_string(),
    });
    let block = ir.new_block();
    let a = ir.constant_int(block, 5);
    let b = ir.constant_int(block, 10);
    let dest = ir.next_var();
    ir.push(
        block,
        Op::Binary {
            dest,
            a,
            b,
            kind: BinaryOp::Add,
        },
    );
    ir.push(block, Op::Return { value: Some(dest) });
    ir
}

fn ast_five_plus_ten() -> ast::Function {
    let body = Stmt::Block {
        body: vec![
            Stmt::DeclareVar {
                name: "x".to_string(),
                value: Box::new(Expr::Literal {
                    value: LiteralValue::Number { value: 5.0 },
                }),
                kind: ValueType::U64,
            },
            Stmt::DeclareVar {
                name: "y".to_string(),
                value: Box::new(Expr::Literal {
                    value: LiteralValue::Number { value: 10.0 },
                }),
                kind: ValueType::U64,
            },
            Stmt::DeclareVar {
                name: "z".to_string(),
                value: Box::new(Expr::Binary {
                    left: Box::new(Expr::GetVar {
                        name: "x".to_string(),
                    }),
                    right: Box::new(Expr::GetVar {
                        name: "y".to_string(),
                    }),
                    op: BinaryOp::Add,
                }),
                kind: ValueType::U64,
            },
            Stmt::Return {
                value: Some(Box::new(Expr::GetVar {
                    name: "z".to_string(),
                })),
            },
        ],
    };
    ast::Function {
        body,
        signature: FuncSignature {
            args: vec![],
            returns: ValueType::U64,
            name: "five_plus_ten".to_string(),
        },
    }
}
