# seesea

A C compiler targeting LLVM IR.  

This is not an optimising compiler, but it's certainly a compiling compiler, 
and that ought to be enough for anybody. Besides, LLVM can fix anything pathological on its own.

## Stages

1. Source code
2. Token stream 
3. AST 
4. IR
5. LLVM IR

It would probably more reasonable to skip the internal IR and go directly to LLVM's IR (they're purposely very similar), 
but I think it would be fun to implement full ASM backends eventually. 

## Libraries

- The lexer (converting source code to a stream of tokens) is generated by [Logos](https://crates.io/crates/logos. 
- [Inkwell](https://crates.io/crates/inkwell) bindings to LLVM for emitting the final IR. 
