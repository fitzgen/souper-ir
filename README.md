# `souper-ir`

A library for manipulating [Souper] IR.

[![](https://docs.rs/souper-ir/badge.svg)](https://docs.rs/souper-ir/)
[![](https://img.shields.io/crates/v/souper-ir.svg)](https://crates.io/crates/souper-ir)
[![](https://img.shields.io/crates/d/souper-ir.svg)](https://crates.io/crates/souper-ir)
![CI](https://github.com/fitzgen/souper-ir/workflows/CI/badge.svg)

This crate provides AST types for parsing or generating Souper IR. It is a
suitable building block either for writing a custom LHS extractor, or for
translating learned optimizations into your own peephole optimizations pass.

### AST

The AST type definitions and builders live in the `souper_ir::ast` module.

### Parsing Souper IR

When the `parse` Cargo feature is enabled, the `souper_ir::parse` module
contains functions for parsing Souper IR from a file or an in-memory string.

```rust
use std::path::Path;

// We provide a filename to get better error messages.
let filename = Path::new("example.souper");

let replacements = souper_ir::parse::parse_replacements_str("
    ;; x + x --> 2 * x
    %0 = var
    %1 = add %0, %0
    %2 = mul %0, 2
    cand %1, %2

    ;; x & x --> x
    %0 = var
    %1 = and %0, %0
    cand %1, %0
", Some(filename))?;
```

### Emitting Souper IR's Text Format

When the `stringify` Cargo feature is enabled, then the
`souper_ir::ast::Replacement`, `souper_ir::ast::LeftHandSide`, and
`souper_ir::ast::RightHandSide` types all implement `std::fmt::Display`. The
`Display` implementation writes the AST type out as Souper's text format.

```rust
use souper_ir::ast;

// Build this Souper left-hand side:
//
//     %x:i32 = var
//     %y = mul %x, 2
//     infer %y
//
// We expect that Souper would be able to synthesize a right-hand side that
// does a left shift by one instead of a multiplication.

let mut lhs = ast::LeftHandSideBuilder::default();

let x = lhs.assignment(
    Some("x".into()),
    Some(ast::Type { width: 32 }),
    ast::AssignmentRhs::Var,
    vec![],
);

let y = lhs.assignment(
    Some("y".into()),
    None,
    ast::Instruction::Mul {
        a: x.into(),
        b: ast::Constant { value: 2, r#type: None }.into(),
    },
    vec![],
);

let lhs = lhs.finish(y, vec![]);

// Now we can stringify the LHS (and then, presumably, give it to Souper)
// with `std::fmt::Display`:

use std::io::Write;

let mut file = std::fs::File::create("my-lhs.souper")?;
write!(&mut file, "{}", lhs)?;
```
[Souper]: https://github.com/google/souper
