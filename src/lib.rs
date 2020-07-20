//! A library for manipulating [Souper] IR.
//!
//! [![](https://docs.rs/souper-ir/badge.svg)](https://docs.rs/souper-ir/)
//! [![](https://img.shields.io/crates/v/souper-ir.svg)](https://crates.io/crates/souper-ir)
//! [![](https://img.shields.io/crates/d/souper-ir.svg)](https://crates.io/crates/souper-ir)
//! ![CI](https://github.com/fitzgen/souper-ir/workflows/CI/badge.svg)
//!
//! This crate provides AST types for parsing or generating Souper IR. It is a
//! suitable building block either for writing a custom LHS extractor, or for
//! translating learned optimizations into your own peephole optimizations pass.
//!
//! ## AST
//!
//! The AST type definitions live in the `souper_ir::ast` module.
//!
//! ## Parsing Souper IR
//!
//! When the `parse` Cargo feature is enabled, the `souper_ir::parse` module
//! contains functions for parsing Souper IR from a file or an in-memory string.
//!
//! ## Emitting Souper IR's Text Format
//!
//! When the `stringify` Cargo feature is enabled, the `souper_ir::stringify`
//! module contains functions for taking an in-memory Souper IR AST and
//! translating it into Souper IR's text format.
//!
//! [Souper]: https://github.com/google/souper

#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

pub mod ast;

#[cfg(feature = "parse")]
pub mod parse;
#[cfg(feature = "stringify")]
pub mod stringify;
