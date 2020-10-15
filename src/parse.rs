//! Parsing the Souper IR text format.
//!
//! This module provides both high- and low-level parsing utilities:
//!
//! * The high-level parsing functions are `parse_*_file` and `parse_*_string`
//!   which can be used to parse full replacements, LHSes, or RHSes either from
//!   files on disk or from an in-memory string.
//!
//! * The low-level parsing utilities are [the `Parse`
//!   trait][crate::parse::Parse] and [the `Parser`
//!   struct][crate::parse::Parser]. These can be used to parse a single
//!    instance of an LHS or RHS, for example.
//!
//! ## Example
//!
//! ```
//! # fn main() -> souper_ir::parse::Result<()> {
//! use souper_ir::parse::parse_replacements_str;
//! use std::path::Path;
//!
//! let replacements = parse_replacements_str("
//!     ;; First replacement.
//!     %x:i32 = var
//!     %2lx = slt 2, %x
//!     pc %2lx 1
//!     %1lx = slt 1, %x
//!     cand %1lx 1
//!
//!     ;; Second replacement.
//!     %bb = block 3
//!     %phi1 = phi %bb, 1:i32, 2, 3
//!     %phi2 = phi %bb, 2:i32, 4, 6
//!     %phi1x2 = mul %phi1, 2
//!     cand %phi2 %phi1x2
//! ", Some(Path::new("example.souper")))?;
//!
//! assert_eq!(replacements.len(), 2);
//! # Ok(())
//! # }
//! ```

use crate::ast;
use id_arena::Arena;
use std::{
    borrow::Cow,
    collections::HashMap,
    convert::TryInto,
    iter::Peekable,
    mem,
    path::{Path, PathBuf},
    str::CharIndices,
    str::FromStr,
};

/*

Here is the grammar, as far as I can tell. See
https://github.com/google/souper/issues/782.

```
<replacement> ::= <lhs> <rhs>
                | <full>

<lhs> ::= <statement>* <infer>

<infer> ::= 'infer' <valname> <root-attribute>*

<rhs> ::= <statement>* <result>

<result> ::= 'result' <operand>

<full> ::= <lhs> <rhs>
         | <statement>* <cand>

<cand> ::= 'cand' <valname> <operand> <root-attribute>*

<statement> ::= <assignment>
              | <pc>
              | <blockpc>

<assignment> ::= <assignment-lhs> '=' <assignment-rhs>

<assignment-lhs> ::= <valname> (':' <type>)?

<assignment-rhs> ::= 'var' <attribute>*
                   | 'block' <int>
                   | 'phi' <valname> (',' <operand>)*
                   | 'reservedinst' <attribute>*
                   | 'reservedconst' <attribute>*
                   | <instruction> <attribute>*

<instruction> ::= 'add' <operand> ',' <operand>
                | 'addnsw' <operand> ',' <operand>
                | 'addnuw' <operand> ',' <operand>
                | 'addnw' <operand> ',' <operand>
                | 'sub' <operand> ',' <operand>
                | 'subnsw' <operand> ',' <operand>
                | 'subnuw' <operand> ',' <operand>
                | 'subnw' <operand> ',' <operand>
                | 'mul' <operand> ',' <operand>
                | 'mulnsw' <operand> ',' <operand>
                | 'mulnuw' <operand> ',' <operand>
                | 'mulnw' <operand> ',' <operand>
                | 'udiv' <operand> ',' <operand>
                | 'sdiv' <operand> ',' <operand>
                | 'udivexact' <operand> ',' <operand>
                | 'sdivexact' <operand> ',' <operand>
                | 'urem' <operand> ',' <operand>
                | 'srem' <operand> ',' <operand>
                | 'and' <operand> ',' <operand>
                | 'or' <operand> ',' <operand>
                | 'xor' <operand> ',' <operand>
                | 'shl' <operand> ',' <operand>
                | 'shlnsw' <operand> ',' <operand>
                | 'shlnuw' <operand> ',' <operand>
                | 'shlnw' <operand> ',' <operand>
                | 'lshr' <operand> ',' <operand>
                | 'lshrexact' <operand> ',' <operand>
                | 'ashr' <operand> ',' <operand>
                | 'ashrexact' <operand> ',' <operand>
                | 'select' <operand> ',' <operand> ',' <operand>
                | 'zext' <operand>
                | 'sext' <operand>
                | 'trunc' <operand>
                | 'eq' <operand> ',' <operand>
                | 'ne' <operand> ',' <operand>
                | 'ult' <operand> ',' <operand>
                | 'slt' <operand> ',' <operand>
                | 'ule' <operand> ',' <operand>
                | 'sle' <operand> ',' <operand>
                | 'ctpop' <operand>
                | 'bswap' <operand>
                | 'bitreverse' <operand>
                | 'cttz' <operand>
                | 'ctlz' <operand>
                | 'fshl' <operand> ',' <operand> ',' <operand>
                | 'fshr' <operand> ',' <operand> ',' <operand>
                | 'sadd.with.overflow' <operand> ',' <operand>
                | 'uadd.with.overflow' <operand> ',' <operand>
                | 'ssub.with.overflow' <operand> ',' <operand>
                | 'usub.with.overflow' <operand> ',' <operand>
                | 'smul.with.overflow' <operand> ',' <operand>
                | 'umul.with.overflow' <operand> ',' <operand>
                | 'sadd.sat' <operand> ',' <operand>
                | 'uadd.sat' <operand> ',' <operand>
                | 'ssub.sat' <operand> ',' <operand>
                | 'usub.sat' <operand> ',' <operand>
                | 'extractvalue' <operand> ',' <operand>
                | 'hole'
                | 'freeze' <operand>

<operand> ::= <valname>
            | <constant>

<root-attribute> ::= '(' <root-attribute-inner> ')'

<root-attribute-inner> ::= 'demandedBits' '=' regexp([0|1]+)
                         | 'harvestedFromUse'

<attribute> ::= '(' <attribute-inner> ')'

<attribute-inner> ::= 'knownBits' '=' regexp([0|1|x]+)
                    | 'powerOfTwo'
                    | 'negative'
                    | 'nonNegative'
                    | 'nonZero'
                    | 'hasExternalUses'
                    | 'signBits' '=' <int>
                    | 'range' '=' '[' <int> ',' <int> ')'

<pc> ::= 'pc' <operand> <operand>

<blockpc> ::= 'blockpc' <valname> <int> <operand> <operand>

<constant> ::= <int> (':' <type>)?

<int> ::= regexp(-?\d+)

<type> ::= regexp(i\d+)

<valname> ::= regexp(%[a-zA-Z0-9_]+)

<ident> ::= regexp([a-zA-Z][a-zA-Z0-9_]+)
```

*/

/// An error that occurs during parsing.
pub struct ParseError {
    inner: Box<ParseErrorInner>,
}

impl std::fmt::Debug for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Debug)]
struct ParseErrorInner {
    kind: ParseErrorKind,
    pos: Option<(usize, usize, String)>,
    filepath: Option<PathBuf>,
}

#[derive(Debug)]
enum ParseErrorKind {
    Io(std::io::Error),
    Parse(usize, String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.inner.kind {
            ParseErrorKind::Io(io) => write!(f, "IO error: {}", io),
            ParseErrorKind::Parse(offset, msg) => {
                let (line, column, line_text) = if let Some((l, c, t)) = &self.inner.pos {
                    (*l, *c, Cow::Borrowed(t))
                } else {
                    (0, 0, Cow::Owned(format!("byte offset {}", offset)))
                };
                write!(
                    f,
                    "\
{file}:{line}:{column}: {msg}
     |
{line:4} | {line_text}
     | {marker:>column$}",
                    file = self
                        .inner
                        .filepath
                        .as_ref()
                        .map_or(Path::new("unknown"), |p| &*p)
                        .display(),
                    line = line + 1,
                    column = column + 1,
                    line_text = line_text,
                    msg = msg,
                    marker = "^"
                )
            }
        }
    }
}

impl std::error::Error for ParseError {}

impl From<std::io::Error> for ParseError {
    fn from(e: std::io::Error) -> Self {
        ParseError {
            inner: Box::new(ParseErrorInner {
                kind: ParseErrorKind::Io(e),
                pos: None,
                filepath: None,
            }),
        }
    }
}

impl ParseError {
    pub(crate) fn new(offset: usize, msg: impl Into<String>) -> Self {
        ParseError {
            inner: Box::new(ParseErrorInner {
                kind: ParseErrorKind::Parse(offset, msg.into()),
                pos: None,
                filepath: None,
            }),
        }
    }

    fn offset(&self) -> Option<usize> {
        if let ParseErrorKind::Parse(offset, _) = self.inner.kind {
            Some(offset)
        } else {
            None
        }
    }

    fn line_col_in(source: &str, offset: usize) -> Option<(usize, usize)> {
        let mut current_offset = 0;
        for (line_num, line) in source.split_terminator('\n').enumerate() {
            // +1 for the `\n`.
            current_offset += line.len() + 1;

            if current_offset >= offset {
                return Some((line_num, line.len().saturating_sub(current_offset - offset)));
            }
        }

        None
    }

    pub(crate) fn set_source(&mut self, source: &str) {
        if let Some(offset) = self.offset() {
            if let Some((line, col)) = Self::line_col_in(source, offset) {
                let line_text = source.lines().nth(line).unwrap_or("").to_string();
                self.inner.pos = Some((line, col, line_text));
            }
        }
    }

    pub(crate) fn set_filepath(&mut self, filepath: impl Into<PathBuf>) {
        self.inner.filepath = Some(filepath.into());
    }
}

/// A `Result` type for parsing.
///
/// Either `Ok(T)` or `Err(ParseError)`.
pub type Result<T> = std::result::Result<T, ParseError>;

/// Keep parsing `P`s until we reach EOF.
fn parse_until_eof<P>(parser: &mut Parser) -> Result<Vec<P>>
where
    P: Parse,
{
    let mut ps = vec![];
    while !parser.eof()? {
        ps.push(P::parse(parser)?);
    }
    Ok(ps)
}

/// Execute the given function and if it returns a parse error, set the source
/// and filename on the error.
fn with_source_and_file<T>(
    source: &str,
    file: Option<&Path>,
    f: impl FnOnce() -> Result<T>,
) -> Result<T> {
    f().map_err(|mut e| {
        e.set_source(source);
        if let Some(f) = file {
            e.set_filepath(f);
        }
        e
    })
}

/// Parse a sequence of [`Replacement`s][crate::ast::Replacement] from an
/// in-memory string.
pub fn parse_replacements_str(
    source: &str,
    filename: Option<&Path>,
) -> Result<Vec<ast::Replacement>> {
    with_source_and_file(source, filename, || {
        let mut parser = Parser::new(source);
        parse_until_eof(&mut parser)
    })
}

/// Parse a sequence of [`Replacement`s][crate::ast::Replacement] from a file on
/// disk.
pub fn parse_replacements_file(path: &Path) -> Result<Vec<ast::Replacement>> {
    let source = std::fs::read_to_string(path)?;
    parse_replacements_str(&source, Some(path))
}

/// Parse a sequence of [`LeftHandSide`s][crate::ast::LeftHandSide] from an
/// in-memory string.
pub fn parse_left_hand_sides_str(
    source: &str,
    filename: Option<&Path>,
) -> Result<Vec<ast::LeftHandSide>> {
    with_source_and_file(source, filename, || {
        let mut parser = Parser::new(source);
        parse_until_eof(&mut parser)
    })
}

/// Parse a sequence of [`LeftHandSide`s][crate::ast::LeftHandSide] from a file on
/// disk.
pub fn parse_left_hand_sides_file(path: &Path) -> Result<Vec<ast::LeftHandSide>> {
    let source = std::fs::read_to_string(path)?;
    parse_left_hand_sides_str(&source, Some(path))
}

/// Parse a sequence of [`RightHandSide`s][crate::ast::RightHandSide] from an
/// in-memory string.
pub fn parse_right_hand_sides_str(
    source: &str,
    filename: Option<&Path>,
) -> Result<Vec<ast::RightHandSide>> {
    with_source_and_file(source, filename, || {
        let mut parser = Parser::new(source);
        parse_until_eof(&mut parser)
    })
}

/// Parse a sequence of [`RightHandSide`s][crate::ast::RightHandSide] from a file on
/// disk.
pub fn parse_right_hand_sides_file(path: &Path) -> Result<Vec<ast::RightHandSide>> {
    let source = std::fs::read_to_string(path)?;
    parse_right_hand_sides_str(&source, Some(path))
}

#[derive(Debug)]
struct Lexer<'a> {
    source: &'a str,
    chars: Peekable<CharIndices<'a>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Token<'a> {
    Ident(&'a str),
    ValName(&'a str),
    KnownBits(&'a str),
    Int(&'a str),
    Comma,
    Colon,
    Eq,
    OpenParen,
    CloseParen,
    OpenBracket,
}

fn is_ident_char(c: char) -> bool {
    match c {
        '0'..='9' | 'a'..='z' | 'A'..='Z' | '_' | '.' => true,
        _ => false,
    }
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Self {
        Lexer {
            source,
            chars: source.char_indices().peekable(),
        }
    }

    fn expect_char(&mut self, c: char) -> Result<()> {
        match self.chars.next() {
            Some((_, c2)) if c2 == c => Ok(()),
            Some((offset, c2)) => Err(ParseError::new(
                offset,
                format!("expected '{}', found '{}'", c, c2),
            )),
            None => Err(ParseError::new(
                self.source.len().saturating_sub(1),
                "unexpected EOF",
            )),
        }
    }

    /// Get the next token.
    ///
    /// Returns `None` at EOF.
    fn next_token(&mut self) -> Result<Option<(usize, Token<'a>)>> {
        loop {
            match self.chars.peek() {
                // EOF.
                None => return Ok(None),

                // Eat whitespace.
                Some((_, c)) if c.is_whitespace() => {
                    while self.chars.peek().map_or(false, |(_, c)| c.is_whitespace()) {
                        self.chars.next().unwrap();
                    }
                }

                // Eat comments.
                Some((_, ';')) => {
                    while self.chars.peek().map_or(false, |(_, c)| *c != '\n') {
                        self.chars.next().unwrap();
                    }
                }

                _ => break,
            }
        }

        match *self.chars.peek().unwrap() {
            (start, ',') => {
                self.chars.next().unwrap();
                Ok(Some((start, Token::Comma)))
            }
            (start, '=') => {
                self.chars.next().unwrap();
                Ok(Some((start, Token::Eq)))
            }
            (start, ':') => {
                self.chars.next().unwrap();
                Ok(Some((start, Token::Colon)))
            }
            (start, '(') => {
                self.chars.next().unwrap();
                Ok(Some((start, Token::OpenParen)))
            }
            (start, ')') => {
                self.chars.next().unwrap();
                Ok(Some((start, Token::CloseParen)))
            }
            (start, '[') => {
                self.chars.next().unwrap();
                Ok(Some((start, Token::OpenBracket)))
            }
            (start, '%') => {
                self.chars.next().unwrap();
                let mut end = start + 1;
                while self.chars.peek().map_or(false, |&(_, c)| is_ident_char(c)) {
                    let (i, _) = self.chars.next().unwrap();
                    end = i + 1;
                }
                if start + 1 == end {
                    Err(ParseError::new(start, "expected value name"))
                } else {
                    Ok(Some((start, Token::ValName(&self.source[start..end]))))
                }
            }
            (start, c) if ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') => {
                self.chars.next().unwrap();
                let mut end = start + 1;
                while self.chars.peek().map_or(false, |&(_, c)| is_ident_char(c)) {
                    let (i, _) = self.chars.next().unwrap();
                    end = i + 1;
                }

                let ident = &self.source[start..end];
                if ident != "knownBits" {
                    return Ok(Some((start, Token::Ident(ident))));
                }

                self.expect_char('=')?;
                let bit_pattern_start = start + "knownBits=".len();
                let mut bit_pattern_end = bit_pattern_start;
                while self
                    .chars
                    .peek()
                    .map_or(false, |&(_, c)| c == '0' || c == '1' || c == 'x')
                {
                    let (i, _) = self.chars.next().unwrap();
                    bit_pattern_end = i + 1;
                }
                if bit_pattern_start == bit_pattern_end {
                    Err(ParseError::new(
                        bit_pattern_start,
                        "expected [0|1|x]+ bit pattern for knownBits",
                    ))
                } else {
                    Ok(Some((
                        start,
                        Token::KnownBits(&self.source[bit_pattern_start..bit_pattern_end]),
                    )))
                }
            }
            (start, c) if c == '-' || ('0' <= c && c <= '9') => {
                self.chars.next().unwrap();
                let mut end = start + 1;
                while self
                    .chars
                    .peek()
                    .map_or(false, |&(_, c)| '0' <= c && c <= '9')
                {
                    let (i, _) = self.chars.next().unwrap();
                    end = i + 1;
                }
                Ok(Some((start, Token::Int(&self.source[start..end]))))
            }
            (start, c) => Err(ParseError::new(start, format!("unexpected '{}'", c))),
        }
    }
}

/// A Souper text parser buffer.
///
/// Manages lexing and lookahead, as well as some parsed values and binding
/// scopes.
#[derive(Debug)]
pub struct Parser<'a> {
    lexer: Lexer<'a>,

    /// Lookahead token that we've peeked at, if any.
    lookahead: Option<Token<'a>>,

    /// Our current offset into the string we are parsing.
    offset: usize,

    /// Statements being built up during parsing.
    statements: Arena<ast::Statement>,

    /// Scope mapping value names to their value id.
    values: HashMap<String, ast::ValueId>,

    /// Scope mapping block names to their block id.
    blocks: HashMap<String, ast::BlockId>,
}

impl<'a> Parser<'a> {
    /// Construct a new parser for the given Souper source text.
    pub fn new(source: &'a str) -> Self {
        Parser {
            lexer: Lexer::new(source),
            lookahead: None,
            offset: 0,
            statements: Arena::new(),
            values: HashMap::new(),
            blocks: HashMap::new(),
        }
    }

    pub(crate) fn lookahead(&mut self) -> Result<Option<Token<'a>>> {
        if self.lookahead.is_none() {
            if let Some((offset, token)) = self.lexer.next_token()? {
                self.offset = offset;
                self.lookahead = Some(token);
            }
        }
        Ok(self.lookahead)
    }

    pub(crate) fn lookahead_ident(&mut self, ident: &str) -> Result<bool> {
        Ok(self.lookahead()? == Some(Token::Ident(ident)))
    }

    /// Are we at EOF?
    pub(crate) fn eof(&mut self) -> Result<bool> {
        Ok(self.lookahead()?.is_none())
    }

    pub(crate) fn error<T>(&self, msg: impl Into<String>) -> Result<T> {
        Err(ParseError::new(self.offset, msg))
    }

    pub(crate) fn token(&mut self) -> Result<Token<'a>> {
        if let Some(tok) = self.lookahead.take() {
            Ok(tok)
        } else {
            match self.lexer.next_token()? {
                Some((offset, tok)) => {
                    self.offset = offset;
                    Ok(tok)
                }
                None => {
                    self.offset = self.lexer.source.len().saturating_sub(1);
                    self.error("unexpected EOF")
                }
            }
        }
    }

    pub(crate) fn val_name(&mut self) -> Result<&'a str> {
        match self.token()? {
            Token::ValName(s) => Ok(s),
            _ => self.error("expected a value name"),
        }
    }

    pub(crate) fn ident(&mut self, which: &str) -> Result<()> {
        match self.token()? {
            Token::Ident(s) if s == which => Ok(()),
            _ => self.error(format!("expected '{}'", which)),
        }
    }

    pub(crate) fn int(&mut self) -> Result<i128> {
        match self.token()? {
            Token::Int(x) => match i128::from_str(x) {
                Ok(x) => Ok(x),
                Err(e) => self.error(e.to_string()),
            },
            _ => self.error("expected an integer literal"),
        }
    }

    pub(crate) fn eq(&mut self) -> Result<()> {
        match self.token()? {
            Token::Eq => Ok(()),
            _ => self.error("expected '='"),
        }
    }

    pub(crate) fn colon(&mut self) -> Result<()> {
        match self.token()? {
            Token::Colon => Ok(()),
            _ => self.error("expected ':'"),
        }
    }

    pub(crate) fn comma(&mut self) -> Result<()> {
        match self.token()? {
            Token::Comma => Ok(()),
            _ => self.error("expected ','"),
        }
    }

    pub(crate) fn open_paren(&mut self) -> Result<()> {
        match self.token()? {
            Token::OpenParen => Ok(()),
            _ => self.error("expected '('"),
        }
    }

    pub(crate) fn close_paren(&mut self) -> Result<()> {
        match self.token()? {
            Token::CloseParen => Ok(()),
            _ => self.error("expected ')'"),
        }
    }

    pub(crate) fn open_bracket(&mut self) -> Result<()> {
        match self.token()? {
            Token::OpenBracket => Ok(()),
            _ => self.error("expected '['"),
        }
    }

    fn take_statements(&mut self) -> Arena<ast::Statement> {
        self.values.clear();
        self.blocks.clear();
        mem::replace(&mut self.statements, Arena::new())
    }
}

/// A trait for AST nodes that can be parsed from text.
pub trait Parse: Sized {
    /// Parse a `Self` from the given buffer.
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self>;
}

/// A trait for whether an AST node looks like it comes next.
pub trait Peek {
    /// Does it look like we can parse a `Self` from the given buffer?
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool>;
}

impl<P> Parse for Option<P>
where
    P: Peek + Parse,
{
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        if P::peek(parser)? {
            Ok(Some(P::parse(parser)?))
        } else {
            Ok(None)
        }
    }
}

impl<P> Parse for Vec<P>
where
    P: Peek + Parse,
{
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        let mut ps = vec![];
        while P::peek(parser)? {
            ps.push(P::parse(parser)?);
        }
        Ok(ps)
    }
}

impl Parse for ast::Replacement {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        while ast::Statement::peek(parser)? {
            parse_statement(parser)?;
        }

        if ast::Infer::peek(parser)? {
            let lhs = ast::Infer::parse(parser)?;
            while ast::Statement::peek(parser)? {
                parse_statement(parser)?;
            }
            parser.ident("result")?;
            let rhs = ast::Operand::parse(parser)?;
            let statements = parser.take_statements();
            return Ok(ast::Replacement::LhsRhs {
                statements,
                lhs,
                rhs,
            });
        }

        let cand = ast::Cand::parse(parser)?;
        let statements = parser.take_statements();
        Ok(ast::Replacement::Cand { statements, cand })
    }
}

impl Parse for ast::LeftHandSide {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        while ast::Statement::peek(parser)? {
            parse_statement(parser)?;
        }
        let infer = ast::Infer::parse(parser)?;
        let statements = parser.take_statements();
        Ok(ast::LeftHandSide { statements, infer })
    }
}

impl Parse for ast::RightHandSide {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        while ast::Statement::peek(parser)? {
            parse_statement(parser)?;
        }
        parser.ident("result")?;
        let result = ast::Operand::parse(parser)?;
        let statements = parser.take_statements();
        Ok(ast::RightHandSide { statements, result })
    }
}

impl Peek for ast::Statement {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        Ok(ast::Assignment::peek(parser)? || ast::Pc::peek(parser)? || ast::BlockPc::peek(parser)?)
    }
}

fn parse_statement(parser: &mut Parser) -> Result<()> {
    if ast::Assignment::peek(parser)? {
        let assignment = ast::Assignment::parse(parser)?;
        let name = assignment.name.clone();
        let is_block = matches!(assignment.value, ast::AssignmentRhs::Block(_));
        let id = parser
            .statements
            .alloc(ast::Statement::Assignment(assignment));
        parser.values.insert(name.clone(), ast::ValueId(id));
        if is_block {
            parser.blocks.insert(name, ast::BlockId(ast::ValueId(id)));
        }
        return Ok(());
    }

    if ast::Pc::peek(parser)? {
        let pc = ast::Pc::parse(parser)?;
        parser.statements.alloc(ast::Statement::Pc(pc));
        return Ok(());
    }

    if ast::BlockPc::peek(parser)? {
        let blockpc = ast::BlockPc::parse(parser)?;
        parser.statements.alloc(ast::Statement::BlockPc(blockpc));
        return Ok(());
    }

    parser.error("expected either an assignment, a pc statement, of a blockpc statement")
}

impl Peek for ast::Infer {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        parser.lookahead_ident("infer")
    }
}

impl Parse for ast::Infer {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.ident("infer")?;
        let name = parser.val_name()?;
        let value = parser.values.get(name).copied().ok_or_else(|| {
            ParseError::new(parser.offset, format!("no value named '{}' in scope", name))
        })?;
        let attributes = Vec::<ast::RootAttribute>::parse(parser)?;
        Ok(ast::Infer { value, attributes })
    }
}

impl Parse for ast::Cand {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.ident("cand")?;
        let lhs = ast::Operand::parse(parser)?;
        let rhs = ast::Operand::parse(parser)?;
        let attributes = Vec::<ast::RootAttribute>::parse(parser)?;
        Ok(ast::Cand {
            lhs,
            rhs,
            attributes,
        })
    }
}

impl Peek for ast::RootAttribute {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        Ok(parser.lookahead()? == Some(Token::OpenParen))
    }
}

impl Parse for ast::RootAttribute {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.open_paren()?;
        match parser.token()? {
            Token::Ident("harvestedFromUse") => {
                parser.close_paren()?;
                Ok(ast::RootAttribute::HarvestedFromUse)
            }
            Token::Ident("demandedBits") => {
                parser.eq()?;
                match parser.token()? {
                    Token::Int(i) => {
                        let mut bits = Vec::with_capacity(i.len());
                        for ch in i.chars() {
                            match ch {
                                '0' => bits.push(false),
                                '1' => bits.push(true),
                                _ => return parser.error("expected [0|1]+ bit pattern"),
                            }
                        }
                        parser.close_paren()?;
                        Ok(ast::RootAttribute::DemandedBits(bits))
                    }
                    _ => parser.error("expected [0|1]+ bit pattern"),
                }
            }
            _ => parser.error("expected 'demandedBits' or 'harvestedFromUse'"),
        }
    }
}

impl Peek for ast::Assignment {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        Ok(matches!(parser.lookahead()?, Some(Token::ValName(_))))
    }
}

impl Parse for ast::Assignment {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        let name = parser.val_name()?.to_string();
        if parser.values.contains_key(&name) {
            return parser.error(format!("cannot redefine '{}'", name));
        }

        let r#type = if parser.lookahead()? == Some(Token::Colon) {
            parser.colon()?;
            Some(ast::Type::parse(parser)?)
        } else {
            None
        };
        parser.eq()?;
        let value = ast::AssignmentRhs::parse(parser)?;
        let attributes = Vec::<ast::Attribute>::parse(parser)?;
        Ok(ast::Assignment {
            name,
            r#type,
            value,
            attributes,
        })
    }
}

impl Parse for ast::AssignmentRhs {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        if parser.lookahead_ident("var")? {
            parser.ident("var")?;
            return Ok(ast::AssignmentRhs::Var);
        }

        if ast::Block::peek(parser)? {
            let block = ast::Block::parse(parser)?;
            return Ok(ast::AssignmentRhs::Block(block));
        }

        if ast::Phi::peek(parser)? {
            let phi = ast::Phi::parse(parser)?;
            return Ok(ast::AssignmentRhs::Phi(phi));
        }

        if parser.lookahead_ident("reservedinst")? {
            parser.ident("reservedinst")?;
            return Ok(ast::AssignmentRhs::ReservedInst);
        }

        if parser.lookahead_ident("reservedconst")? {
            parser.ident("reservedconst")?;
            return Ok(ast::AssignmentRhs::ReservedConst);
        }

        if ast::Instruction::peek(parser)? {
            let inst = ast::Instruction::parse(parser)?;
            return Ok(ast::AssignmentRhs::Instruction(inst));
        }

        parser.error("expected a constant, var, block, phi, or instruction")
    }
}

impl Peek for ast::Pc {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        parser.lookahead_ident("pc")
    }
}

impl Parse for ast::Pc {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.ident("pc")?;
        let x = ast::Operand::parse(parser)?;
        let y = ast::Operand::parse(parser)?;
        Ok(ast::Pc { x, y })
    }
}

impl Peek for ast::BlockPc {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        parser.lookahead_ident("blockpc")
    }
}

impl Parse for ast::BlockPc {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.ident("blockpc")?;
        let name = parser.val_name()?;
        let block =
            parser.blocks.get(name).copied().ok_or_else(|| {
                ParseError::new(parser.offset, format!("unknown block '{}'", name))
            })?;
        let predecessor = <i128 as TryInto<u32>>::try_into(parser.int()?)
            .map_err(|e| ParseError::new(parser.offset, e.to_string()))?;
        let x = ast::Operand::parse(parser)?;
        let y = ast::Operand::parse(parser)?;
        Ok(ast::BlockPc {
            block,
            predecessor,
            x,
            y,
        })
    }
}

impl Parse for ast::Type {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        match parser.token()? {
            Token::Ident(ident) if ident.starts_with('i') => match u16::from_str(&ident[1..]) {
                Ok(width) if width > 0 => return Ok(ast::Type { width }),
                _ => {}
            },
            _ => {}
        }

        parser.error("expected a type (like 'i32', 'i8', or 'i1')")
    }
}

impl Peek for ast::Constant {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        Ok(matches!(parser.lookahead()?, Some(Token::Int(_))))
    }
}

impl Parse for ast::Constant {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        let value = parser.int()?;
        let r#type = if parser.lookahead()? == Some(Token::Colon) {
            parser.colon()?;
            Some(ast::Type::parse(parser)?)
        } else {
            None
        };
        Ok(ast::Constant { value, r#type })
    }
}

impl Peek for ast::Block {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        parser.lookahead_ident("block")
    }
}

impl Parse for ast::Block {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.ident("block")?;
        let predecessors: u32 = <i128 as TryInto<u32>>::try_into(parser.int()?)
            .map_err(|e| ParseError::new(parser.offset, e.to_string()))?;
        Ok(ast::Block { predecessors })
    }
}

impl Peek for ast::Phi {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        parser.lookahead_ident("phi")
    }
}

impl Parse for ast::Phi {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.ident("phi")?;
        let name = parser.val_name()?;
        let block =
            parser.blocks.get(name).copied().ok_or_else(|| {
                ParseError::new(parser.offset, format!("unknown block '{}'", name))
            })?;
        let predecessors = match parser.statements[(block.0).0] {
            ast::Statement::Assignment(ast::Assignment {
                value: ast::AssignmentRhs::Block(ast::Block { predecessors }),
                ..
            }) => predecessors,
            _ => unreachable!(),
        };
        let mut values = vec![];
        for _ in 0..predecessors {
            parser.comma()?;
            values.push(ast::Operand::parse(parser)?);
        }
        Ok(ast::Phi { block, values })
    }
}

impl Peek for ast::Attribute {
    fn peek<'a>(parser: &mut Parser<'a>) -> Result<bool> {
        Ok(parser.lookahead()? == Some(Token::OpenParen))
    }
}

impl Parse for ast::Attribute {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        parser.open_paren()?;
        match parser.token()? {
            Token::KnownBits(kb) => {
                let mut bits = Vec::with_capacity(kb.len());
                for b in kb.chars() {
                    match b {
                        '0' => bits.push(Some(false)),
                        '1' => bits.push(Some(true)),
                        'x' => bits.push(None),
                        _ => unreachable!(),
                    }
                }
                parser.close_paren()?;
                Ok(ast::Attribute::KnownBits(bits))
            }
            Token::Ident("powerOfTwo") => {
                parser.close_paren()?;
                Ok(ast::Attribute::PowerOfTwo)
            }
            Token::Ident("negative") => {
                parser.close_paren()?;
                Ok(ast::Attribute::Negative)
            }
            Token::Ident("nonNegative") => {
                parser.close_paren()?;
                Ok(ast::Attribute::NonNegative)
            }
            Token::Ident("nonZero") => {
                parser.close_paren()?;
                Ok(ast::Attribute::NonZero)
            }
            Token::Ident("hasExternalUses") => {
                parser.close_paren()?;
                Ok(ast::Attribute::HasExternalUses)
            }
            Token::Ident("signBits") => {
                parser.eq()?;
                let bits = <i128 as TryInto<u8>>::try_into(parser.int()?)
                    .map_err(|e| ParseError::new(parser.offset, e.to_string()))?;
                parser.close_paren()?;
                Ok(ast::Attribute::SignBits(bits))
            }
            Token::Ident("range") => {
                parser.eq()?;
                parser.open_bracket()?;
                let min = parser.int()?;
                parser.comma()?;
                let max = parser.int()?;
                parser.close_paren()?;
                parser.close_paren()?;
                Ok(ast::Attribute::Range(min, max))
            }
            Token::Ident(id) => parser.error(format!("unknown attribute '{}'", id)),
            _ => parser.error("expected an attribute identifier"),
        }
    }
}

impl Parse for ast::Operand {
    fn parse<'a>(parser: &mut Parser<'a>) -> Result<Self> {
        if matches!(parser.lookahead()?, Some(Token::ValName(_))) {
            let name = parser.val_name()?;
            let value = parser.values.get(name).copied().ok_or_else(|| {
                ParseError::new(parser.offset, format!("unknown value '{}'", name))
            })?;
            Ok(ast::Operand::Value(value))
        } else {
            let constant = ast::Constant::parse(parser)?;
            Ok(ast::Operand::Constant(constant))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_error_display() {
        let source = "\
hello, how are you?
> I am good, thanks
thats good
";
        let mut err = ParseError::new(45, "missing apostrophe");
        err.set_source(source);
        err.set_filepath("path/to/foo.txt");

        let expected = "\
path/to/foo.txt:3:5: missing apostrophe
     |
   3 | thats good
     |     ^";
        let actual = err.to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn test_lexer_tokens() {
        use super::Token::*;

        macro_rules! tokenizes {
            ( $( $source:expr => [ $($tok:expr),* $(,)* ]; )* ) => {
                $({
                    eprintln!("=== Lexing {:?} ===", $source);
                    let mut lexer = Lexer::new($source);
                    $(
                        let expected = $tok;
                        eprintln!("Expect: {:?}", expected);
                        let actual = lexer.next_token()
                            .expect("should not have an error during lexing")
                            .expect("should not hit EOF")
                            .1;
                        eprintln!("Actual: {:?}", actual);
                        assert_eq!(expected, actual);
                    )*
                    assert!(lexer.next_token().unwrap().is_none());
                })*
            }
        }

        tokenizes! {
            "foo foo1 foo_foo FOO" => [
                Ident("foo"),
                Ident("foo1"),
                Ident("foo_foo"),
                Ident("FOO"),
            ];
            "%0 %foo %FOO %foo1" => [
                ValName("%0"),
                ValName("%foo"),
                ValName("%FOO"),
                ValName("%foo1"),
            ];
            "knownBits=0 knownBits=1 knownBits=x knownBits=01x01x01x" => [
                KnownBits("0"),
                KnownBits("1"),
                KnownBits("x"),
                KnownBits("01x01x01x"),
            ];
            ", : = ( ) [" => [Comma, Colon, Eq, OpenParen, CloseParen, OpenBracket];
            "1234 -4567" => [Int("1234"), Int("-4567")];
            "%0:i8" => [ValName("%0"), Colon, Ident("i8")];
            "hello ; blah blah blah\n goodbye" => [Ident("hello"), Ident("goodbye")];
        }
    }

    #[test]
    fn test_lexer_offsets() {
        macro_rules! offsets {
            ( $source:expr => [ $($offset:expr),* $(,)* ]; ) => {
                let mut lexer = Lexer::new($source);
                $(
                    let expected = $offset;
                    eprintln!("Expect: {:?}", expected);
                    let actual = lexer.next_token()
                        .expect("should not have an error during lexing")
                        .expect("should not hit EOF")
                        .0;
                    eprintln!("Actual: {:?}", actual);
                    assert_eq!(expected, actual);
                )*
                assert!(lexer.next_token().unwrap().is_none());
            }
        }

        #[rustfmt::skip]
        offsets! {
            //         1         2         3         4
            //12345678901234567890123456789012345678901234567890
            "foo %123 knownBits=01x ,   :   =   (   )   [   42" => [
             0,  4,   9,            23, 27, 31, 35, 39, 43, 47
            ];
        }
    }
}
