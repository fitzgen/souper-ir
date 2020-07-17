//! Parsing the Souper IR text format.

use std::path::Path;

/// An error that occurs during parsing.
#[derive(Debug)]
pub struct ParseError;

/// A `Result` type for parsing.
///
/// Either `Ok(T)` or `Err(ParseError)`.
pub type Result<T> = std::result::Result<T, ParseError>;

/// Parse an in-memory string.
pub fn parse_str(source: &str, filename: Option<&Path>) -> Result<()> {
    let _ = (source, filename);
    todo!()
}

/// Parse a file from disk.
pub fn parse_file(path: &Path) -> Result<()> {
    let _ = path;
    todo!()
}
