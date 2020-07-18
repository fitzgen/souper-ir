//! Parsing the Souper IR text format.

use std::{
    borrow::Cow,
    iter::Peekable,
    ops::Range,
    path::{Path, PathBuf},
    str::CharIndices,
    str::FromStr,
};

/// An error that occurs during parsing.
#[derive(Debug)]
pub struct ParseError {
    inner: Box<ParseErrorInner>,
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
{file}:{line}:{column}: error: {msg}
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

            if current_offset > offset {
                return Some((line_num, line.len() - (current_offset - offset)));
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

/// Parse an in-memory string.
pub fn parse_str(source: &str, filename: Option<&Path>) -> Result<()> {
    let _ = (source, filename);
    todo!()
}

/// Parse a file from disk.
pub fn parse_file(path: &Path) -> Result<()> {
    let source = std::fs::read_to_string(path)?;
    parse_str(&source, Some(path))
}

#[derive(Debug)]
struct Lexer<'a> {
    source: &'a str,
    chars: Peekable<CharIndices<'a>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token<'a> {
    Ident(&'a str),
    ValName(&'a str),
    KnownBits(&'a str),
    Comma,
    Colon,
    Eq,
    Int(i128),
    OpenParen,
    CloseParen,
    OpenBracket,
}

fn is_ident_char(c: char) -> bool {
    ('0' <= c && c <= '9') || ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') || (c == '_')
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
            (start, c) if c == '-' || c.is_numeric() => {
                self.chars.next().unwrap();
                let mut end = start + 1;
                while self.chars.peek().map_or(false, |&(_, c)| c.is_numeric()) {
                    let (i, _) = self.chars.next().unwrap();
                    end = i + 1;
                }
                match i128::from_str(&self.source[start..end]) {
                    Ok(x) => Ok(Some((start, Token::Int(x)))),
                    Err(e) => Err(ParseError::new(
                        start,
                        format!("failed to parse int: {}", e),
                    )),
                }
            }
            (start, c) => Err(ParseError::new(start, format!("unexpected '{}'", c))),
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
path/to/foo.txt:3:5: error: missing apostrophe
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
            "1234 -4567" => [Int(1234), Int(-4567)];
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
