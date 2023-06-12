use super::parse_utils::ParseResult;

/// Core utilities for parser

pub trait TryParse<'a> {
    /// Try to parse the struct from the text
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized;
}
