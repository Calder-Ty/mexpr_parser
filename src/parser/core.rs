use super::parse_utils::ParseResult;

/// Core utilities for parser

pub trait TryParse<'a, T> {
    /// Try to parse the struct from the text
    fn try_parse(text: &'a str) -> ParseResult<T>
    where
        Self: Sized;
}
