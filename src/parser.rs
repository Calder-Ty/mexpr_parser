use self::{
    expressions::LetExpression,
    parse_utils::{skip_whitespace_and_comments, ParseResult},
};

mod core;
pub mod expressions;
mod identifier;
mod keywords;
mod literal;
mod operators;

pub fn try_parse(text: &str) -> ParseResult<Vec<LetExpression<'_>>> {
    let mut res = vec![];
    // Parsing the text
    let mut parse_pointer = skip_whitespace_and_comments(text);
    while parse_pointer < text.len() {
        let (delta, val) = LetExpression::try_parse(&text[parse_pointer..])?;
        res.push(val);
        parse_pointer += delta;
        parse_pointer += skip_whitespace_and_comments(&text[parse_pointer..]);
    }
    Ok((parse_pointer, res))
}

pub(crate) mod parse_utils {
    use std::{eprintln, panic};

    use thiserror::Error;

    use super::identifier::is_identifier_part;
    pub type ParseResult<T> = Result<(usize, T), Box<ParseError>>;

    #[derive(Debug, Error)]
    pub enum ParseError {
        #[error("Input is Invalid, Unable to proceed at character {pointer} \n{ctx}")]
        InvalidInput { pointer: usize, ctx: String },
    }

    pub(crate) fn gen_error_ctx(text: &str, pointer: usize, size: usize) -> String {
        let start: usize = if pointer < size { 0 } else { pointer - size };

        let end: usize = if pointer + size > text.len() {
            text.len()
        } else {
            pointer + size
        };

        let ctx = &text[start..end];
        let padding = "-".repeat(pointer - start + 1); // +1 accounts for the quotes added in
        format!("{ctx:?}\n{padding}^")
    }

    #[inline]
    /// Skips Whitespace and comments, going to next parseable character
    pub(crate) fn skip_whitespace_and_comments(text: &str) -> usize {
        let mut parse_pointer = 0;
        while next_char(&text[parse_pointer..])
            .unwrap_or('_')
            .is_whitespace()
            || text[parse_pointer..].starts_with("//")
            || text[parse_pointer..].starts_with("/*")
        {
            // First skip whitespace
            parse_pointer += text[parse_pointer..].chars().take_while(|c| (*c).is_whitespace()).count();
            // Now skip comments
            if text[parse_pointer..].starts_with("//") {
                parse_pointer += text[parse_pointer..]
                    .chars()
                    .take_while(|c| (*c) != '\n')
                    .count();
            } else if text[parse_pointer..].starts_with("/*") {
                parse_pointer += text[parse_pointer..]
                    .char_indices()
                    .skip(1)
                    .take_while(|(i, c)| {
                        eprintln!("{}, {}", i, c);
                        !text[parse_pointer + i - c.len_utf8()..].starts_with("*/")
                    }
                    ).count() + 2; // for the one we skipped and to account for the one at the end
            }
        }
        parse_pointer
    }

    #[inline]
    pub fn followed_by_valid_seperator(text: &str, len: usize) -> bool {
        let next = text.chars().nth(len).unwrap_or('_');
        // Valid Separator
        next.is_whitespace() || next == ','
    }

    #[inline]
    pub fn end_of_identifier(text: &str, len: usize) -> bool {
        let next = text.chars().nth(len).unwrap_or('_');
        // Valid Separator
        !is_identifier_part(&next)
    }

    #[inline]
    pub fn followed_by_whitespace(text: &str, len: usize) -> bool {
        let next = text.chars().nth(len).unwrap_or('_');
        // Valid Separator
        next.is_whitespace()
    }

    #[inline]
    pub fn next_char(text: &str) -> Option<char> {
        text.chars().next()
    }

    #[cfg(test)]
    mod tests {
        use super::{gen_error_ctx, skip_whitespace_and_comments};
        use rstest::rstest;

        #[rstest]
        #[case(
            "this is some text that has errored",
            10,
            5,
            r#""is some te"
------^"#
        )]
        #[case(
            "this is some text that has errored",
            0,
            5,
            r#""this "
-^"#
        )]
        #[case(
            "this is some text that has errored",
            32,
            5,
            r#""errored"
------^"#
        )]
        fn test_get_error_ctx(
            #[case] input: &str,
            #[case] pointer: usize,
            #[case] size: usize,
            #[case] exp_res: &str,
        ) {
            let res = gen_error_ctx(input, pointer, size);
            assert_eq!(exp_res, res)
        }

        #[rstest]
        #[case("      this is some text that has errored", 6)]
        #[case("//      this is some text that has errored", 42)]
        #[case("/*      this is some text that*/ has errored", 33)]
        #[case(
            "
this is some text that has errored",
            1
        )]
        fn test_skip_whitespace_and_comments(#[case] input: &str, #[case] expected_delta: usize) {
            let res = skip_whitespace_and_comments(input);
            assert_eq!(expected_delta, res)
        }
    }
}
