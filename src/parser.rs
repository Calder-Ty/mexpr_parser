use self::{
    expressions::LetExpression,
    parse_utils::{skip_whitespace, ParseResult},
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
    let mut parse_pointer = skip_whitespace(text);
    while parse_pointer < text.len() {
        let (delta, val) = LetExpression::try_parse(&text[parse_pointer..])?;
        res.push(val);
        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);
    }
    Ok((parse_pointer, res))
}

pub(crate) mod parse_utils {
    use thiserror::Error;

    use super::identifier::is_identifier_part;
    pub type ParseResult<T> = Result<(usize, T), Box<ParseError>>;

    #[derive(Debug, Error)]
    pub enum ParseError {
        #[error("Input is Invalid, Unable to proceed at character {pointer} \n{ctx}")]
        InvalidInput { pointer: usize, ctx: String },
    }

    pub(crate) fn gen_error_ctx(text: &str, pointer: usize, size: usize) -> String {
        let start: usize = if pointer < size {
            0
        } else {
            pointer - size
        };

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
    pub(crate) fn skip_whitespace(text: &str) -> usize {
        text.chars().take_while(|c| (*c).is_whitespace()).count()
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
    pub fn next_char(text:&str) -> Option<char> {
        text.chars().next()
    }

    #[cfg(test)]
    mod tests {
        use super::gen_error_ctx;
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
    }
}
