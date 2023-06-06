mod identifier;
mod literal;
pub mod expressions;


pub(crate) mod parse_utils {
    use thiserror::Error;
    pub type ParseResult<T> = Result<(usize, T), Box<ParseError>>;

    #[derive(Debug, Error)]
    pub enum ParseError {
        #[error("Input is Invalid, Unable to proceed at character {pointer} \n{ctx}")]
        InvalidInput { pointer: usize, ctx: String },
    }

    pub(crate) fn gen_error_ctx(text: &str, pointer: usize, size: usize) -> String {
        let start: usize;
        let end: usize;
        if pointer < size {
            start = 0;
        } else {
            start = pointer - size
        }

        if pointer + size > text.len() {
            end = text.len();
        } else {
            end = pointer + size;
        }

        let ctx = &text[start..end];
        let padding = "-".repeat(pointer - start + 1); // +1 accounts for the quotes added in
        format!("{ctx:?}\n{padding}^")
    }

    #[inline]
    pub(crate) fn skip_whitespace(text: &str) -> usize {
        text.chars()
            .take_while(|c| (*c).is_whitespace())
            .count()
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

