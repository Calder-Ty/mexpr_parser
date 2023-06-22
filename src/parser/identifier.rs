use serde::Serialize;
use std::unreachable;

use crate::{parser::keywords::is_keyword, ERR_CONTEXT_SIZE};

use super::{
    literal::Literal,
    parse_utils::{self, ParseError, ParseResult, skip_whitespace},
};

#[inline]
fn is_identifier_part(c: &char) -> bool {
    // For now just '.', rather than finding a group for Mn, Mc or Pc
    // to represent continuation characters
    c.is_alphabetic() || c.is_ascii_digit() || *c == '_' || *c == '.'
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub(crate) struct Identifier<'a> {
    text: &'a str,
}

impl<'a> Identifier<'a> {
    #[cfg(test)]
    pub(crate) fn new(text: &'a str) -> Self {
        Self { text }
    }

    /// Panics if `text` is not a keyword.
    pub fn from_keyword(text: &'a str) -> Self {
        assert!(is_keyword(text));
        Self { text }
    }

    pub(crate) fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(&text);

        let ident_text = &text[parse_pointer..];
        // Check if it is a Quoted Identifier
        let is_quoted = if ident_text.starts_with(r#"#""#) {
            // Can unwrap because we know we have initialized the value already ^^^
            parse_pointer += 1;
            true
        } else {
            false
        };

        let mut end = parse_pointer;

        if is_quoted {
            let (delta, name) = Literal::try_parse_text(&text[parse_pointer..])?;
            end += delta;
            match name {
                Literal::Text(txt) => Ok((end, Self { text: txt })),
                _ => unreachable!(
                    "Only Literal::Text should be a valid return value from try_parse_text"
                ),
            }
        } else {
            // Get the identifier range
            end += {
                text[parse_pointer..]
                    .char_indices()
                    .take_while(|(_, c)| is_identifier_part(c))
                    .count()
            };

            if end == parse_pointer {
                // Identifiers must have _SOME_ text
                Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }))
            } else if is_keyword(&text[parse_pointer..end]) {
                // Identifers cannot be keywords
                Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }))
            } else {
                Ok((
                    end,
                    Self {
                        text: &text[parse_pointer..end],
                    },
                ))
            }
        }
    }

    pub fn text(&self) -> &str {
        // Eventually fix this with Valid States
        &self.text
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case("This = Not a variable", "This", 4)]
    #[case("This=Not a variable", "This", 4)]
    #[case("   This = Not a variable", "This", 7)]
    #[case(r##"#"This is some text" = Not a variable"##, "This is some text", 20)]
    #[case(
        r##"   #"This is some text" = Not a variable"##,
        "This is some text",
        23
    )]
    // Keeping this malformed name for now, just want to make sure the parser doesn't panic on it.
    // The expectation is that the input is lexically valid
    #[case(r##"#"Malformed name""##, "Malformed name", 17)]
    #[case("list, of, idents", "list", 4)]
    #[case("ThisIsTheEND", "ThisIsTheEND", 12)]
    #[case("    nottext, 'more stuff', yadda yadda", "nottext", 11)]
    fn test_parse_identifier(
        #[case] input: &str,
        #[case] expected: &str,
        #[case] exp_delta: usize,
    ) {
        let (delta, out) = Identifier::try_parse(input).unwrap();
        assert_eq!(expected, out.text());
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case(r#""this is text""#)]
    fn text_identifier_parser_errors(#[case] input: &str) {
        let out = Identifier::try_parse(input);
        println!("{:?}", &out);
        match out {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }
}
