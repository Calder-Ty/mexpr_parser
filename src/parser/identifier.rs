use std::unreachable;

use super::{
    literal::Literal,
    parse_utils::{self, ParseError, ParseResult},
};

#[inline]
fn is_identifier_part(c: &char) -> bool {
    // For now just '.', rather than finding a group for Mn, Mc or Pc
    // to represent continuation characters
    c.is_alphabetic() || c.is_ascii_digit() || *c == '_' || *c == '.'
}

#[derive(Debug)]
pub(crate) struct Identifier<'a> {
    text: &'a str,
}

impl<'a> Identifier<'a> {
    #[cfg(test)]
    pub(crate) fn new(text: &'a str) -> Self {
        Self { text }
    }

    pub(crate) fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut start = parse_utils::skip_whitespace(&text);

        let ident_text = &text[start..];
        // Check if it is a Quoted Identifier
        let is_quoted = if ident_text.starts_with(r#"#""#) {
            // Can unwrap because we know we have initialized the value already ^^^
            start += 1;
            true
        } else {
            false
        };

        let mut end = start;

        if is_quoted {
            let (delta, name) = Literal::try_parse_text(&text[start..])?;
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
                text[start..]
                    .char_indices()
                    .take_while(|(_, c)| is_identifier_part(c))
                    .count()
            };

            if end == start {
                // Identifiers must have _SOME_ text
                Err(Box::new(ParseError::InvalidInput{ pointer: start, ctx: parse_utils::gen_error_ctx(text, start, 5) }))
            } else {
                Ok((
                    end,
                    Self {
                        text: &text[start..end],
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
