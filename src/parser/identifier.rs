use super::{
    parse_utils::{self, ParseError, ParseResult},
    literal::Literal,
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
            let (delta, _) = Literal::try_parse_text(&text[start..])?;
            end += delta;
            Ok((
                end,
                Self {
                    text: &text[start + 1..end],
                },
            ))
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
                Err(Box::new(ParseError::InvalidInput))
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
    #[case("This = Not a variable", "This")]
    #[case("This=Not a variable", "This")]
    #[case("   This = Not a variable", "This")]
    #[case(r##"#"This is some text" = Not a variable"##, "This is some text")]
    #[case(r##"   #"This is some text" = Not a variable"##, "This is some text")]
    // Keeping this malformed name for now, just want to make sure the parser doesn't panic on it.
    // The expectation is that the input is lexically valid
    #[case(r##"#"Malformed name""##, "Malformed name")]
    #[case("list, of, idents", "list")]
    // #[case("ThisIsTheEND", "ThisIsTheEND")]
    #[case("    nottext, 'more stuff', yadda yadda", "nottext")]
    fn test_parse_identifier(#[case] input: &str, #[case] expected: &str) {
        let (_, mut out) = Identifier::try_parse(input).unwrap();
        assert_eq!(expected, out.text())
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
