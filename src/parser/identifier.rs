use serde::Serialize;
use std::unreachable;
use unicode_categories::UnicodeCategories;

use crate::{parser::keywords::is_keyword, ERR_CONTEXT_SIZE};

use super::{
    literal::Literal,
    parse_utils::{self, gen_error_ctx, next_char, skip_whitespace, ParseError, ParseResult},
};

#[inline]
pub(crate) fn is_identifier_part(c: &char) -> bool {
    is_letter_character(c)
        || c.is_number_decimal_digit()     // Nd
        || c.is_punctuation_connector()    // Pc
        || c.is_other_format()             // Cf
        || c.is_mark_spacing_combining()   // Mc
        || c.is_mark_nonspacing()          // Mn
        || *c == '_'
        || *c == '.' // This is not part of the spec, but it is allowed as a separator between
                     // valid identifier parts
}

#[inline]
fn is_identifier_start(c: &char) -> bool {
    is_letter_character(c) || *c == '_'
}

// The definition of "Letter Character" given by the Microsoft Spec is more restrictive
// than given by the `is_letter` method in unicode_categories
#[inline]
fn is_letter_character(c: &char) -> bool {
    c.is_letter_modifier()                 // Lm
        || c.is_letter_uppercase()         // Lu
        || c.is_letter_lowercase()         // Ll
        || c.is_letter_titlecase()         // Lt
        || c.is_letter_other()             // Lo
        || c.is_number_letter() // Nl
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

    /// Parses a Generalized Identifier, as described in the specs
    /// generalized-identifier:
    ///     generalized-identifier-part
    ///     generalized-identifier separated only by blanks [(U+0020)] generalized-identifier-part
    /// generalized-identifier-part:
    ///     generalized-identifier-segment
    ///     decimal-digit-character generalized-identifier-segment
    /// generalized-identifier-segment:
    ///     keyword-or-identifier
    ///     keyword-or-identifier dot-character keyword-or-identifier
    pub(crate) fn try_parse_generalized(text: &'a str) -> ParseResult<Self> {
        if let Ok(res) = Identifier::try_parse_quoted(text) {
            return Ok(res);
        }

        let mut parse_pointer = skip_whitespace(text);
        let start = parse_pointer;

        // Between each space seperated texts
        loop {
            if next_char(&text[parse_pointer..])
                .unwrap_or(' ')
                .is_number_decimal_digit()
            {
                parse_pointer += 1;
            }

            let delta = match Identifier::try_parse(&text[parse_pointer..]) {
                Ok((i, _)) => i,
                Err(e) => {
                    let end = text[parse_pointer..]
                        .chars()
                        .take_while(is_identifier_part)
                        .count();
                    if is_keyword(&text[parse_pointer..parse_pointer + end]) {
                        end
                    } else {
                        return Err(e);
                    }
                }
            };
            parse_pointer += delta;
            // lookahead space check
            let lookahead = skip_whitespace(&text[parse_pointer..]);
            if let Some(c) = next_char(&text[parse_pointer + lookahead..]) {
                if !(is_identifier_part(&c) || c.is_number_decimal_digit()) {
                    break;
                }
            } else {
                // Reached the end of the text, which could be valid for an identifier
                break;
            };
            parse_pointer += lookahead;
        }

        Ok((
            parse_pointer,
            Self {
                text: &text[start..parse_pointer],
            },
        ))
    }

    /// Not Public because always used in conjuction with
    /// Regular identifiers or Generalized Identifiers
    fn try_parse_quoted(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        if text[parse_pointer..].starts_with(r#"#""#) {
            parse_pointer += 1;
        } else {
            // This is not a quoted identifier
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        let mut end = parse_pointer;
        let (delta, name) = Literal::try_parse_text(&text[parse_pointer..])?;
        end += delta;
        match name {
            Literal::Text(txt) => Ok((end, Self { text: txt })),
            _ => unreachable!(
                "Only Literal::Text should be a valid return value from try_parse_text"
            ),
        }
    }

    /// This generates what is termed in the specs, a "Quoted Identifier" or an "Available Identeifier"
    /// Keywords are rejected via this code.
    pub(crate) fn try_parse(text: &'a str) -> ParseResult<Self> {
        if let Ok(res) = Identifier::try_parse_quoted(text) {
            return Ok(res);
        }
        let parse_pointer = skip_whitespace(text);

        let mut end = parse_pointer;

        // Get the identifier range
        end += {
            text[parse_pointer..]
                .char_indices()
                .take_while(|(i, c)| {
                    if *i == 0 {
                        is_identifier_start(c)
                    } else {
                        is_identifier_part(c)
                    }
                })
                .count()
        };

        if end == parse_pointer || is_keyword(&text[parse_pointer..end]){
            // Identifiers must have _SOME_ text
            // Identifers cannot be keywords
            Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }))
        }  else {
            Ok((
                end,
                Self {
                    text: &text[parse_pointer..end],
                },
            ))
        }
    }

    #[cfg(test)]
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
    #[case(r#"99text"#)]
    #[case(r#""this is text""#)]
    fn text_identifier_parser_errors(#[case] input: &str) {
        let out = Identifier::try_parse(input);
        println!("{:?}", &out);
        match out {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[rstest]
    #[case(r##"   #"Malformed name""##, 20, "Malformed name")]
    #[case(r##"#"Malformed name""##, 17, "Malformed name")]
    #[case(r##" #"Malformed name"     "##, 18, "Malformed name")]
    #[case("  9text", 7, "9text")]
    #[case("9text more text 7text", 21, "9text more text 7text")]
    #[case("   not text, 'more stuff', yadda yadda", 11, "not text")]
    fn text_generalized_identifier(
        #[case] input: &str,
        #[case] exp_delta: usize,
        #[case] expected: &str,
    ) {
        let (delta, out) = Identifier::try_parse_generalized(input).expect("Unable to parse input");
        assert_eq!(expected, out.text());
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case("  {text}")]
    // NOTE: This is an interesting case. The Spec doesn't make it supre clear, but it appears
    // according to the strict interpretation that with generalized idents, There is only allowed
    // ONE decimal digit character
    #[case("99text")]
    #[case(r#""this is text""#)]
    fn text_generalized_identifier_parser_errors(#[case] input: &str) {
        let out = Identifier::try_parse_generalized(input);
        match out {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }
}
