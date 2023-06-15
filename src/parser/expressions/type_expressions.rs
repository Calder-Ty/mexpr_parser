use serde::Serialize;

use crate::{
    parser::parse_utils::{gen_error_ctx, skip_whitespace, ParseResult},
    ParseError,
};

use super::primary_expressions::PrimaryExpression;

pub(crate) const PRIMITIVE_TYPES: [&str; 18] = [
    "any",
    "anynonnull",
    "binary",
    "date",
    "datetime",
    "datetimezone",
    "duration",
    "function",
    "list",
    "logical",
    "none",
    "null",
    "number",
    "record",
    "table",
    "text",
    "time",
    "type",
];

#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum Type<'a> {
    TypeStatement(TypeExpression<'a>),
    Primary(PrimaryExpression<'a>),
}

impl<'a> Type<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        if let Ok((i, val)) = TypeExpression::try_parse(text) {
            return Ok((i, Type::TypeStatement(val)));
        }

        let (i, val) = PrimaryExpression::try_parse(text)?;
        Ok((i, Type::Primary(val)))
    }
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct TypeExpression<'a> {
    text: &'a str,
}

impl<'a> TypeExpression<'a> {

    #[cfg(test)]
    pub(crate) fn new(text: &'a str) -> Self { Self { text } }

    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        let start = parse_pointer;
        let followed_by_space = &text[parse_pointer..]
            .chars()
            .skip(4)
            .next()
            .unwrap_or('_')
            .is_whitespace();

        if !(text[parse_pointer..].starts_with("type") && *followed_by_space) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        }

        parse_pointer += 4; // length of the word "type"
        parse_pointer += skip_whitespace(&text[parse_pointer..]); // length of the word "type"

        // for now only supporting the 'primitive type' expression
        let delta_type = &text[parse_pointer..]
            .chars()
            .take_while(|c| (*c).is_ascii_alphabetic())
            .count();
        if PRIMITIVE_TYPES.contains(&&text[parse_pointer..parse_pointer + delta_type]) {
            parse_pointer += delta_type;
            return Ok((
                parse_pointer,
                Self {
                    text: &text[start..parse_pointer],
                },
            ));
        }
        return Err(Box::new(ParseError::InvalidInput {
            pointer: parse_pointer,
            ctx: gen_error_ctx(text, parse_pointer, 5),
        }));
    }
}

#[cfg(test)]
mod tests {

    use std::assert_eq;

    use super::*;
    use rstest::rstest;


    #[rstest]
    #[case("    type null", "type null", 13)]
    #[case("    type datetime  ", "type datetime", 17)]
    fn test_type_expr_parser(
        #[case] input_text: &str,
        #[case] name: &str,
        #[case] exp_delta: usize,
    ) {
        let (delta, res) = TypeExpression::try_parse(input_text)
            .expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(name, res.text);
        assert_eq!(exp_delta, delta);
    }
}
