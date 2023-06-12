//! Function Expression
//!
//! https://learn.microsoft.com/en-us/powerquery-m/m-spec-consolidated-grammar#function-expression

use serde::Serialize;

use crate::parser::core::TryParse;
use crate::parser::identifier::Identifier;
use crate::parser::parse_utils::{
    followed_by_valid_seperator, followed_by_whitespace, gen_error_ctx, skip_whitespace,
    ParseResult,
};
use crate::ParseError;

use super::{Expression, PRIMITIVE_TYPES};

/// function-expression:
/// `(` parameter-listopt `)` return-type[opt] `=>` function-body
/// function-body:
///     expression
/// parameter-list:
///     fixed-parameter-list
///     fixed-parameter-list , optional-parameter-list
///     optional-parameter-list
/// fixed-parameter-list:
///     parameter
///     parameter , fixed-parameter-list
/// parameter:
///     parameter-name parameter-type[opt]
/// parameter-name:
///     identifier
/// parameter-type:
///     assertion
/// return-type:
///     assertion
/// assertion:
///     `as` nullable-primitive-type
/// optional-parameter-list:
///     optional-parameter
///     optional-parameter `,` optional-parameter-list
/// optional-parameter:
///     `optional` parameter
#[derive(Debug, PartialEq, Serialize)]
struct FunctionExpression<'a> {
    parameters: Vec<FuncParameter<'a>>,
    return_type: Option<&'a str>,
    body: Expression<'a>,
}



#[derive(Debug, PartialEq, Serialize)]
struct FuncParameter<'a> {
    name: Identifier<'a>,
    param_type: Option<Assertion<'a>>,
}

impl<'a> TryParse<'a> for FuncParameter<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        let (delta, ident) = Identifier::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        let lookahead_pointer = skip_whitespace(&text[parse_pointer..]);
        if text[lookahead_pointer..].chars().next().unwrap_or(',') == ',' {
            return Ok((
                parse_pointer,
                Self {
                    name: ident,
                    param_type: None,
                },
            ));
        };

        let (delta, param_type) = Assertion::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((parse_pointer, Self {
            name: ident,
            param_type: Some(param_type),
        }))
    }
}

#[derive(Debug, PartialEq, Serialize)]
struct Assertion<'a> {
    value: &'a str,
}

impl<'a> TryParse<'a> for Assertion<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);

        if !(text[parse_pointer..].starts_with("as")
            && followed_by_whitespace(&text[parse_pointer..], 2))
        {
            // TODO: Add Constant for Parse Pointer context size
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        };

        parse_pointer += 2; // skip `as`
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        // nullable-primitive-type allows the text "nullable" to appear
        if (text[parse_pointer..].starts_with("nullable")
            && followed_by_whitespace(&text[parse_pointer..], 8))
        {
            parse_pointer += 8;
            parse_pointer += skip_whitespace(&text[parse_pointer..])
        };

        let mut value = None;
        for type_name in PRIMITIVE_TYPES {
            if text[parse_pointer..].starts_with(type_name)
                && followed_by_valid_seperator(&text[parse_pointer..], type_name.len())
            {
                parse_pointer += type_name.len();
                value = Some(type_name);
                break;
            };
        }

        if let Some(val) = value {
            Ok((parse_pointer, Self { value: val }))
        } else {
            Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }))
        }
    }
}

#[cfg(test)]
mod tests {

    use std::assert_eq;

    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(
        "as nullable time, more stuff",
        16,

        Assertion {
            value: "time"
        })]
    fn parse_assertion(#[case] input: &str, #[case] exp_delta: usize, #[case] expected: Assertion) {
        let (delta, res) = Assertion::try_parse(input).expect("Unable to parse input");

        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }



}
