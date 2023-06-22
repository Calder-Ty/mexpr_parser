use serde::Serialize;

use crate::{parser::{
    core::TryParse,
    keywords,
    parse_utils::{followed_by_whitespace, gen_error_ctx, skip_whitespace},
}, ERR_CONTEXT_SIZE};

use super::Expression;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct EachExpression<'a> {
    body: Expression<'a>,
}

impl<'a> EachExpression<'a> {
    #[cfg(test)]
    pub(crate) fn new(body: Expression<'a>) -> Self { Self { body } }
}

impl<'a> TryParse<'a, Self> for EachExpression<'a> {
    fn try_parse(text: &'a str) -> crate::parser::parse_utils::ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        if !(text[parse_pointer..].starts_with(keywords::EACH)
            && followed_by_whitespace(&text[parse_pointer..], keywords::EACH.len()))
        {
            return Err(Box::new(crate::ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        parse_pointer += keywords::EACH.len();
        // The Specification says the Each Expression should have a function-body,
        // But the function-body is just an Expression.
        let (delta, body) = Expression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((parse_pointer, Self { body }))
    }
}

#[cfg(test)]
mod tests {

    use std::{assert_eq, vec};

    use crate::parser::expressions::{
        primary_expressions::{Invocation, PrimaryExpression},
        Expression, Identifier,
    };

    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(
        "each func.call()",
        16,
        EachExpression {
            body:
                Expression::Primary(
                    PrimaryExpression::Invoke(
                        Box::new(
                            Invocation::new(
                                PrimaryExpression::Identifier(Identifier::new("func.call")),
                                vec![]
                            )
                        )
                    )
                )
        }
    )]
    fn parse_func_expression(
        #[case] input: &str,
        #[case] exp_delta: usize,
        #[case] expected: EachExpression,
    ) {
        let (delta, res) = EachExpression::try_parse(input).expect("Unable to parse input");

        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }
}
