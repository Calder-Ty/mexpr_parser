use std::{ops::Mul, todo};

use serde::Serialize;

use crate::{
    parser::{
        keywords, operators,
        parse_utils::{followed_by_valid_seperator, gen_error_ctx, skip_whitespace, ParseResult},
    },
    ParseError,
};

use super::{Type, TypeExpression};

/// logical-or-expression:
///       logical-and-expression
///       logical-and-expression or logical-or-expression
/// logical-and-expression:
///       is-expression
///       logical-and-expression and is-expression
struct LogicalExpression {}

/// is-expression:
///   as-expression
///   is-expression is nullable-primitive-type
/// nullable-primitive-type:
///   nullable[opt] primitive-type
struct IsExpression {}

/// as-expression:
///   equality-expression
///   as-expression as nullable-primitive-type
struct AsExpression {}

/// equality-expression:
///    relational-expression
///    relational-expression = equality-expression
///    relational-expression <> equality-expression
struct EqualityExpression {}

/// relational-expression:
///     additive-expression
///     additive-expression < relational-expression
///     additive-expression > relational-expression
///     additive-expression <= relational-expression
///     additive-expression >= relational-expression
struct RelationalExpression {}

/// These are the Arithmetic expressions
///
/// additive-expression:
///       multiplicative-expression
///       multiplicative-expression + additive-expression
///       multiplicative-expression - additive-expression
///       multiplicative-expression & _additive-expression
/// multiplicative-expression:
///       metadata-expression
///       metadata-expression * multiplicative-expression
///       metadata-expression / multiplicative-expression
#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct AdditiveExpression<'a> {
    rhs: MultiplicativeExpression<'a>,
    lhs: Option<Lhs<'a, Box<AdditiveExpression<'a>>>>,
}

impl<'a> AdditiveExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);

        let (delta, rhs) = MultiplicativeExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);

        let operator = match text[lookahead_pointer..].chars().next().unwrap_or('_') {
            operators::PLUS => operators::PLUS_STR,
            operators::MINUS => operators::MINUS_STR,
            _ => return Ok((parse_pointer, (Self { rhs, lhs: None }))),
        };

        parse_pointer = lookahead_pointer + 1;

        let (delta, expr) = AdditiveExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lhs = Some(Lhs::new(Box::new(expr), operator));

        Ok((parse_pointer, (Self { rhs, lhs })))
    }
}

#[derive(Debug, Serialize, PartialEq)]
struct MultiplicativeExpression<'a> {
    rhs: MetadataExpression<'a>,
    lhs: Option<Lhs<'a, Box<MultiplicativeExpression<'a>>>>,
}

impl<'a> MultiplicativeExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);

        let (delta, rhs) = MetadataExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);

        let operator = match text[lookahead_pointer..].chars().next().unwrap_or('_') {
            operators::STAR => operators::STAR_STR,
            operators::DIV => operators::DIV_STR,
            _ => return Ok((parse_pointer, (Self { rhs, lhs: None }))),
        };

        parse_pointer = lookahead_pointer + 1;

        let (delta, expr) = MultiplicativeExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lhs = Some(Lhs::new(Box::new(expr), operator));

        Ok((parse_pointer, (Self { rhs, lhs })))
    }
}

#[derive(Debug, Serialize, PartialEq)]
struct Lhs<'a, T> {
    expr: T,
    operator: &'a str,
}

impl<'a, T> Lhs<'a, T> {
    pub fn new(expr: T, operator: &'a str) -> Self {
        Self { expr, operator }
    }
}

/// metadata-expression:
///    unary-expression
///    unary-expression meta unary-expression
#[derive(Debug, Serialize, PartialEq)]
struct MetadataExpression<'a> {
    rhs: UnaryExpression<'a>,
    lhs: Option<Lhs<'a, UnaryExpression<'a>>>,
}

impl<'a> MetadataExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);

        let (delta, rhs) = UnaryExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);
        if !(text[lookahead_pointer..].starts_with(keywords::META)
            && followed_by_valid_seperator(&text[lookahead_pointer..], 4))
        {
            return Ok((parse_pointer, (Self { rhs, lhs: None })));
        };

        parse_pointer = lookahead_pointer + 4;

        let (delta, expr) = UnaryExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lhs = Some(Lhs::new(expr, keywords::META));

        Ok((parse_pointer, (Self { rhs, lhs })))
    }
}

/// unary-expression:
///   type-expression
///   + unary-expression
///   - unary-expression
///   not unary-expression
#[derive(Debug, Serialize, PartialEq)]
enum UnaryExpression<'a> {
    Type(Type<'a>),
    Unary(Unary<'a>),
}

#[derive(Debug, Serialize, PartialEq)]
struct Unary<'a> {
    operator: &'a str,
    expr: Box<UnaryExpression<'a>>,
}

impl<'a> UnaryExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        if let Ok((i, val)) = Type::try_parse(text) {
            return Ok((i, Self::Type(val)));
        }
        if let Ok((i, val)) = Unary::try_parse(text) {
            return Ok((i, Self::Unary(val)));
        }
        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: gen_error_ctx(text, 0, 10),
        }))
    }
}

impl<'a> Unary<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{
        expressions::primary_expressions::PrimaryExpression,
        literal::{Literal, NumberType},
    };

    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(
        "1 + 2",
        5,
        AdditiveExpression {
            rhs: MultiplicativeExpression {
                rhs: MetadataExpression {
                    rhs: UnaryExpression::Type(Type::Primary(PrimaryExpression::Literal(
                        Literal::Number(NumberType::Float(1.0)),
                    ))),
                    lhs: None,
                },
                lhs: None,
            },
            lhs: Some(Lhs::new(
                Box::new(AdditiveExpression {
                    rhs: MultiplicativeExpression {
                        rhs: MetadataExpression {
                            rhs: UnaryExpression::Type(Type::Primary(PrimaryExpression::Literal(
                                Literal::Number(NumberType::Float(2.0)),
                            ))),
                            lhs: None,
                        },
                        lhs: None,
                    },
                    lhs: None,
                }),
                "+",
            )),
        },
    )]
    fn test_additive_expression(#[case] input: &str, #[case] expected_delta: usize, #[case] expected: AdditiveExpression) {
        let (delta, val) = AdditiveExpression::try_parse(input).expect("Test Failed");
        assert_eq!(expected_delta, delta);
        assert_eq!(expected, val);
    }

    #[rstest]
    fn test_multiplicative_expression() {
        let input = "1 * 2";
        let expected_delta = 5;
        let expected = MultiplicativeExpression {
            rhs: MetadataExpression {
                rhs: UnaryExpression::Type(Type::Primary(PrimaryExpression::Literal(
                    Literal::Number(NumberType::Float(1.0)),
                ))),
                lhs: None,
            },
            lhs: Some(Lhs::new(
                Box::new(MultiplicativeExpression {
                    rhs: MetadataExpression {
                        rhs: UnaryExpression::Type(Type::Primary(PrimaryExpression::Literal(
                            Literal::Number(NumberType::Float(2.0)),
                        ))),
                        lhs: None,
                    },
                    lhs: None,
                }),
                "*",
            )),
        };
        let (delta, val) = MultiplicativeExpression::try_parse(input).expect("Test Failed");
        assert_eq!(expected_delta, delta);
        assert_eq!(expected, val);
    }
}
