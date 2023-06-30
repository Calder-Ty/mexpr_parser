use serde::Serialize;

use crate::{
    parser::{
        core::TryParse,
        keywords, operators,
        parse_utils::{
            followed_by_valid_seperator, followed_by_whitespace, gen_error_ctx, next_char,
            skip_whitespace, ParseResult,
        },
    },
    ParseError, ERR_CONTEXT_SIZE,
};

use super::type_expressions::{PrimaryType, TypeExpression};

/// logical-or-expression:
///       logical-and-expression
///       logical-and-expression or logical-or-expression
/// logical-and-expression:
///       is-expression
///       logical-and-expression and is-expression
#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum LogicalExpression<'a> {
    Or(LogicalOr<'a>),
    And(LogicalAnd<'a>),
}

impl<'a> TryParse<'a, Self> for LogicalExpression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        if let Ok((delta, i)) = LogicalAnd::try_parse(text) {
            return Ok((delta, LogicalExpression::And(i)));
        };
        if let Ok((delta, i)) = LogicalOr::try_parse(text) {
            return Ok((delta, LogicalExpression::Or(i)));
        };
        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        }))
    }
}


#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct LogicalOr<'a> {
    rhs: LogicalAnd<'a>,
    lhs: Option<Box<LogicalOr<'a>>>,
}

impl<'a> TryParse<'a, Self> for LogicalOr<'a> {

    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        let (delta, rhs) = LogicalAnd::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);
        if !(text[lookahead_pointer..].starts_with(keywords::OR)
            && followed_by_whitespace(&text[lookahead_pointer..], keywords::OR.len()))
        {
            return Ok((parse_pointer, Self { rhs, lhs:None }));
        };

        parse_pointer = lookahead_pointer + keywords::OR.len();

        let (delta, lhs) = LogicalOr::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        return Ok((parse_pointer, Self { rhs, lhs: Some(Box::new(lhs)) }));
    }
}



#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct LogicalAnd<'a> {
    rhs: IsExpression<'a>,
    lhs: Option<Box<LogicalAnd<'a>>>,
}

impl<'a> LogicalAnd<'a> {
    #[cfg(test)]
    pub(crate) fn new(rhs: IsExpression<'a>, lhs: Option<Box<LogicalAnd<'a>>>) -> Self { Self { rhs, lhs } }
}

impl<'a> TryParse<'a, Self> for LogicalAnd<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        let (delta, rhs) = IsExpression::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);
        if !(text[lookahead_pointer..].starts_with(keywords::AND)
            && followed_by_whitespace(&text[lookahead_pointer..], keywords::AND.len()))
        {
            return Ok((parse_pointer, Self { rhs, lhs:None }));
        };

        parse_pointer = lookahead_pointer + keywords::AND.len();

        let (delta, lhs) = LogicalAnd::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        return Ok((parse_pointer, Self { rhs, lhs: Some(Box::new(lhs)) }));
    }
}

/// is-expression:
///   as-expression
///   is-expression is nullable-primitive-type
/// nullable-primitive-type:
///   nullable[opt] primitive-type
#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum IsExpression<'a> {
    AsExpression(AsExpression<'a>),
    WithNullable(Box<IsExpressionWithNullable<'a>>),
}

impl<'a> TryParse<'a, Self> for IsExpression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        if let Ok((delta, i)) = AsExpression::try_parse(text) {
            return Ok((delta, IsExpression::AsExpression(i)));
        };
        if let Ok((delta, i)) = IsExpressionWithNullable::try_parse(text) {
            return Ok((delta, IsExpression::WithNullable(Box::new(i))));
        };
        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        }))
    }
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct IsExpressionWithNullable<'a> {
    expr: AsExpression<'a>,
    nullable: PrimaryType<'a>,
}

impl<'a> TryParse<'a, Self> for IsExpressionWithNullable<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        let (delta, expr) = AsExpression::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        if !(text[parse_pointer..].starts_with(keywords::IS)
            && followed_by_whitespace(&text[parse_pointer..], keywords::IS.len()))
        {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        let (delta, nullable) = PrimaryType::try_parse_primitive(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((parse_pointer, Self { expr, nullable }))
    }
}
/// as-expression:
///   equality-expression
///   as-expression as nullable-primitive-type
#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum AsExpression<'a> {
    Equality(EqualityExpression<'a>),
    WithNullable(Box<AsExressionWithNullable<'a>>),
}

impl<'a> TryParse<'a, Self> for AsExpression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        if let Ok((delta, i)) = EqualityExpression::try_parse(text) {
            return Ok((delta, AsExpression::Equality(i)));
        };
        if let Ok((delta, i)) = AsExressionWithNullable::try_parse(text) {
            return Ok((delta, AsExpression::WithNullable(Box::new(i))));
        };
        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        }))
    }
}


/// The spec indicates that you could have lots of chained as type as type as type.
/// But that seems really bad, and is recursive causing overflows. I'm going to 
/// disallow it for now.
#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct AsExressionWithNullable<'a> {
    expr: EqualityExpression<'a>,
    nullable: PrimaryType<'a>,
}

impl<'a> TryParse<'a, Self> for AsExressionWithNullable<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        let (delta, expr) = EqualityExpression::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        if !(text[parse_pointer..].starts_with(keywords::AS)
            && followed_by_whitespace(&text[parse_pointer..], keywords::AS.len()))
        {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        let (delta, nullable) = PrimaryType::try_parse_primitive(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((parse_pointer, Self { expr, nullable }))
    }
}

/// equality-expression:
///    relational-expression
///    relational-expression = equality-expression
///    relational-expression <> equality-expression
#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct EqualityExpression<'a> {
    rhs: RelationalExpression<'a>,
    lhs: Option<Lhs<'a, Box<EqualityExpression<'a>>>>,
}

impl<'a> EqualityExpression<'a> {
    #[cfg(test)]
    pub(crate) fn new(
        rhs: RelationalExpression<'a>,
        lhs: Option<Lhs<'a, Box<EqualityExpression<'a>>>>,
    ) -> Self {
        Self { rhs, lhs }
    }
}

impl<'a> TryParse<'a, Self> for EqualityExpression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);
        let (delta, rhs) = RelationalExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);
        let mut lookahead_iter = text[lookahead_pointer..].chars();
        let operator = (lookahead_iter.next(), lookahead_iter.next());

        let operator = match operator {
            (Some(operators::EQUAL), _) => operators::EQUAL_STR,
            (Some(operators::LT), Some(operators::GT)) => operators::NE,
            (_, _) => return Ok((parse_pointer, Self { rhs, lhs: None })),
        };
        parse_pointer = lookahead_pointer + operator.len();

        let (delta, lhs_inner) = EqualityExpression::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        Ok((
            parse_pointer,
            Self {
                rhs,
                lhs: Some(Lhs {
                    expr: Box::new(lhs_inner),
                    operator,
                }),
            },
        ))
    }
}

/// relational-expression:
///     additive-expression
///     additive-expression < relational-expression
///     additive-expression > relational-expression
///     additive-expression <= relational-expression
///     additive-expression >= relational-expression
#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct RelationalExpression<'a> {
    rhs: AdditiveExpression<'a>,
    lhs: Option<Lhs<'a, Box<RelationalExpression<'a>>>>,
}

impl<'a> RelationalExpression<'a> {
    #[cfg(test)]
    pub(crate) fn new(
        rhs: AdditiveExpression<'a>,
        lhs: Option<Lhs<'a, Box<RelationalExpression<'a>>>>,
    ) -> Self {
        Self { rhs, lhs }
    }
}

impl<'a> TryParse<'a, Self> for RelationalExpression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);
        let (delta, rhs) = AdditiveExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);
        let mut lookahead_iter = text[lookahead_pointer..].chars();
        let operator = (lookahead_iter.next(), lookahead_iter.next());

        let operator = match operator {
            (Some(operators::GT), Some(operators::EQUAL)) => operators::GTE,
            (Some(operators::LT), Some(operators::EQUAL)) => operators::LTE,
            (Some(operators::GT), _) => operators::GT_STR,
            (Some(operators::LT), Some(operators::GT)) => {
                // This is part of an Equality Expression. End
                return Ok((parse_pointer, Self { rhs, lhs: None }));
            }
            (Some(operators::LT), _) => operators::LT_STR,
            (_, _) => return Ok((parse_pointer, Self { rhs, lhs: None })),
        };
        parse_pointer = lookahead_pointer + operator.len();

        let (delta, lhs_inner) = RelationalExpression::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        Ok((
            parse_pointer,
            Self {
                rhs,
                lhs: Some(Lhs {
                    expr: Box::new(lhs_inner),
                    operator,
                }),
            },
        ))
    }
}

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
    #[cfg(test)]
    pub(crate) fn new(
        rhs: MultiplicativeExpression<'a>,
        lhs: Option<Lhs<'a, Box<AdditiveExpression<'a>>>>,
    ) -> Self {
        Self { rhs, lhs }
    }

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
pub(crate) struct MultiplicativeExpression<'a> {
    rhs: MetadataExpression<'a>,
    lhs: Option<Lhs<'a, Box<MultiplicativeExpression<'a>>>>,
}

impl<'a> MultiplicativeExpression<'a> {
    #[cfg(test)]
    pub(crate) fn new(
        rhs: MetadataExpression<'a>,
        lhs: Option<Lhs<'a, Box<MultiplicativeExpression<'a>>>>,
    ) -> Self {
        Self { rhs, lhs }
    }

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
pub(crate) struct Lhs<'a, T> {
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
pub(crate) struct MetadataExpression<'a> {
    rhs: UnaryExpression<'a>,
    lhs: Option<Lhs<'a, UnaryExpression<'a>>>,
}

impl<'a> MetadataExpression<'a> {
    #[cfg(test)]
    pub(crate) fn new(rhs: UnaryExpression<'a>, lhs: Option<Lhs<'a, UnaryExpression<'a>>>) -> Self {
        Self { rhs, lhs }
    }

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
pub(crate) enum UnaryExpression<'a> {
    Type(TypeExpression<'a>),
    Unary(Unary<'a>),
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct Unary<'a> {
    operator: &'a str,
    expr: Box<UnaryExpression<'a>>,
}

impl<'a> UnaryExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        if let Ok((i, val)) = TypeExpression::try_parse(text) {
            return Ok((i, Self::Type(val)));
        }
        if let Ok((i, val)) = Unary::try_parse(text) {
            return Ok((i, Self::Unary(val)));
        }
        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        }))
    }
}

impl<'a> Unary<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        let (delta, operator) = match next_char(&text[parse_pointer..]) {
            Some(operators::MINUS) => (1, operators::MINUS_STR),
            Some(operators::PLUS) => (1, operators::PLUS_STR),
            Some(_) => {
                if text[parse_pointer..].starts_with(keywords::NOT)
                    && followed_by_whitespace(&text[parse_pointer..], keywords::NOT.len())
                {
                    (keywords::NOT.len(), keywords::NOT)
                } else {
                    return Err(Box::new(ParseError::InvalidInput {
                        pointer: parse_pointer,
                        ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                    }));
                }
            }
            None => {
                return Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }));
            }
        };
        parse_pointer += delta;

        let (delta, expr) = UnaryExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;
        Ok((
            parse_pointer,
            Self {
                operator,
                expr: Box::new(expr),
            },
        ))
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
        "1 + 2 > 3 <> false",
        18,
        EqualityExpression {
        rhs: RelationalExpression {
            rhs: AdditiveExpression {
            rhs: MultiplicativeExpression {
                rhs: MetadataExpression {
                    rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
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
                            rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
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
            lhs: Some(Lhs { expr: Box::new(RelationalExpression {
                rhs: AdditiveExpression {
                    rhs: MultiplicativeExpression {
                        rhs: MetadataExpression {
                            rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
                                Literal::Number(NumberType::Float(3.0)),
                            ))),
                            lhs: None,
                        },
                        lhs: None,
                    },
                    lhs: None
                },
            lhs: None
            },),
                operator: ">",
            }
            )},
            lhs: Some(Lhs { expr: Box::new(
                EqualityExpression {
                    rhs: RelationalExpression {
                        rhs: AdditiveExpression {
                            rhs: MultiplicativeExpression {
                                rhs: MetadataExpression {
                                    rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
                                        Literal::Logical(false),
                                    ))),
                                    lhs: None,
                                },
                                lhs: None,
                            },
                            lhs: None
                        },
                    lhs: None
                    },
                    lhs: None
                },),
                operator: "<>",
            }
            )},
    )]
    fn test_equality_expression(
        #[case] input: &str,
        #[case] expected_delta: usize,
        #[case] expected: EqualityExpression,
    ) {
        let (delta, val) = EqualityExpression::try_parse(input).expect("Test Failed");
        assert_eq!(expected_delta, delta);
        assert_eq!(expected, val);
    }

    #[rstest]
    #[case(
        "1 + 2 > 3",
        9,
        RelationalExpression {
            rhs: AdditiveExpression {
            rhs: MultiplicativeExpression {
                rhs: MetadataExpression {
                    rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
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
                            rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
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
            lhs: Some(Lhs { expr: Box::new(RelationalExpression {
                rhs: AdditiveExpression {
                    rhs: MultiplicativeExpression {
                        rhs: MetadataExpression {
                            rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
                                Literal::Number(NumberType::Float(3.0)),
                            ))),
                            lhs: None,
                        },
                        lhs: None,
                    },
                    lhs: None
                },
            lhs: None
            },),
                operator: ">",
            }
            )}
    )]
    fn test_relational_expression(
        #[case] input: &str,
        #[case] expected_delta: usize,
        #[case] expected: RelationalExpression,
    ) {
        let (delta, val) = RelationalExpression::try_parse(input).expect("Test Failed");
        assert_eq!(expected_delta, delta);
        assert_eq!(expected, val);
    }
    #[rstest]
    #[case(
        "1 + 2",
        5,
        AdditiveExpression {
            rhs: MultiplicativeExpression {
                rhs: MetadataExpression {
                    rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
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
                            rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
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
    fn test_additive_expression(
        #[case] input: &str,
        #[case] expected_delta: usize,
        #[case] expected: AdditiveExpression,
    ) {
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
                rhs: UnaryExpression::Type(TypeExpression::Primary(PrimaryExpression::Literal(
                    Literal::Number(NumberType::Float(1.0)),
                ))),
                lhs: None,
            },
            lhs: Some(Lhs::new(
                Box::new(MultiplicativeExpression {
                    rhs: MetadataExpression {
                        rhs: UnaryExpression::Type(TypeExpression::Primary(
                            PrimaryExpression::Literal(Literal::Number(NumberType::Float(2.0))),
                        )),
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
