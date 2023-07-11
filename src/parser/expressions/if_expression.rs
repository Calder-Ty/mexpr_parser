//! if-expression:
//!       if if-condition then true-expression else false-expression
//! if-condition:
//!     expression
//! true-expression:
//!     expression
//! false-expression:
//!     expression

use serde::Serialize;

use crate::{
    parser::{
        core::TryParse,
        keywords,
        parse_utils::{followed_by_valid_seperator, gen_error_ctx, skip_whitespace_and_comments},
    },
    ERR_CONTEXT_SIZE,
};

use super::Expression;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct IfExpression<'a> {
    condition: Expression<'a>,
    if_true: Expression<'a>,
    if_false: Expression<'a>,
}

impl<'a> TryParse<'a, Self> for IfExpression<'a> {
    fn try_parse(text: &'a str) -> crate::parser::parse_utils::ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace_and_comments(text);
        if !text[parse_pointer..].starts_with(keywords::IF) {
            return Err(Box::new(crate::ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };
        parse_pointer += keywords::IF.len();
        let (delta, condition) =
            Expression::try_parse_with_lookahead(&text[parse_pointer..], then_lookahead)?;

        parse_pointer += delta;
        parse_pointer += skip_whitespace_and_comments(&text[parse_pointer..]);
        parse_pointer += keywords::THEN.len();

        let (delta, if_true) =
            Expression::try_parse_with_lookahead(&text[parse_pointer..], else_lookahead)?;

        parse_pointer += delta;
        parse_pointer += skip_whitespace_and_comments(&text[parse_pointer..]);
        parse_pointer += keywords::ELSE.len();

        let (delta, if_false) = Expression::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        Ok((
            parse_pointer,
            Self {
                condition,
                if_true,
                if_false,
            },
        ))
    }
}

fn then_lookahead(text: &str) -> bool {
    let lookahead_pointer = skip_whitespace_and_comments(text);
    text[lookahead_pointer..].starts_with(keywords::THEN)
        && followed_by_valid_seperator(&text[lookahead_pointer..], keywords::THEN.len())
}

fn else_lookahead(text: &str) -> bool {
    let lookahead_pointer = skip_whitespace_and_comments(text);
    text[lookahead_pointer..].starts_with(keywords::ELSE)
        && followed_by_valid_seperator(&text[lookahead_pointer..], keywords::ELSE.len())
}

#[cfg(test)]
mod test {
    use crate::parser::{
        expressions::{
            logical::{
                AdditiveExpression, AsExpression, EqualityExpression, IsExpression, Lhs,
                LogicalAnd, LogicalExpression, LogicalOr, MetadataExpression,
                MultiplicativeExpression, RelationalExpression, UnaryExpression,
            },
            primary_expressions::{FieldAccess, PrimaryExpression},
            type_expressions::TypeExpression,
        },
        identifier::Identifier,
        literal::Literal,
        operators,
    };
    use rstest::rstest;

    use super::*;

    #[rstest]
    fn if_expression() {
        let input = r#"if [days_from_go_live] = null then "Empty" else null),"#;
        let expected_delta = 52;
        let expected = IfExpression {
            condition: Expression::Logical(LogicalExpression::Or(LogicalOr::new(
                LogicalAnd::new(
                    IsExpression::AsExpression(AsExpression::Equality(EqualityExpression::new(
                        RelationalExpression::new(
                            AdditiveExpression::new(
                                MultiplicativeExpression::new(
                                    MetadataExpression::new(
                                        UnaryExpression::Type(TypeExpression::Primary(
                                            PrimaryExpression::FieldAccess(Box::new(
                                                FieldAccess::new(
                                                    None,
                                                    Identifier::new("days_from_go_live"),
                                                ),
                                            )),
                                        )),
                                        None,
                                    ),
                                    None,
                                ),
                                None,
                            ),
                            None,
                        ),
                        Some(Lhs::new(
                            Box::new(EqualityExpression::new(
                                RelationalExpression::new(
                                    AdditiveExpression::new(
                                        MultiplicativeExpression::new(
                                            MetadataExpression::new(
                                                UnaryExpression::Type(TypeExpression::Primary(
                                                    PrimaryExpression::Literal(Literal::Null),
                                                )),
                                                None,
                                            ),
                                            None,
                                        ),
                                        None,
                                    ),
                                    None,
                                ),
                                None,
                            )),
                            operators::EQUAL_STR,
                        )),
                    ))),
                    None,
                ),
                None,
            ))),

            if_true: Expression::Primary(PrimaryExpression::Literal(Literal::Text("Empty"))),
            if_false: Expression::Primary(PrimaryExpression::Literal(
                crate::parser::literal::Literal::Null,
            )),
        };
        let (delta, res) = IfExpression::try_parse(input).expect("Test Failed");
        assert_eq!(expected, res);
        assert_eq!(expected_delta, delta);
    }
}
