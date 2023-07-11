mod field_access;
mod invocation;
mod item_access;
mod list_expression;
mod parenthesized_expression;

use crate::{
    parser::{core::TryParse, identifier::Identifier, literal::Literal, parse_utils},
    ParseError, ERR_CONTEXT_SIZE,
};

pub(crate) use self::field_access::FieldAccess;
pub(crate) use self::invocation::Invocation;
pub(crate) use self::item_access::ItemAccess;
pub(crate) use self::list_expression::ListExpression;
use self::parenthesized_expression::ParenthesizedExpression;

use super::{record::Record, Expression};
use serde::Serialize;

// primary-expression:
// x      literal-expression
// x      list-expression
// x      record-expression
// x       identifier-expression
//       section-access-expression
// x      parenthesized-expression
// x      field-access-expression
// x      item-access-expression
// x      invoke-expression
//       not-implemented-expression
//
/// For now We are only implementing a parser for Identifier Expression and
/// Invoke Expressions. This is the minimum we need for the task.
#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum PrimaryExpression<'a> {
    /// invoke-expression:
    ///     primary-expression <(> argument-listopt <)>
    /// argument-list:
    ///     expression
    ///     expression , argument-list
    List(ListExpression<'a>),
    Identifier(Identifier<'a>),
    Invoke(Box<Invocation<'a>>),
    Literal(Literal<'a>),
    Record(Record<'a>),
    FieldAccess(Box<FieldAccess<'a>>),
    ItemAccess(Box<ItemAccess<'a>>),
    ParenthesizedExpression(Box<Expression<'a>>),
}

impl<'a> PrimaryExpression<'a> {
    // parses the stuff and returns an instance of itself
    pub fn try_parse(text: &'a str) -> Result<(usize, Self), ParseError> {
        if let Ok((i, val)) = Literal::try_parse(text) {
            return Ok((i, PrimaryExpression::Literal(val)));
        }
        if let Ok((i, val)) = ItemAccess::try_parse(text) {
            return Ok((i, PrimaryExpression::ItemAccess(Box::new(val))));
        }
        if let Ok((i, val)) = FieldAccess::try_parse(text) {
            return Ok((i, PrimaryExpression::FieldAccess(Box::new(val))));
        }
        if let Ok((i, val)) = Record::try_parse(text) {
            return Ok((i, PrimaryExpression::Record(val)));
        }
        if let Ok((i, val)) = Invocation::try_parse(text) {
            return Ok((i, PrimaryExpression::Invoke(Box::new(val))));
        }
        if let Ok((i, val)) = ListExpression::try_parse(text) {
            return Ok((i, PrimaryExpression::List(val)));
        }
        if let Ok((i, val)) = Identifier::try_parse(text) {
            return Ok((i, PrimaryExpression::Identifier(val)));
        }
        if let Ok((i, val)) = ParenthesizedExpression::try_parse(text) {
            return Ok((i, PrimaryExpression::ParenthesizedExpression(Box::new(val))));
        }
        Err(ParseError::InvalidInput {
            pointer: 0,
            ctx: parse_utils::gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        })
    }

    pub fn try_parse_with_lookahead<F>(text: &'a str, lookahead_func: F) -> Result<(usize, Self), ParseError>
    where
        F: Fn(&'a str) -> bool,
    {
        if let Ok((i, val)) = Literal::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::Literal(val)));
            }
        }
        if let Ok((i, val)) = ItemAccess::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::ItemAccess(Box::new(val))));
            }
        }
        if let Ok((i, val)) = FieldAccess::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::FieldAccess(Box::new(val))));
            }
        }
        if let Ok((i, val)) = Record::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::Record(val)));
            }
        }
        if let Ok((i, val)) = Invocation::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::Invoke(Box::new(val))));
            }
        }
        if let Ok((i, val)) = ListExpression::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::List(val)));
            }
        }
        if let Ok((i, val)) = Identifier::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::Identifier(val)));
            }
        }
        if let Ok((i, val)) = ParenthesizedExpression::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, PrimaryExpression::ParenthesizedExpression(Box::new(val))));
            }
        }
        Err(ParseError::InvalidInput {
            pointer: 0,
            ctx: parse_utils::gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        })
    }
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;
    use crate::parser::identifier::Identifier;
    use rstest::rstest;

    #[rstest]
    #[case(
        r#" Source{ [ value ] }[txt]"#,
        25,
        FieldAccess::new(
            Some(PrimaryExpression::ItemAccess(Box::new(ItemAccess::new(
                PrimaryExpression::Identifier(Identifier::new("Source")),
                Expression::Primary(PrimaryExpression::FieldAccess(Box::new(FieldAccess::new(
                    None,
                    Identifier::new("value")
                ))))
            )))),
            Identifier::new("txt")
        )
    )]
    fn test_item_and_field_access_expression(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] exp_field: FieldAccess,
    ) {
        let (delta, field) = FieldAccess::try_parse(input_text)
            .expect(format!("Failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(exp_delta, delta);
        assert_eq!(exp_field, field);
    }
}
