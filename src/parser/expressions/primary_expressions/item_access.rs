use serde::Serialize;

use crate::{
    parser::{
        core::TryParse,
        expressions::Expression,
        operators,
        parse_utils::{gen_error_ctx, next_char, skip_whitespace_and_comments, ParseResult},
    },
    ParseError, ERR_CONTEXT_SIZE,
};

use super::PrimaryExpression;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct ItemAccess<'a> {
    expr: PrimaryExpression<'a>,
    selector: Expression<'a>,
}

impl<'a> ItemAccess<'a> {
    #[cfg(test)]
    pub(crate) fn new(expr: PrimaryExpression<'a>, selector: Expression<'a>) -> Self {
        Self { expr, selector }
    }
}

impl<'a> TryParse<'a, Self> for ItemAccess<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace_and_comments(text);

        // For Item Access to be valid, There _has_ to be an '{' somewhere near.
        // To ensure that we are not in a situation where we recurse forever
        // and overflow the stack, we are going to make sure that the primary Expression we
        // parse is limited to the text immediately preceding the next `{`
        //
        // If There is no `{`, we will fail, as the current expression we are parsing cannot
        // possibly be an Item Access.
        if !(&text[parse_pointer..].contains(operators::OPEN_BRACE_STR)) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }
        let primary_end = text
            .chars()
            .take_while(|c| *c != operators::OPEN_BRACE)
            .count();
        let (delta, expr) = PrimaryExpression::try_parse(&text[parse_pointer..primary_end])?;
        parse_pointer += delta;
        parse_pointer += skip_whitespace_and_comments(&text[parse_pointer..]);

        if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::OPEN_BRACE {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };
        parse_pointer += 1; // Advance past the `{`
                            //
        let (delta, selector) = Expression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;
        let lookahead_pointer = skip_whitespace_and_comments(&text[parse_pointer..]);

        if next_char(&text[parse_pointer + lookahead_pointer..]).unwrap_or(' ')
            != operators::CLOSE_BRACE
        {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        parse_pointer += lookahead_pointer + 1; // Advance past the `}`

        // HACK: Do A lookahead to make sure that we haven't just parsed a part of an FieldAccess
        // Expression
        if next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::OPEN_BRACKET {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };
        Ok((parse_pointer, Self { expr, selector }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    use crate::parser::identifier::Identifier;

    #[rstest]
    #[case(
        r#" text{  inner{value} }"#, 
        22,
        ItemAccess {
            expr: PrimaryExpression::Identifier(Identifier::new("text")),
            selector: Expression::Primary(PrimaryExpression::ItemAccess( Box::new(ItemAccess {
                expr: PrimaryExpression::Identifier(Identifier::new("inner")),
                selector: Expression::Primary(PrimaryExpression::Identifier(Identifier::new("value")))
            }
            )))}
    )
    ]
    #[case(
        r#" text{  value }"#, 
        15,
        ItemAccess {
            expr: PrimaryExpression::Identifier(Identifier::new("text")),
            selector: Expression::Primary(PrimaryExpression::Identifier(Identifier::new("value"))) }
    )
    ]
    fn test_item_access_expression(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] exp_field: ItemAccess,
    ) {
        let (delta, field) = ItemAccess::try_parse(input_text)
            .expect(format!("Failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(exp_delta, delta);
        assert_eq!(exp_field, field);
    }

    #[rstest]
    #[case(r#" { value }"#)]
    fn test_item_access_fails(#[case] input_text: &str) {
        let res = ItemAccess::try_parse(input_text);
        match res {
            Ok(_) => assert!(false),
            Err(_) => assert!(true),
        }
    }
}
