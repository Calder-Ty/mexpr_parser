use crate::{
    parser::{
        core::TryParse,
        expressions::Expression,
        operators,
        parse_utils::{gen_error_ctx, next_char, skip_whitespace_and_comments, ParseResult},
    },
    ParseError, ERR_CONTEXT_SIZE,
};

pub(super) struct ParenthesizedExpression { }

impl<'a> TryParse<'a, Expression<'a>> for ParenthesizedExpression {
    fn try_parse(text: &'a str) -> ParseResult<Expression<'_>>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace_and_comments(text);
        if next_char(&text[parse_pointer..]).unwrap_or('_') != operators::OPEN_PAREN {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };
        parse_pointer += 1; // Skip OPEN_PAREN
        let (delta, expr) =
            Expression::try_parse_with_lookahead(&text[parse_pointer..], parenthesized_lookahead)?;
        parse_pointer += delta;
        parse_pointer += 1; // Skip CLOSE_PAREN (the lookahead above guarantees that we have a
                            // closing paren
        Ok((parse_pointer, expr))
    }
}

fn parenthesized_lookahead(text: &str) -> bool {
    let lookahead_pointer = skip_whitespace_and_comments(text);
    next_char(&text[lookahead_pointer..]).unwrap_or(' ') == operators::CLOSE_PAREN
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;
    use crate::parser::{expressions::primary_expressions::PrimaryExpression, literal::Literal};
    use rstest::rstest;

    #[rstest]
    #[case(
        r#"("thing")"#,
        9,
        Expression::Primary(PrimaryExpression::Literal(Literal::Text("thing")))
    )]
    fn parenthesized_expression(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] expected: Expression,
    ) {
        let (delta, actual) = ParenthesizedExpression::try_parse(input_text)
            .expect("Unable to parse input");

        assert_eq!(exp_delta, delta);
        assert_eq!(expected, actual);
    }
}
