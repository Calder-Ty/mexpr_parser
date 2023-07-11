use serde::Serialize;

use crate::{
    parser::{
        expressions::Expression,
        operators,
        parse_utils::{self, gen_error_ctx, next_char, skip_whitespace_and_comments, ParseResult}, core::TryParse,
    },
    ParseError, ERR_CONTEXT_SIZE,
};

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct ListExpression<'a> {
    elements: Vec<Expression<'a>>,
}

impl<'a> ListExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace_and_comments(text);

        if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::OPEN_BRACE {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }
        parse_pointer += 1;
        let mut elements = vec![];
        loop {
            parse_pointer += skip_whitespace_and_comments(&text[parse_pointer..]);
            if text[parse_pointer..]
                .chars()
                .next()
                .unwrap_or(operators::CLOSE_BRACE)
                == operators::CLOSE_BRACE
            {
                parse_pointer += 1; // Add to account that we have moved one forward
                break;
            }

            let (delta, el) = Expression::try_parse(&text[parse_pointer..])?;
            elements.push(el);
            parse_pointer += delta + skip_whitespace_and_comments(&text[parse_pointer + delta..]);

            if text[parse_pointer..].starts_with(operators::RANGE) {
                parse_pointer += operators::RANGE.len();
                let (delta, el) = Expression::try_parse(&text[parse_pointer..])?;
                elements.push(el);
                parse_pointer += delta + skip_whitespace_and_comments(&text[parse_pointer + delta..]);
            }

            if text[parse_pointer..]
                .chars()
                .next()
                .unwrap_or(operators::CLOSE_BRACE)
                == operators::CLOSE_BRACE
            {
                parse_pointer += 1; // Add to account that we have moved one forward
                break;
            }

            if text[parse_pointer..]
                .chars()
                .next()
                .unwrap_or(operators::COMMA)
                != operators::COMMA
            {
                eprintln!("This Is not a regular Primary Expression, halting!");
                panic!(
                    "This is unexpected:\n{0}",
                    gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE)
                );
            }
            parse_pointer += 1; // Skip the comma
        }

        Ok((parse_pointer, Self { elements }))
    }
}


#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;
    use crate::parser::{
        expressions::{
            logical::{
                AdditiveExpression, AsExpression, EqualityExpression, IsExpression, LogicalAnd,
                LogicalExpression, LogicalOr, MetadataExpression, MultiplicativeExpression,
                RelationalExpression, UnaryExpression,
            },
            primary_expressions::PrimaryExpression,
            type_expressions::{PrimaryType, PrimitiveType, TypeExpression},
        },
        literal::{Literal, NumberType},
    };
    use rstest::rstest;

    #[rstest]
    #[case(
    r#"{" Not a 235.E10 variable", false, 1234.5, 0x25}"#, 
        ListExpression { elements:
            vec![
                Expression::Primary(PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable"))),
                Expression::Primary(PrimaryExpression::Literal(Literal::Logical(false))),
                Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5)))),
                Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25)))),
            ]
        },
48)
]
    #[case(
    r#"{" Not a 235.E10 variable", false, 1234.5, type datetime }"#, 
        ListExpression { elements:
            vec![
                Expression::Primary(PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable"))),
                Expression::Primary(PrimaryExpression::Literal(Literal::Logical(false))),
                Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5)))),
                Expression::Logical(
                    LogicalExpression::Or(
                    LogicalOr::new(
                    LogicalAnd::new(
                    IsExpression::AsExpression( AsExpression::Equality(
                    EqualityExpression::new(
                        RelationalExpression::new(
                            AdditiveExpression::new(
                                MultiplicativeExpression::new(
                                    MetadataExpression::new(
                                        UnaryExpression::Type(
                                            TypeExpression::PrimaryType(
                                                PrimaryType::PrimitiveType(
                                                    PrimitiveType::new( "datetime" )
                                                )
                                            )),
                                    None ),
                                None ),
                            None ),
                        None),
                    None),
                )
        ), None
                            ), None)))
            ]
        },
58)
]
    fn test_list_expression_parser(
        #[case] input_text: &str,
        #[case] exp_elements: ListExpression,
        #[case] exp_delta: usize,
    ) {
        let (delta, list) = ListExpression::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(exp_delta, delta);
        assert_eq!(exp_elements, list);
    }
}
