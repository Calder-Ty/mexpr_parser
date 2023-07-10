//! Record
//! https://learn.microsoft.com/en-us/powerquery-m/m-spec-consolidated-grammar#record-expression
//!
//! record-expression:
//!     [ field-listopt ]
//! field-list:
//!     field
//!     field , field-list
//! field:
//!     field-name = expression
//! field-name:
//!     generalized-identifier
//!     quoted-identifier

use std::vec;

use serde::Serialize;

use crate::{
    parser::{
        identifier::Identifier,
        parse_utils::{gen_error_ctx, skip_whitespace, ParseResult, next_char}, operators,
    },
    ParseError, ERR_CONTEXT_SIZE,
};

use super::Expression;

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct Record<'a> {
    fields: Vec<Field<'a>>,
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct Field<'a> {
    name: Identifier<'a>,
    expr: Expression<'a>,
}

impl<'a> Record<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);

        if !&text[parse_pointer..].starts_with('[') {
            // Not a record
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        parse_pointer += 1;

        let mut fields = vec![];

        loop {
            if next_char(&text[parse_pointer..]).unwrap_or(operators::CLOSE_BRACKET) == operators::CLOSE_BRACKET {
                // End of the record,
                parse_pointer += 1;
                break;
            }

            let (delta, name) = Identifier::try_parse_generalized(&text[parse_pointer..])?;
            parse_pointer += delta;
            parse_pointer += skip_whitespace(&text[parse_pointer..]);

            if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::EQUAL {
                // The next character must be a '='.
                return Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }));
            }

            parse_pointer += 1;
            let (delta, expr) = Expression::try_parse(&text[parse_pointer..])?;

            fields.push(Field { name, expr });

            parse_pointer += delta;
            parse_pointer += skip_whitespace(&text[parse_pointer..]);

            if next_char(&text[parse_pointer..]).unwrap_or(operators::CLOSE_BRACKET) == operators::CLOSE_BRACKET {
                // End of the record,
                parse_pointer += 1;
                break;
            }

            if !text[parse_pointer..].starts_with(',') {
                return Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }));
            }
            parse_pointer += 1;
        }

        Ok((parse_pointer, Self { fields }))
    }
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use crate::parser::expressions::primary_expressions::PrimaryExpression;

    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(r#" [   ident  = "abcdefg" , ident2 = "hijklmn"  ]"#,
         47,
        Record {
            fields: vec![Field {
                name: Identifier::new("ident"),
                expr: Expression::Primary(PrimaryExpression::Literal(
                    crate::parser::literal::Literal::Text("abcdefg"),
                )),
            }, Field {
                name: Identifier::new("ident2"),
                expr: Expression::Primary(PrimaryExpression::Literal(
                    crate::parser::literal::Literal::Text("hijklmn"),
                )),
            }
            ],
        })]
    #[case(r#" [   ident  = "abcdefg"   ]"#,
         27,
        Record {
            fields: vec![Field {
                name: Identifier::new("ident"),
                expr: Expression::Primary(PrimaryExpression::Literal(
                    crate::parser::literal::Literal::Text("abcdefg"),
                )),
            }],
        })]
    #[case(r#"[#"ident"="abcdefg"]}"#,
         20,
        Record {
            fields: vec![Field {
                name: Identifier::new("ident"),
                expr: Expression::Primary(PrimaryExpression::Literal(
                    crate::parser::literal::Literal::Text("abcdefg"),
                )),
            }],
        })]
    #[case(r#"[ident="abcdefg"]}"#,
         17,
        Record {
            fields: vec![Field {
                name: Identifier::new("ident"),
                expr: Expression::Primary(PrimaryExpression::Literal(
                    crate::parser::literal::Literal::Text("abcdefg"),
                )),
            }],
        })]
    fn test_try_parse(
        #[case] input: &str,
        #[case] expected_delta: usize,
        #[case] expected: Record,
    ) {
        let (delta, val) = Record::try_parse(input).expect("Test Failed!");
        assert_eq!(expected_delta, delta);
        assert_eq!(expected, val)
    }
}
