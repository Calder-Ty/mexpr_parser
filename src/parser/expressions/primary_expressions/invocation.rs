use serde::Serialize;

use crate::{
    parser::{
        expressions::Expression,
        identifier::Identifier,
        keywords::is_func_keyword,
        operators,
        parse_utils::{self, gen_error_ctx, next_char, skip_whitespace_and_comments, ParseResult},
    },
    ParseError, ERR_CONTEXT_SIZE,
};

use super::PrimaryExpression;

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct Invocation<'a> {
    pub invoker: PrimaryExpression<'a>,
    pub args: Vec<Expression<'a>>,
}

impl<'a> Invocation<'a> {
    #[cfg(test)]
    pub fn new(invoker: PrimaryExpression<'a>, args: Vec<Expression<'a>>) -> Self {
        Self { invoker, args }
    }

    pub fn try_parse(text: &'a str) -> ParseResult<Invocation<'a>> {
        // To start, we need to identifiy the calling Expresion. Lets try:
        let mut parse_pointer = skip_whitespace_and_comments(text);

        // Check if is a Keyword function. This is not well documented in the standard. But there
        // are a few Keywords that are actually functions. We Should check if it is one of them.
        let ident_txt_stop = text[parse_pointer..]
            .chars()
            .take_while(|c| *c != '(')
            .count();

        let (delta, invoker) =
            if is_func_keyword(&text[parse_pointer..parse_pointer + ident_txt_stop]) {
                (
                    ident_txt_stop,
                    Identifier::from_keyword(&text[parse_pointer..parse_pointer + ident_txt_stop]),
                )
            } else {
                Identifier::try_parse(&text[parse_pointer..])?
            };

        parse_pointer += delta;
        let mut args = vec![];
        parse_pointer += skip_whitespace_and_comments(&text[parse_pointer..]);
        if next_char(&text[parse_pointer..]).unwrap_or(' ') != (operators::OPEN_PAREN) {
            // It is invalid for a invokation to not start with '('
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        } else {
            parse_pointer += 1; // Skip the opening '('
        }
        // Now we need to Parse the contents of the function invocation
        loop {
            if text[parse_pointer..].chars().next().is_none() {
                return Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }));
            }

            // Check if it is close of function call
            if text[parse_pointer..].chars().next().unwrap_or(')') == operators::CLOSE_PAREN {
                parse_pointer += 1; // Add to account that we have moved one forward
                break;
            }
            let (delta, arg) =
                Expression::try_parse_with_lookahead(&text[parse_pointer..], arg_lookahead)?;
            args.push(arg);
            parse_pointer += delta;
            parse_pointer =
                parse_pointer + parse_utils::skip_whitespace_and_comments(&text[parse_pointer..]);

            // If we come to the end of the text of the invocation, we want
            // to end
            if text[parse_pointer..].chars().next().unwrap_or('_') == operators::CLOSE_PAREN {
                parse_pointer += 1; // Add to account that we have moved one forward
                break;
            }
            if text[parse_pointer..].chars().next().unwrap_or(',') != operators::COMMA {
                panic!(
                    "This is unexpected:\n{0}",
                    gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE)
                )
            } else if next_char(&text[parse_pointer..]).is_some() {
                parse_pointer += 1; // Skip the comma
            }
        }

        Ok((
            parse_pointer,
            Invocation {
                invoker: PrimaryExpression::Identifier(invoker),
                args,
            },
        ))
    }
}

/// Validates that the text is followed by a `,` or `)`
fn arg_lookahead(text: &str) -> bool {
    let lookahead_pointer = skip_whitespace_and_comments(text);

    if text[lookahead_pointer..].chars().next().unwrap_or(')') == ')' {
        true
    } else {
        text[lookahead_pointer..].chars().next().unwrap_or(',') == ','
    }
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;
    use crate::parser::{
        expressions::{each::EachExpression, primary_expressions::field_access::FieldAccess},
        identifier::Identifier,
        literal::{Literal, NumberType},
    };
    use rstest::rstest;

    #[rstest]
    #[case(r#"This()"#, "This", vec![])]
    #[case(r#"This("Not a variable", "More Text")"#, "This", vec!["Not a variable", "More Text"])]
    #[case(r#"This("Not a variable")"#, "This", vec!["Not a variable"])]
    fn test_invokation_parser(
        #[case] input_text: &str,
        #[case] ident: &str,
        #[case] vars: Vec<&str>,
    ) {
        let (_, invokation) = Invocation::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        if let PrimaryExpression::Identifier(invoker) = invokation.invoker {
            assert_eq!(invoker.text(), ident)
        }

        assert_eq!(invokation.args.len(), vars.len());
        for (i, arg) in invokation.args.iter().enumerate() {
            match arg {
                Expression::Primary(PrimaryExpression::Literal(Literal::Text(v))) => {
                    assert_eq!(v, &vars[i])
                }
                _ => assert!(false),
            }
        }
    }

    #[rstest]
    #[case(
    r#"Table.AddColumn(#"Inserted Start of Month", "Period", each Date.ToText([Start of Month],"MMM yyyy"))"#,
        Invocation {
        invoker: PrimaryExpression::Identifier(Identifier::new("Table.AddColumn")),
        args: vec![
         Expression::Primary(PrimaryExpression::Identifier(Identifier::new("Inserted Start of Month"))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Text("Period"))),
         Expression::Each(Box::new(EachExpression::new(
                    Expression::Primary(PrimaryExpression::Invoke(Box::new(
                        Invocation {
                            invoker: PrimaryExpression::Identifier(Identifier::new ( "Date.ToText" )),
                            args: vec![
                                Expression::Primary(PrimaryExpression::FieldAccess(Box::new(FieldAccess::new (
                                    None,
                                    Identifier::new ( "Start of Month")
                                )))),
                                Expression::Primary(PrimaryExpression::Literal(Literal::Text("MMM yyyy")))
                            ]
                        }
                    )))
                )))
    ]
        },
    100
) ]
    #[case(
     r#"This("Not a variable", true, identifier)"#,
         Invocation {
         invoker: PrimaryExpression::Identifier(Identifier::new("This")),
         args: vec![
          Expression::Primary(PrimaryExpression::Literal(Literal::Text("Not a variable"))),
          Expression::Primary(PrimaryExpression::Literal(Literal::Logical(true))),
          Expression::Primary(PrimaryExpression::Identifier(Identifier::new("identifier")),
     )],
         },
     40
 ) ]
    #[case(
     r#"This(#!" Not a 235.E10 variable"  ,false  , 1234.5 , 0x25)"#,
         Invocation {
     invoker: PrimaryExpression::Identifier(Identifier::new("This")),
     args: vec![
         Expression::Primary(PrimaryExpression::Literal(Literal::Verbatim(" Not a 235.E10 variable"))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Logical(false))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5)))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25)))),
     ],
         },
 58) ]
    #[case(
     r#"This(" Not a 235.E10 variable", false, 1234.5, 0x25)"#,
         Invocation {

     invoker: PrimaryExpression::Identifier(Identifier::new("This")),
     args: vec![
         Expression::Primary(PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable"))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Logical(false))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5)))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25)))),
     ]
         },
 52)
 ]
    #[case(
     r#"#date(" Not a 235.E10 variable", false, 1234.5, 0x25)"#,
         Invocation {
     invoker: PrimaryExpression::Identifier(Identifier::new("#date")),
     args: vec![
         Expression::Primary(PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable"))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Logical(false))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5)))),
         Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25)))),
     ],
         },
 53)
 ]
    fn test_invokation_parser_mixed(
        #[case] input_text: &str,
        #[case] expected: Invocation,
        #[case] exp_delta: usize,
    ) {
        let (delta, invokation) = Invocation::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(expected, invokation);
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case("identifier")]
    fn test_invocation_parser_fail(#[case] input_text: &str) {
        match Invocation::try_parse(input_text) {
            Err(_) => assert!(true),
            Ok(_) => assert!(false),
        }
    }
}
