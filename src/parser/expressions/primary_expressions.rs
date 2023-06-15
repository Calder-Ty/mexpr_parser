use std::eprintln;

use crate::{
    parser::{
        identifier::Identifier,
        keywords::is_func_keyword,
        literal::Literal,
        parse_utils::{self, gen_error_ctx, skip_whitespace, ParseResult},
    },
    ParseError,
};

use super::{record::Record, Expression};
use serde::Serialize;

// primary-expression:
// x      literal-expression
// x      list-expression
// x      record-expression
// x       identifier-expression
//       section-access-expression
//       parenthesized-expression
//       field-access-expression
//       item-access-expression
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
}

impl<'a> PrimaryExpression<'a> {
    // parses the stuff and returns an instance of itself
    pub fn try_parse(text: &'a str) -> Result<(usize, Self), ParseError> {
        if let Ok((i, val)) = Literal::try_parse(text) {
            return Ok((i, PrimaryExpression::Literal(val)));
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
        Err(ParseError::InvalidInput {
            pointer: 0,
            ctx: parse_utils::gen_error_ctx(text, 0, 5),
        })
    }
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct ListExpression<'a> {
    elements: Vec<Expression<'a>>,
}

impl<'a> ListExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);

        if text[parse_pointer..].chars().next().unwrap_or(' ') != '{' {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, 5),
            }));
        }
        parse_pointer += 1;
        let mut elements = vec![];
        loop {
            let (delta, el) = Expression::try_parse(&text[parse_pointer..])?;
            parse_pointer += delta + skip_whitespace(&text[parse_pointer + delta..]);
            elements.push(el);

            if text[parse_pointer..].chars().next().unwrap_or('}') == '}' {
                parse_pointer += 1; // Add to account that we have moved one forward
                break;
            }
            if text[parse_pointer..].chars().next().unwrap_or(',') != ',' {
                eprintln!("This Is not a regular Primary Expression, halting!");
                panic!(
                    "This is unexpected:\n{0}",
                    gen_error_ctx(text, parse_pointer, 10)
                );
            }
            parse_pointer += 1; // Skip the comma
        }

        Ok((parse_pointer, Self { elements }))
    }
}

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
        let mut parse_pointer = skip_whitespace(text);

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
        parse_pointer += skip_whitespace(&text[parse_pointer..]);
        if !&text[parse_pointer..].starts_with('(') {
            // It is invalid for a invokation to not start with '('
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, 5),
            }));
        } else {
            parse_pointer += 1; // Skip the opening '('
        }
        // Now we need to Parse the contents of the function invocation
        loop {
            // Check if it is empty function call
            if text[parse_pointer..].chars().next().unwrap_or(')') == ')' {
                parse_pointer += 1; // Add to account that we have moved one forward
                break;
            }
            let (delta, arg) =
                Expression::try_parse_with_lookahead(&text[parse_pointer..], arg_lookahead)?;
            args.push(arg);
            parse_pointer = parse_pointer
                + delta
                + parse_utils::skip_whitespace(&text[parse_pointer + delta..]);
            // If we come to the end of the text of the invocation, we want
            // to end
            if text[parse_pointer..].chars().next().unwrap_or(')') == ')' {
                parse_pointer += 1; // Add to account that we have moved one forward
                break;
            }
            if text[parse_pointer..].chars().next().unwrap_or(',') != ',' {
                panic!(
                    "This is unexpected:\n{0}",
                    gen_error_ctx(text, parse_pointer, 10)
                )
            }
            parse_pointer += 1; // Skip the comma
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
    let lookahead_pointer = skip_whitespace(text);

    if text[lookahead_pointer..].chars().next().unwrap_or(')') == ')' {
        true
    } else if text[lookahead_pointer..].chars().next().unwrap_or(',') == ',' {
        true
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use std::{assert_eq, todo};

    use super::*;
    use crate::parser::{
        expressions::TypeExpression,
        identifier::Identifier,
        literal::{Literal, NumberType},
    };
    use assert_matches::assert_matches;
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
    r#"This("Not a variable", true, identifier)"#, 
    "This",
    vec![
         PrimaryExpression::Literal(Literal::Text("Not a variable")), 
         PrimaryExpression::Literal(Literal::Logical(true)),
         PrimaryExpression::Identifier(Identifier::new("identifier"),
    )],
    40
) ]
    #[case(
    r#"This(#!" Not a 235.E10 variable"  ,false  , 1234.5 , 0x25)"#, 
    "This", 
    vec![
        PrimaryExpression::Literal(Literal::Verbatim(" Not a 235.E10 variable")), 
        PrimaryExpression::Literal(Literal::Logical(false)),
        PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5))),
        PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25))),
    ],
58) ]
    #[case(
    r#"This(" Not a 235.E10 variable", false, 1234.5, 0x25)"#, 
    "This", 
    vec![
        PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable")), 
        PrimaryExpression::Literal(Literal::Logical(false)),
        PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5))),
        PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25))),
    ],
52)
]
    #[case(
    r#"#date(" Not a 235.E10 variable", false, 1234.5, 0x25)"#, 
    "#date", 
    vec![
        PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable")), 
        PrimaryExpression::Literal(Literal::Logical(false)),
        PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5))),
        PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25))),
    ],
53)
]
    fn test_invokation_parser_mixed(
        #[case] input_text: &str,
        #[case] ident: &str,
        #[case] vars: Vec<PrimaryExpression>,
        #[case] exp_delta: usize,
    ) {
        let (delta, invokation) = Invocation::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        if let PrimaryExpression::Identifier(invoker) = invokation.invoker {
            assert_eq!(invoker.text(), ident)
        }
        assert_eq!(exp_delta, delta);

        for (i, arg) in invokation.args.iter().enumerate() {
            match arg {
                Expression::Each(_) => todo!(),
                Expression::Primary(PrimaryExpression::List(_)) => todo!(),
                Expression::Primary(PrimaryExpression::Record(_)) => todo!(),
                Expression::Primary(PrimaryExpression::Identifier(ident)) => {
                    assert_matches!(&vars[i], PrimaryExpression::Identifier(expected) => {
                        assert_eq!(ident.text(), expected.text())
                    })
                }
                Expression::Primary(PrimaryExpression::Invoke(_invoke)) => todo!(),
                Expression::Primary(PrimaryExpression::Literal(_literal)) => {
                    assert_matches!(&vars[i], PrimaryExpression::Literal(expected) => {
                        assert_matches!(expected, _literal)
                    })
                }
                Expression::Let(_) | Expression::Logical(_) | Expression::Type(_) => {
                    todo!("Need to test these cases")
                }
            }
        }
    }

    #[rstest]
    #[case("identifier")]
    fn test_invocation_parser_fail(#[case] input_text: &str) {
        match Invocation::try_parse(input_text) {
            Err(_) => assert!(true),
            Ok(_) => assert!(false),
        }
    }

    #[rstest]
    #[case(
    r#"{" Not a 235.E10 variable", false, 1234.5, 0x25}"#, 
    vec![
        Expression::Primary(PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable"))),
        Expression::Primary(PrimaryExpression::Literal(Literal::Logical(false))),
        Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5)))),
        Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Int(0x25)))),
    ],
48)
]
    #[case(
    r#"{" Not a 235.E10 variable", false, 1234.5, type datetime }"#, 
    vec![
        Expression::Primary(PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable"))),
        Expression::Primary(PrimaryExpression::Literal(Literal::Logical(false))),
        Expression::Primary(PrimaryExpression::Literal(Literal::Number(NumberType::Float(1234.5)))),
        Expression::Type(crate::parser::expressions::Type::TypeStatement( TypeExpression { text: "type datetime"} ))
    ],
58)
]
    fn test_list_expression_parser(
        #[case] input_text: &str,
        #[case] exp_elements: Vec<Expression>,
        #[case] exp_delta: usize,
    ) {
        let (delta, list) = ListExpression::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(exp_delta, delta);

        for (i, arg) in list.elements.iter().enumerate() {
            match arg {
                Expression::Each(_) => todo!(),
                Expression::Primary(PrimaryExpression::Record(_)) => todo!(),
                Expression::Primary(PrimaryExpression::List(_)) => todo!(),
                Expression::Primary(PrimaryExpression::Identifier(ident)) => {
                    assert_matches!(&exp_elements[i], Expression::Primary(PrimaryExpression::Identifier(expected)) => {
                        assert_eq!(ident.text(), expected.text())
                    })
                }
                Expression::Primary(PrimaryExpression::Invoke(_invoke)) => todo!(),
                Expression::Primary(PrimaryExpression::Literal(_literal)) => {
                    assert_matches!(&exp_elements[i], Expression::Primary(PrimaryExpression::Literal(expected)) => {
                        assert_matches!(expected, _literal)
                    })
                }
                Expression::Let(_) => assert!(false),
                Expression::Type(crate::parser::expressions::Type::TypeStatement(actual_type)) => {
                    assert_matches!(exp_elements[i], Expression::Type(
                        crate::parser::expressions::Type::TypeStatement(TypeExpression{text: exp_text})) => {
                        assert_eq!(exp_text, actual_type.text)

                    })
                }
                Expression::Type(_) => {
                    assert!(false)
                }
                Expression::Logical(_) => {
                    todo!()
                }
            }
        }
    }
}
