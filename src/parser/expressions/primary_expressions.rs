use std::eprintln;

use crate::{
    parser::{
        core::TryParse,
        identifier::Identifier,
        keywords::is_func_keyword,
        literal::Literal,
        operators,
        parse_utils::{self, gen_error_ctx, next_char, skip_whitespace, ParseResult},
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
// x      field-access-expression
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
    FieldAccess(FieldAccess<'a>),
    ItemAccess(Box<ItemAccess<'a>>),
}

impl<'a> PrimaryExpression<'a> {
    // parses the stuff and returns an instance of itself
    pub fn try_parse(text: &'a str) -> Result<(usize, Self), ParseError> {
        if let Ok((i, val)) = ItemAccess::try_parse(text) {
            return Ok((i, PrimaryExpression::ItemAccess(Box::new(val))));
        }
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
        if let Ok((i, val)) = FieldAccess::try_parse(text) {
            return Ok((i, PrimaryExpression::FieldAccess(val)));
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

        if next_char(&text[parse_pointer..]).unwrap_or(' ') != '{' {
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

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct FieldAccess<'a> {
    // The Grammar posted by Microsoft for Field Access Expressions has it start with
    // a Primary Expression. However, this recursive relationship is dangerous, as there
    // is a very legitimate opportunity that we would be stuck in a loop because the pointer will
    // never progress, and keep trying to find an expression.
    //
    // Since FieldAccess expressions can be done alone (something mentioned in the docs, but
    // not allowed by the Grammar). We are going to just assume that a Primary Expression preceeds
    // field Access, because it won't always be the case anyway.
    // https://learn.microsoft.com/en-us/powerquery-m/m-spec-functions#simplified-declarations
    selector: Identifier<'a>,
}

impl<'a> TryParse<'a> for FieldAccess<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::OPEN_BRACKET) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        };
        parse_pointer += 1; // Advance past the `[`

        let (delta, selector) = Identifier::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta; // Advance past the `]`
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::CLOSE_BRACKET) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        };

        parse_pointer += 1;

        Ok((parse_pointer, Self { selector }))
    }
}


#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct ItemAccess<'a> {

    expr: PrimaryExpression<'a>,
    selector: Expression<'a>

}

impl<'a> TryParse<'a> for ItemAccess<'a> {

    fn try_parse(text: &'a str) -> ParseResult<Self>
        where
            Self: Sized {

        let mut parse_pointer = skip_whitespace(text);

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
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        }
        let primary_end = text.chars().take_while(|c| *c != operators::OPEN_BRACE).count();
        let (delta, expr) = PrimaryExpression::try_parse(&text[parse_pointer..primary_end])?;
        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::OPEN_BRACE) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        };
        parse_pointer += 1; // Advance past the `{`
        //
        let (delta, selector) = Expression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;
        let lookahead_pointer = skip_whitespace(&text[parse_pointer..]);

        if !(next_char(&text[parse_pointer + lookahead_pointer..]).unwrap_or(' ') == operators::CLOSE_BRACE) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        };
        parse_pointer += lookahead_pointer + 1; // Advance past the `}`
        Ok((parse_pointer, Self { expr: expr, selector }))
    }
}


#[cfg(test)]
mod tests {
    use std::{assert_eq, todo};

    use super::*;
    use crate::parser::{
        expressions::type_expressions::TypeExpression,
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
                Expression::Primary(PrimaryExpression::ItemAccess(_)) => todo!(),
                Expression::Primary(PrimaryExpression::FieldAccess(_)) => todo!(),
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
                Expression::Type(crate::parser::expressions::Type::TypeStatement( TypeExpression::new("type datetime") ))
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

    #[rstest]
    #[case(
        r#" [  text ]"#, 
        10,
        FieldAccess { selector: Identifier::new("text") } 
    )
    ]
    fn test_field_access_expression(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] exp_field: FieldAccess,
    ) {
        let (delta, field) = FieldAccess::try_parse(input_text)
            .expect(format!("Failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(exp_delta, delta);
        assert_eq!(exp_field, field);
    }

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
    #[case(r#" { value }"#,)
    ]
    fn test_item_access_fails(
        #[case] input_text: &str,
    ) {
        let res = ItemAccess::try_parse(input_text);
        match res {
            Ok(_) => assert!(false),
            Err(_) => assert!(true),
        }
    }
}
