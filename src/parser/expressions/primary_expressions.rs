use std::{eprintln, marker::PhantomData};

use crate::{
    parser::{
        core::TryParse,
        identifier::Identifier,
        keywords::is_func_keyword,
        literal::Literal,
        operators,
        parse_utils::{self, gen_error_ctx, next_char, skip_whitespace, ParseResult},
    },
    ParseError, ERR_CONTEXT_SIZE,
};

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
        if let Ok((i, val)) = ItemAccess::try_parse(text) {
            return Ok((i, PrimaryExpression::ItemAccess(Box::new(val))));
        }
        if let Ok((i, val)) = FieldAccess::try_parse(text) {
            return Ok((i, PrimaryExpression::FieldAccess(Box::new(val))));
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
        if let Ok((i, val)) = ParenthesizedExpression::<PrimaryExpression>::try_parse(text) {
            return Ok((i, PrimaryExpression::ParenthesizedExpression(Box::new(val))));
        }
        Err(ParseError::InvalidInput {
            pointer: 0,
            ctx: parse_utils::gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
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
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
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
                    gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE)
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
                return Err(Box::new(ParseError::InvalidInput
                    {
                    pointer: parse_pointer,
                    ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE) 
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
            parse_pointer = parse_pointer
                + delta
                + parse_utils::skip_whitespace(&text[parse_pointer + delta..]);

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
    // a Primary Expression. This is required by the spec, but in practice
    // it doesn't always have to be there. (eg, each statement).
    // https://learn.microsoft.com/en-us/powerquery-m/m-spec-functions#simplified-declarations
    expr: Option<PrimaryExpression<'a>>,
    selector: Identifier<'a>,
}

impl<'a> TryParse<'a, Self> for FieldAccess<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        // For FieldAccess to be valid, There _has_ to be an '[' somewhere near.
        // To ensure that we are not in a situation where we recurse forever
        // and overflow the stack, we are going to make sure that the primary Expression we
        // parse is limited to the text immediately preceding the next `[`, on the same
        // syntax level.
        //
        // If There is no `[`, we will fail, as the current expression we are parsing cannot
        // possibly be an FieldAccess.
        if !(&text[parse_pointer..].contains(operators::OPEN_BRACKET_STR)) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }

        let primary_end = if let Some(v) = find_next_bracket_on_syntax_level(&text[parse_pointer..]){
            v
        } else {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };


        let (delta, expr) = match PrimaryExpression::try_parse(&text[parse_pointer..parse_pointer + primary_end]) {
            Ok((i, v)) => (i, Some(v)),
            Err(_) => (0, None),
        };

        parse_pointer += delta;

        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::OPEN_BRACKET) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };
        parse_pointer += 1; // Advance past the `[`

        let (delta, selector) = Identifier::try_parse_generalized(&text[parse_pointer..])?;

        parse_pointer += delta; // Advance past the `]`
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::CLOSE_BRACKET) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        parse_pointer += 1;

        Ok((parse_pointer, Self { expr, selector }))
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct ItemAccess<'a> {
    expr: PrimaryExpression<'a>,
    selector: Expression<'a>,
}

impl<'a> TryParse<'a, Self> for ItemAccess<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
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
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }
        let primary_end = text
            .chars()
            .take_while(|c| *c != operators::OPEN_BRACE)
            .count();
        let (delta, expr) = PrimaryExpression::try_parse(&text[parse_pointer..primary_end])?;
        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::OPEN_BRACE) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };
        parse_pointer += 1; // Advance past the `{`
                            //
        let (delta, selector) = Expression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;
        let lookahead_pointer = skip_whitespace(&text[parse_pointer..]);

        if !(next_char(&text[parse_pointer + lookahead_pointer..]).unwrap_or(' ')
            == operators::CLOSE_BRACE)
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
        Ok((
            parse_pointer,
            Self {
                expr,
                selector,
            },
        ))
    }
}


/// This finds the next instance of the character on the same syntactic level as the current
/// expression
fn find_next_brace_on_syntax_level(text: &str) -> Option<usize>{

    let mut level = 0;
    for (i, c) in text.char_indices() {
        // If we hit our target on our level, return
        match c {
            operators::OPEN_BRACE if level==0 => return Some(i),
            operators::OPEN_BRACKET | operators::OPEN_PAREN => level += 1,
            operators::CLOSE_BRACKET | operators::CLOSE_PAREN => level -= 1,
        _ => ()
        };
        if level < 0 {
            return None
        };
    };
    // We've reached the end of the rope here.
    None

}

fn find_next_bracket_on_syntax_level(text: &str) -> Option<usize>{

    let mut level = 0;
    for (i, c) in text.char_indices() {
        // If we hit our target on our level, return
        match c {
            operators::OPEN_BRACKET if level == 0 => return Some(i),
            operators::OPEN_BRACE | operators::OPEN_PAREN => level += 1,
            operators::CLOSE_BRACE | operators::CLOSE_PAREN => level -= 1,
        _ => ()
        };
        if level < 0 {
            return None
        };
    };
    // We've reached the end of the rope here.
    None

}

struct ParenthesizedExpression<'a, T: 'a> {
    _phantom: PhantomData<&'a T>,
}

impl<'a, T> TryParse<'a, Expression<'a>> for ParenthesizedExpression<'a, T> {

    fn try_parse(text: &'a str) -> ParseResult<Expression<'_>>
        where
            Self: Sized {

        let mut parse_pointer = skip_whitespace(text);
        if next_char(&text[parse_pointer..]).unwrap_or('_') != operators::OPEN_PAREN {
            return Err(
                Box::new(
                    ParseError::InvalidInput { 
                        pointer: parse_pointer, 
                        ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE)
                    }
                )
            );
        };
        parse_pointer += 1; // Skip OPEN_PAREN
        let (delta, expr) = Expression::try_parse_with_lookahead(&text[parse_pointer..], parenthesized_lookahead)?;
        parse_pointer += delta;
        parse_pointer += 1; // Skip CLOSE_PAREN (the lookahead above guarantees that we have a
        // closing paren
        Ok((parse_pointer, expr))

    }

}

fn parenthesized_lookahead(text: &str) -> bool {
    let lookahead_pointer = skip_whitespace(text);
    next_char(&text[lookahead_pointer..]).unwrap_or(' ') == operators::CLOSE_PAREN
}




#[cfg(test)]
mod tests {
    use std::{assert_eq, todo};

    use super::*;
    use crate::parser::{
        expressions::{
            type_expressions::{
                TypeExpression, PrimaryType, PRIMITIVE_TYPES, PrimitiveType
            }, logical::{
                AdditiveExpression, MultiplicativeExpression,  MetadataExpression, UnaryExpression
            },
            each::EachExpression,
        },
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
                                Expression::Primary(PrimaryExpression::FieldAccess(Box::new(FieldAccess { 
                                    expr: None,
                                    selector: Identifier::new ( "Start of Month")
                                }))), 
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
                Expression::Logical(AdditiveExpression::new(
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
                    None ))
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
        FieldAccess { expr: None, selector: Identifier::new("text") }
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
    #[case(
        r#" Source{ [ value ] }[txt]"#,
        25,
        FieldAccess{
            expr: Some(
                PrimaryExpression::ItemAccess(
                    Box::new(ItemAccess {
                        expr: PrimaryExpression::Identifier(Identifier::new("Source")),
                        selector: Expression::Primary(
                            PrimaryExpression::FieldAccess( 
                                Box::new(
                                FieldAccess {
                                    expr: None,
                                    selector: Identifier::new("value")
                                })
                            )
                        )
                    }
                    )
                )),

            selector: Identifier::new("txt")
        }
    )
    ]
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

    #[rstest]
    #[case(r#" { value }"#)]
    fn test_item_access_fails(#[case] input_text: &str) {
        let res = ItemAccess::try_parse(input_text);
        match res {
            Ok(_) => assert!(false),
            Err(_) => assert!(true),
        }
    }

    #[rstest]
    #[case(r#"("thing")"#, 9, Expression::Primary(PrimaryExpression::Literal(Literal::Text("thing"))))]
    fn parenthesized_expression(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] expected: Expression
    ) {
        let (delta, actual) = ParenthesizedExpression::<PrimaryExpression>::try_parse(input_text).expect("Unable to parse input");

        assert_eq!(exp_delta, delta);
        assert_eq!(expected, actual);
    }

    #[rstest]
    #[case("[]", Some(0))]
    #[case("([()])", None)]
    #[case("([()])[]", Some(6))]
    fn test_find_next_bracket_on_syntax_level(
        #[case] input_text: &str,
        #[case]  expected: Option<usize>,
    ) {
        let actual = find_next_bracket_on_syntax_level(input_text);
        assert_eq!(expected, actual);
    }
}
