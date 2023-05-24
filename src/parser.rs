mod identifier;
mod literal;

use self::{
    identifier::Identifier,
    literal::Literal,
    parse_utils::{skip_whitespace, ParseError, ParseResult},
};

pub(crate) mod parse_utils {
    use thiserror::Error;
    pub type ParseResult<T> = Result<(usize, T), Box<ParseError>>;

    #[derive(Debug, Error)]
    pub enum ParseError {
        #[error("Input is Invalid, Unable to proceed at character {pointer} \n{ctx:?}")]
        InvalidInput { pointer: usize, ctx: String },
    }

    pub(crate) fn gen_error_ctx(text: &str, pointer: usize, size: usize) -> String {
        let start: usize;
        let end: usize;
        if pointer < size {
            start = 0;
        } else {
            start = pointer - size
        }

        if pointer + size > text.len() {
            end = text.len();
        } else {
            end = pointer + size
        }

        let ctx = &text[start..end];
        let padding = "-".repeat(pointer - start);
        format!("{ctx}\n{padding}^")
    }

    #[inline]
    pub(crate) fn skip_whitespace(text: &str) -> usize {
        text.char_indices()
            .take_while(|(_, c)| (*c).is_whitespace())
            .count()
    }

    #[cfg(test)]
    mod tests {
        use super::gen_error_ctx;
        use rstest::rstest;

        #[rstest]
        #[case(
            "this is some text that has errored",
            10,
            5,
            r#"is some te
-----^"#
        )]
        #[case(
            "this is some text that has errored",
            0,
            5,
            r#"this 
^"#
        )]
        #[case(
            "this is some text that has errored",
            32,
            5,
            r#"errored
-----^"#
        )]
        fn test_get_error_ctx(
            #[case] input: &str,
            #[case] pointer: usize,
            #[case] size: usize,
            #[case] exp_res: &str,
        ) {
            let res = gen_error_ctx(input, pointer, size);
            assert_eq!(
            exp_res,
                res
            )
        }
    }
}

/// let-expression:
///     <let> variable-list <in> expression
/// variable-list:
///     variable
///     variable <,> variable-list
/// variable:
///     variable-name <=> expression
/// variable-name:
///     identifier
#[derive(Debug)]
pub struct LetExpression<'a> {
    variable_list: Vec<VariableAssignment<'a>>,
}

impl<'a> LetExpression<'a> {
    pub fn try_parse(text: &'a str) -> parse_utils::ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        if !&text[parse_pointer..].starts_with("let ") {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, 5),
            }));
        }
        parse_pointer += 4; // skip 'let '

        let mut variable_list = vec![];
        loop {
            let (delta, assignment) = VariableAssignment::try_parse(&text[parse_pointer..])?;
            variable_list.push(assignment);
            parse_pointer += delta;
            parse_pointer += skip_whitespace(&text[parse_pointer..]);
            if text[parse_pointer..].chars().next().unwrap_or(' ') != ',' {
                break;
            }
            parse_pointer += 1 // Skip the ','
        }

        Ok((parse_pointer, Self { variable_list }))
    }
}

#[derive(Debug)]
struct VariableAssignment<'a> {
    name: Identifier<'a>,
    expr: PrimaryExpression<'a>,
}

impl<'a> VariableAssignment<'a> {
    fn try_parse(text: &'a str) -> parse_utils::ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        let (delta, name) = Identifier::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;
        // Skip let part of the statement
        // split on the = sign, now pass that in
        let sep_delta = text[parse_pointer..]
            .chars()
            .take_while(|c| (*c) != '=')
            .count()
            + 1;

        parse_pointer += sep_delta;

        let (delta, expr) = PrimaryExpression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((parse_pointer, Self { name, expr }))
    }
}

// primary-expression:
// x      literal-expression
//       list-expression
//       record-expression
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
#[derive(Debug)]
enum PrimaryExpression<'a> {
    /// invoke-expression:
    ///     primary-expression <(> argument-listopt <)>
    /// argument-list:
    ///     expression
    ///     expression , argument-list
    Identifier(Identifier<'a>),
    Invoke(Box<Invocation<'a>>),
    Literal(Literal<'a>),
}

impl<'a> PrimaryExpression<'a> {
    // parses the stuff and returns an instance of itself
    fn try_parse(text: &'a str) -> Result<(usize, Self), ParseError> {
        if let Ok((i, val)) = Literal::try_parse(text) {
            return Ok((i, PrimaryExpression::Literal(val)));
        }
        if let Ok((i, val)) = Invocation::try_parse(text) {
            return Ok((i, PrimaryExpression::Invoke(Box::new(val))));
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

#[derive(Debug)]
struct Invocation<'a> {
    pub invoker: PrimaryExpression<'a>,
    pub args: Vec<PrimaryExpression<'a>>,
}

impl<'a> Invocation<'a> {
    #[cfg(test)]
    fn new(invoker: PrimaryExpression<'a>, args: Vec<PrimaryExpression<'a>>) -> Self {
        Self { invoker, args }
    }

    pub fn try_parse(text: &'a str) -> ParseResult<Invocation<'a>> {
        // To start, we need to identifiy the calling Expresion. Lets try:
        let mut parse_pointer = 0;
        let (delta, invoker) = Identifier::try_parse(text)?;

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
            let (delta, arg) = PrimaryExpression::try_parse(&text[parse_pointer..])?;
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
                panic!("This is unexpected");
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

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;
    use assert_matches::assert_matches;
    use rstest::rstest;

    #[rstest]
    #[case(
        r#"let    var = "Not a variable""#,
        vec![
            VariableAssignment {
                name:Identifier::new("var"),
                expr:PrimaryExpression::Literal(Literal::Text("Not a variable"))
            }
        ]
    )]
    #[case(
        r#"let    var = "Not a variable",
        var2 = 0xff"#,
        vec![
            VariableAssignment {
                name:Identifier::new("var"), 
                expr:PrimaryExpression::Literal(Literal::Text("Not a variable"))
            },
            VariableAssignment {
                name:Identifier::new("var2"), 
                expr:PrimaryExpression::Literal(Literal::Number(literal::NumberType::Int(0xff)))
            }
        ]
    )]
    fn test_let_expression_parser(#[case] input_text: &str, #[case] expr: Vec<VariableAssignment>) {
        let (_, let_expr) = LetExpression::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());
        assert_eq!(let_expr.variable_list.len(), expr.len());
        for (i, _actual) in let_expr.variable_list.iter().enumerate() {
            assert_matches!(&expr[i], _actual)
        }
    }

    #[rstest]
    #[case(
        r#"    var = "Not a variable""#,
        "var",
        PrimaryExpression::Literal(Literal::Text("Not a variable")),
        26
    )]
    #[case(
        r#"
var = "Not a variable""#,
        "var",
        PrimaryExpression::Literal(Literal::Text("Not a variable")),
        23
    )]
    #[case(
        r#"       var =          This("Not a variable")"#,
        "var",
        PrimaryExpression::Invoke(Box::new(Invocation::new(
            PrimaryExpression::Identifier(Identifier::new("This")),
            vec![PrimaryExpression::Literal(Literal::Text("Not a variable"))]
        ))),
        44
    )]
    fn test_let_assignment_parser(
        #[case] input_text: &str,
        #[case] name: &str,
        #[case] _expr: PrimaryExpression,
        #[case] delta: usize,
    ) {
        let (i, assignment) = VariableAssignment::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(assignment.name.text(), name);
        assert_eq!(delta, i);

        assert_matches!(assignment.expr, _expr)
    }

    #[rstest]
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
                PrimaryExpression::Literal(Literal::Text(v)) => assert_eq!(v, &vars[i]),
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
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Float(1234.5))),
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Int(0x25))),
        ],
    58) ]
    #[case(
        r#"This(" Not a 235.E10 variable", false, 1234.5, 0x25)"#, 
        "This", 
        vec![
            PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable")), 
            PrimaryExpression::Literal(Literal::Logical(false)),
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Float(1234.5))),
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Int(0x25))),
        ],
    52)
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
                PrimaryExpression::Identifier(ident) => {
                    assert_matches!(&vars[i], PrimaryExpression::Identifier(expected) => {
                        assert_eq!(ident.text(), expected.text())
                    })
                }
                PrimaryExpression::Invoke(_invoke) => todo!(),
                PrimaryExpression::Literal(_literal) => {
                    assert_matches!(&vars[i], PrimaryExpression::Literal(expected) => {
                        assert_matches!(expected, _literal)
                    })
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
}
