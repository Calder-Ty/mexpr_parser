mod identifier;
mod literal;

use self::{
    identifier::Identifier,
    literal::Literal,
    parse_utils::{skip_whitespace, ParseError, ParseResult},
};

pub(crate) enum ParserState<'a> {
    Let,
    VariableList,
    Variable,
    VariableName(identifier::Identifier<'a>),
}

mod parse_utils {
    use thiserror::Error;
    pub type ParseResult<T> = Result<(usize, T), Box<ParseError>>;

    #[derive(Debug, Error)]
    pub enum ParseError {
        #[error("Input is Invalid, Unable to proceed")]
        InvalidInput,
    }

    #[inline]
    pub(crate) fn skip_whitespace(text: &str) -> usize {
        text.char_indices()
            .take_while(|(_, c)| (*c).is_whitespace())
            .count()
    }
}

pub struct Parser<'state> {
    variables: Vec<&'state str>,
    parser_state: ParserState<'state>,
}

impl<'state> Default for Parser<'state> {
    fn default() -> Self {
        Self {
            variables: Vec::default(),
            parser_state: ParserState::Let,
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
impl<'state> Parser<'state> {
    pub fn parse(&mut self, text: &'state str) -> ParseResult<()> {
        // This takes us past the let statement
        // Skip the Variable List state, because we know where we are.
        let (i, ident) = Identifier::try_parse(text)?;
        // Skip let part of the statement
        // split on the = sign, now pass that in
        let var_txt = text[i..].splitn(2, '=').last().unwrap();
        // let supbarser = MExpresion::parse(var_txt);
        Ok((0, ()))
    }
}

#[derive(Debug)]
struct LetExpression<'a> {
    variable_list: Vec<VariableAssignment<'a>>,
}

impl<'a> LetExpression<'a> {
    fn try_parse(text: &'a str) -> parse_utils::ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        if !&text[parse_pointer..].starts_with("let ") {
            return Err(Box::new(ParseError::InvalidInput));
        }
        parse_pointer += 4; // skip 'let '

        let mut variable_list = vec![];
        loop {
            let (delta, assignment) = VariableAssignment::try_parse(&text[parse_pointer..])?;
            variable_list.push(assignment);
            parse_pointer += delta;
            parse_pointer += skip_whitespace(&text[parse_pointer..]);
            if text[parse_pointer..].chars().next().unwrap_or(',') != ',' {
                break;
            }
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
        let var_txt = text[parse_pointer..]
            .splitn(2, '=')
            .last()
            .expect("No `=` Found for Splitting!");

        let (delta, expr) = PrimaryExpression::try_parse(var_txt)?;
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
        if let Ok((i, val)) = Identifier::try_parse(text) {
            return Ok((i, PrimaryExpression::Identifier(val)));
        }
        if let Ok((i, val)) = Invocation::try_parse(text) {
            return Ok((i, PrimaryExpression::Invoke(Box::new(val))));
        }
        Err(ParseError::InvalidInput)
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
        let (i, mut invoker) = Identifier::try_parse(text)?;
        // For and invocation we expect that we can be in a call so lets try something here:
        let mut args = vec![];
        let arglist = &text[i..];
        // Skip the Calling Parenthesis
        let mut arglist_start = arglist
            .char_indices()
            .take_while(|(_, c)| *c != '(')
            .count()
            + 1; // Skip the opening '('
                 // Now we need to Parse the contents of the function invocation
        loop {
            let (delta, arg) = PrimaryExpression::try_parse(&arglist[arglist_start..])?;
            args.push(arg);
            arglist_start = arglist_start
                + delta
                + parse_utils::skip_whitespace(&arglist[arglist_start + delta..]);
            // If we come to the end of the text of the invocation, we want
            // to end
            if arglist[arglist_start..].chars().next().unwrap_or(')') == ')' {
                break;
            }
            if arglist[arglist_start..].chars().next().unwrap_or(',') != ',' {
                panic!("This is unexpected");
            }
            arglist_start += 1; // Skip the comma
        }

        Ok((
            arglist_start,
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
        r#"let    var = "Not a variable
        var2 = 0x25
        ""#,
        vec![
            VariableAssignment {
                name:Identifier::new("var"), 
                expr:PrimaryExpression::Literal(Literal::Text("Not a variable"))
            }
        ]
    )]
    fn test_let_expression_parser(
        #[case] input_text: &str,
        #[case] expr: Vec<VariableAssignment>,
    ) {
        let (_, let_expr) = LetExpression::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());
        for (i, _actual) in let_expr.variable_list.iter().enumerate() {
            assert_matches!(&expr[i], _actual)
        }
    }

    #[rstest]
    #[case(
        r#"    var = "Not a variable""#,
        "var",
        PrimaryExpression::Literal(Literal::Text("Not a variable"))
    )]
    #[case(
        r#"    var = This("Not a variable")"#,
        "var",
        PrimaryExpression::Invoke(Box::new(Invocation::new(
            PrimaryExpression::Identifier(Identifier::new("This")),
            vec![PrimaryExpression::Literal(Literal::Text("Not a variable"))]
        )))
    )]
    fn test_let_assignment_parser(
        #[case] input_text: &str,
        #[case] name: &str,
        #[case] _expr: PrimaryExpression,
    ) {
        let (_, assignment) = VariableAssignment::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        assert_eq!(assignment.name.text(), name);

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
        )]) ]
    #[case(
        r#"This(" Not a 235.E10 variable"  ,false  , 1234.5 , 0x25)"#, 
        "This", 
        vec![
            PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable")), 
            PrimaryExpression::Literal(Literal::Logical(false)),
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Float(1234.5))),
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Int(0x25))),
        ]) ]
    #[case(
        r#"This(" Not a 235.E10 variable", false, 1234.5, 0x25)"#, 
        "This", 
        vec![
            PrimaryExpression::Literal(Literal::Text(" Not a 235.E10 variable")), 
            PrimaryExpression::Literal(Literal::Logical(false)),
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Float(1234.5))),
            PrimaryExpression::Literal(Literal::Number(literal::NumberType::Int(0x25))),
        ])]
    fn test_invokation_parser_mixed(
        #[case] input_text: &str,
        #[case] ident: &str,
        #[case] vars: Vec<PrimaryExpression>,
    ) {
        let (_, invokation) = Invocation::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        if let PrimaryExpression::Identifier(invoker) = invokation.invoker {
            assert_eq!(invoker.text(), ident)
        }

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
}
