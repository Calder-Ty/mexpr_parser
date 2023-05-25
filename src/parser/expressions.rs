mod primary_expressions;
use crate::ParseError;
use primary_expressions::PrimaryExpression;

use super::{
    identifier::Identifier,
    parse_utils::{self, gen_error_ctx, skip_whitespace, ParseResult},
};

const PRIMITIVE_TYPES: [&str; 18] = [
    "any",
    "anynonnull",
    "binary",
    "date",
    "datetime",
    "datetimezone",
    "duration",
    "function",
    "list",
    "logical",
    "none",
    "null",
    "number",
    "record",
    "table",
    "text",
    "time",
    "type",
];

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
        let let_sep = &text[parse_pointer..]
            .chars()
            .skip(3)
            .next()
            .unwrap_or('_')
            .is_whitespace();
        if !(text[parse_pointer..].starts_with("let") && *let_sep) {
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

pub(crate) struct TypeExpression<'a> {
    text: &'a str,
}

impl<'a> TypeExpression<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        let start = parse_pointer;
        let followed_by_space = &text[parse_pointer..]
            .chars()
            .skip(4)
            .next()
            .unwrap_or('_')
            .is_whitespace();

        if !(text[parse_pointer..].starts_with("type") && *followed_by_space) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        }

        parse_pointer += 4; // length of the word "type"
        parse_pointer += skip_whitespace(&text[parse_pointer..]); // length of the word "type"

        // for now only supporting the 'primitive type' expression
        let delta_type = &text[parse_pointer..]
            .chars()
            .take_while(|c| !(*c).is_whitespace())
            .count();
        if PRIMITIVE_TYPES.contains(&&text[parse_pointer..parse_pointer + delta_type]) {
            parse_pointer += delta_type;
            return Ok((
                parse_pointer,
                Self {
                    text: &text[start..parse_pointer],
                },
            ));
        }
        return Err(Box::new(ParseError::InvalidInput {
            pointer: parse_pointer,
            ctx: gen_error_ctx(text, parse_pointer, 5),
        }));
    }
}

#[cfg(test)]
mod tests {

    use std::assert_eq;

    use super::*;
    use crate::parser::{
        identifier::Identifier,
        literal::{Literal, NumberType},
    };
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
            expr:PrimaryExpression::Literal(Literal::Number(NumberType::Int(0xff)))
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
    PrimaryExpression::Invoke(Box::new(primary_expressions::Invocation::new(
        PrimaryExpression::Identifier(Identifier::new("This")),
        vec![PrimaryExpression::Literal(Literal::Text("Not a variable"))]
    ))),
    44
)]
    #[case(
    r#"       #"var" =          This.that("Not a variable")"#,
    "var",
    PrimaryExpression::Invoke(Box::new(primary_expressions::Invocation::new(
        PrimaryExpression::Identifier(Identifier::new("This.that")),
        vec![PrimaryExpression::Literal(Literal::Text("Not a variable"))]
    ))),
    52
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
    #[case("    type null", "type null", 13)]
    #[case("    type datetime  ", "type datetime", 17)]
    fn test_type_expr_parser(
        #[case] input_text: &str,
        #[case] name: &str,
        #[case] exp_delta: usize,
    ) {

        let (delta, res) = TypeExpression::try_parse(input_text).expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(name, res.text);
        assert_eq!(exp_delta, delta);

    }
}
