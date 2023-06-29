mod each;
mod function;
mod logical;
mod primary_expressions;
mod record;
mod type_expressions;

use self::{each::EachExpression, logical::EqualityExpression};

use super::{
    core::TryParse,
    identifier::Identifier,
    keywords, operators,
    parse_utils::{self, gen_error_ctx, skip_whitespace, ParseResult},
};
use crate::{ParseError, ERR_CONTEXT_SIZE};
use primary_expressions::PrimaryExpression;
use serde::Serialize;

#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum Expression<'a> {
    Let(LetExpression<'a>),
    Primary(PrimaryExpression<'a>),
    Logical(EqualityExpression<'a>),
    Each(Box<EachExpression<'a>>),
}

impl<'a> Expression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self> {
        if let Ok((i, val)) = LetExpression::try_parse(text) {
            return Ok((i, Expression::Let(val)));
        }
        if let Ok((i, val)) = PrimaryExpression::try_parse(text) {
            return Ok((i, Expression::Primary(val)));
        }
        if let Ok((i, val)) = EachExpression::try_parse(text) {
            return Ok((i, Expression::Each(Box::new(val))));
        }
        if let Ok((i, val)) = EqualityExpression::try_parse(text) {
            return Ok((i, Expression::Logical(val)));
        }
        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        }))
    }

    fn try_parse_with_lookahead<F>(text: &'a str, lookahead_func: F) -> ParseResult<Self>
    where
        F: Fn(&'a str) -> bool,
    {
        if let Ok((i, val)) = LetExpression::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, Expression::Let(val)));
            }
        }
        if let Ok((i, val)) = PrimaryExpression::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, Expression::Primary(val)));
            }
        }
        if let Ok((i, val)) = EachExpression::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, Expression::Each(Box::new(val))));
            }
        }
        if let Ok((i, val)) = EqualityExpression::try_parse(text) {
            if lookahead_func(&text[i..]) {
                return Ok((i, Expression::Logical(val)));
            }
        }
        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        }))
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
#[derive(Debug, Serialize, PartialEq)]
pub struct LetExpression<'a> {
    variable_list: Vec<VariableAssignment<'a>>,
}

impl<'a> LetExpression<'a> {
    pub fn try_parse(text: &'a str) -> parse_utils::ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        let let_sep = &text[parse_pointer..]
            .chars()
            .nth(keywords::LET.len())
            .unwrap_or('_')
            .is_whitespace();
        if !(text[parse_pointer..].starts_with(keywords::LET) && *let_sep) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }
        parse_pointer += keywords::LET.len() + 1; // skip 'let '

        let mut variable_list = vec![];
        loop {
            let (delta, assignment) = VariableAssignment::try_parse(&text[parse_pointer..])?;
            variable_list.push(assignment);
            parse_pointer += delta;
            parse_pointer += skip_whitespace(&text[parse_pointer..]);
            if text[parse_pointer..].chars().next().unwrap_or(' ') != ',' {
                break;
            }
            parse_pointer += operators::COMMA_STR.len();
        }

        // Now for the In part
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        let in_sep = &text[parse_pointer..]
            .chars()
            .nth(keywords::IN.len())
            .unwrap_or('_')
            .is_whitespace();
        if !(text[parse_pointer..].starts_with(keywords::IN) && *in_sep) {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }
        parse_pointer += keywords::IN.len() + 1; // Skip 'in '
                            // I Don't care about the In expression right now
        let (delta, _) = Expression::try_parse(&text[parse_pointer..])?;

        Ok((parse_pointer + delta, Self { variable_list }))
    }
}

#[derive(Debug, Serialize, PartialEq)]
struct VariableAssignment<'a> {
    name: Identifier<'a>,
    expr: Expression<'a>,
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

        let (delta, expr) =
            Expression::try_parse_with_lookahead(&text[parse_pointer..], var_assignment_lookahead)?;
        parse_pointer += delta;

        Ok((parse_pointer, Self { name, expr }))
    }
}

/// Makes sure that the value given back is a FULL assignment value
fn var_assignment_lookahead(text: &str) -> bool {
    let lookahead_pointer = skip_whitespace(text);

    text[lookahead_pointer..].starts_with(operators::COMMA_STR)
        || text[lookahead_pointer..].starts_with(keywords::IN)
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
    r#"let    var = "Not a variable" in stuff"#,
38,
    vec![
        VariableAssignment {
            name:Identifier::new("var"),
            expr:Expression::Primary( PrimaryExpression::Literal(Literal::Text("Not a variable")))
        }
    ]
)]
    #[case(
    r#"let    var = "Not a variable",
    var2 = 0xff
    in stuff"#,
        59,
    vec![
        VariableAssignment {
            name:Identifier::new("var"), 
            expr:Expression::Primary( PrimaryExpression::Literal(Literal::Text("Not a variable")))
        },
        VariableAssignment {
            name:Identifier::new("var2"), 
            expr:Expression::Primary( PrimaryExpression::Literal(Literal::Number(NumberType::Int(0xff))))
        }
    ]
)]
    fn test_let_expression_parser(
        #[case] input_text: &str,
        #[case] expected_delta: usize,
        #[case] expr: Vec<VariableAssignment>,
    ) {
        let (delta, let_expr) = LetExpression::try_parse(input_text)
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());
        assert_eq!(expected_delta, delta);
        assert_eq!(let_expr.variable_list.len(), expr.len());
        for (i, _actual) in let_expr.variable_list.iter().enumerate() {
            assert_matches!(&expr[i], _actual)
        }
    }

    #[rstest]
    #[case(
        r#"    var = "Not a variable" in thing"#,
        "var",
        PrimaryExpression::Literal(Literal::Text("Not a variable")),
        26
    )]
    #[case(
        r#"
var = "Not a variable" in thing"#,
        "var",
        PrimaryExpression::Literal(Literal::Text("Not a variable")),
        23
    )]
    #[case(
    r#"       var =          This("Not a variable") in thing"#,
    "var",
    PrimaryExpression::Invoke(Box::new(primary_expressions::Invocation::new(
        PrimaryExpression::Identifier(Identifier::new("This")),
        vec![Expression::Primary(PrimaryExpression::Literal(Literal::Text("Not a variable")))]
    ))),
    44
)]
    #[case(
    r#"       #"var" =          This.that("Not a variable") in thing"#,
    "var",
    PrimaryExpression::Invoke(Box::new(primary_expressions::Invocation::new(
        PrimaryExpression::Identifier(Identifier::new("This.that")),
        vec![Expression::Primary(PrimaryExpression::Literal(Literal::Text("Not a variable")))]
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
}
