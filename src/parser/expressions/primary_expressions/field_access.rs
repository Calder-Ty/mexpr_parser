use serde::Serialize;

use crate::{
    parser::{
        core::TryParse,
        identifier::Identifier,
        operators,
        parse_utils::{gen_error_ctx, next_char, skip_whitespace_and_comments, ParseResult},
    },
    ParseError, ERR_CONTEXT_SIZE,
};

use super::PrimaryExpression;

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct FieldAccess<'a> {
    // The Grammar posted by Microsoft for Field Access Expressions has it start with
    // a Primary Expression. This is required by the spec, but in practice
    // it doesn't always have to be there. (eg, each statement).
    // https://learn.microsoft.com/en-us/powerquery-m/m-spec-functions#simplified-declarations
    expr: Option<PrimaryExpression<'a>>,
    selector: Identifier<'a>,
}

impl<'a> FieldAccess<'a> {
    #[cfg(test)]
    pub(crate) fn new(expr: Option<PrimaryExpression<'a>>, selector: Identifier<'a>) -> Self {
        Self { expr, selector }
    }
}

impl<'a> TryParse<'a, Self> for FieldAccess<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace_and_comments(text);

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

        let primary_end = if let Some(v) = find_next_bracket_on_syntax_level(&text[parse_pointer..])
        {
            v
        } else {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        let (delta, expr) =
            match PrimaryExpression::try_parse(&text[parse_pointer..parse_pointer + primary_end]) {
                Ok((i, v)) => (i, Some(v)),
                Err(_) => (0, None),
            };

        parse_pointer += delta;

        if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::OPEN_BRACKET {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };
        parse_pointer += 1; // Advance past the `[`

        let (delta, selector) = Identifier::try_parse_generalized(&text[parse_pointer..])?;

        parse_pointer += delta; // Advance past the `]`
        parse_pointer += skip_whitespace_and_comments(&text[parse_pointer..]);

        if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::CLOSE_BRACKET {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        parse_pointer += 1;

        Ok((parse_pointer, Self { expr, selector }))
    }
}

fn find_next_bracket_on_syntax_level(text: &str) -> Option<usize> {
    let mut level = 0;
    for (i, c) in text.char_indices() {
        // If we hit our target on our level, return
        match c {
            operators::OPEN_BRACKET if level == 0 => return Some(i),
            operators::OPEN_BRACE | operators::OPEN_PAREN => level += 1,
            operators::CLOSE_BRACE | operators::CLOSE_PAREN => level -= 1,
            _ => (),
        };
        if level < 0 {
            return None;
        };
    }
    // We've reached the end of the rope here.
    None
}

#[cfg(test)]
mod tests {
    use std::assert_eq;

    use super::*;
    use crate::parser::identifier::Identifier;
    use rstest::rstest;

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
    #[case("[]", Some(0))]
    #[case("([()])", None)]
    #[case("([()])[]", Some(6))]
    fn test_find_next_bracket_on_syntax_level(
        #[case] input_text: &str,
        #[case] expected: Option<usize>,
    ) {
        let actual = find_next_bracket_on_syntax_level(input_text);
        assert_eq!(expected, actual);
    }
}
