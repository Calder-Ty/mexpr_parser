use std::{vec, marker::PhantomData};

use serde::Serialize;

use crate::{
    parser::{
        core::TryParse,
        identifier::Identifier,
        operators,
        parse_utils::{
            followed_by_whitespace, gen_error_ctx, next_char,
            skip_whitespace, ParseResult,
        }, keywords,
    },
    ParseError, ERR_CONTEXT_SIZE,
};

use super::primary_expressions::PrimaryExpression;

pub(crate) const PRIMITIVE_TYPES: [&str; 18] = [
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

/// Type Expression is different from Type
/// Per the spec, a TypeExpression is either a primary expression,
/// or a primary-type, preceded by `type` literally.
///
/// A Type is either a PrimaryExpression or a PrimaryType.
#[derive(Debug, PartialEq, Serialize)]
pub(crate) enum TypeExpression<'a> {
    PrimaryType(PrimaryType<'a>),
    Primary(PrimaryExpression<'a>),
}

impl<'a> TryParse<'a, Self> for TypeExpression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        if text[parse_pointer..].starts_with(keywords::TYPE)
            && followed_by_whitespace(&text[parse_pointer..], keywords::TYPE.len())
        {
            parse_pointer += 4;
            let (delta, val) = PrimaryType::try_parse(&text[parse_pointer..])?;
            Ok((parse_pointer + delta, TypeExpression::PrimaryType(val)))
        } else {
            let (delta, val) = PrimaryExpression::try_parse(&text[parse_pointer..])?;
            Ok((parse_pointer + delta, TypeExpression::Primary(val)))
        }
    }
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum Type<'a> {
    PrimaryType(PrimaryType<'a>),
    Primary(PrimaryExpression<'a>),
}

impl<'a> Type<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        if let Ok((i, val)) = PrimaryType::try_parse(text) {
            return Ok((i, Type::PrimaryType(val)));
        }

        let (i, val) = PrimaryExpression::try_parse(text)?;
        Ok((i, Type::Primary(val)))
    }
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum PrimaryType<'a> {
    PrimitiveType(PrimitiveType<'a>),
    TableType(TableType<'a>),
    Nullable(Box<Type<'a>>),
}

impl<'a> PrimaryType<'a> {
    /// For nullable-primitive type
    /// nullable [opt] primitive type
    pub(crate) fn try_parse_primitive(text: &'a str) -> ParseResult<Self>{
        let (delta, val) = PrimaryType::try_parse(text)?;
        match &val {
            PrimaryType::Nullable(inner) => {
                if matches!(inner.as_ref(), Type::PrimaryType(PrimaryType::PrimitiveType(_))) {
                    Ok((delta, val))
                } else {
                    Err(Box::new(ParseError::InvalidInput { pointer: 0, ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE) }))
                }
            },
            PrimaryType::PrimitiveType(_) => { Ok((delta, val)) },
            _ => Err(Box::new(ParseError::InvalidInput { pointer: 0, ctx: gen_error_ctx(text, 0, ERR_CONTEXT_SIZE) })),
        }
    }

}
impl<'a> PrimaryType<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        let parse_pointer = skip_whitespace(text);

        if let Ok((i, v)) = Nullable::try_parse(&text[parse_pointer..]) {
            return Ok((parse_pointer + i, PrimaryType::Nullable(Box::new(v))));
        }
        if let Ok((i, v)) = TableType::try_parse(&text[parse_pointer..]) {
            return Ok((parse_pointer + i, PrimaryType::TableType(v)));
        }
        // for now only supporting the 'primitive type' expression
        if let Ok((i, v)) = PrimitiveType::try_parse(&text[parse_pointer..]) {
            return Ok((parse_pointer + i, PrimaryType::PrimitiveType(v)));
        }
        Err(Box::new(ParseError::InvalidInput {
            pointer: parse_pointer,
            ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
        }))
    }
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct PrimitiveType<'a> {
    text: &'a str,
}

impl<'a> PrimitiveType<'a> {
    #[cfg(test)]
    pub(crate) fn new(text: &'a str) -> Self {
        Self { text }
    }
}

impl<'a> TryParse<'a, Self> for PrimitiveType<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);
        let start = parse_pointer;
        let delta_type = &text[parse_pointer..]
            .chars()
            .take_while(|c| (*c).is_ascii_alphabetic())
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
        Err(Box::new(ParseError::InvalidInput {
            pointer: parse_pointer,
            ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
        }))
    }
}

#[derive(Debug, Serialize, PartialEq)]
struct Nullable { }

impl Nullable {
}

impl<'a>  TryParse<'a, Type<'a>> for Nullable {

    fn try_parse(text: &'a str) -> ParseResult<Type<'a>>
        where
            Self: Sized {
        let mut parse_pointer = skip_whitespace(text);
        if !(text[parse_pointer..].starts_with("nullable") && followed_by_whitespace(&text[parse_pointer..], 8)) {
            return Err(
                Box::new(ParseError::InvalidInput { 
                    pointer: parse_pointer, 
                    ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE) 
                }
            ));
        };
        parse_pointer += 8;

        let (delta, type_) = Type::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;
        return Ok((parse_pointer, type_));
    }

}



#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct TableType<'a> {
    row_spec: Vec<FieldSpecification<'a>>,
}

impl<'a> TryParse<'a, Self> for TableType<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        if !(text[parse_pointer..].starts_with("table")
           && followed_by_whitespace(&text[parse_pointer..], 5))
        {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        };

        parse_pointer += 5;
        let (delta, row_spec) = Vec::<FieldSpecification>::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((parse_pointer, Self { row_spec } ))
    }
}


impl<'a> TryParse<'a, Vec<FieldSpecification<'a>>> for Vec<FieldSpecification<'a>> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::OPEN_BRACKET {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }

        parse_pointer += 1; // skip the `[`
        let mut row_spec = vec![];

        loop {
            let (delta, val) = FieldSpecification::try_parse(&text[parse_pointer..])?;
            parse_pointer += delta;
            parse_pointer += skip_whitespace(&text[parse_pointer..]);
            row_spec.push(val);

            if next_char(&text[parse_pointer..]).unwrap_or(' ') == operators::CLOSE_BRACKET {
                parse_pointer += 1; // skip the `]`
                break;
            };

            if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::COMMA {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
            }
            parse_pointer += 1; //  Skip the `,`
        };

        Ok((parse_pointer, row_spec))
    }
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) struct FieldSpecification<'a> {
    name: Identifier<'a>,
    spec: Type<'a>,
}

impl<'a> TryParse<'a, Self> for FieldSpecification<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);
        let (delta, name) = Identifier::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        if next_char(&text[parse_pointer..]).unwrap_or(' ') != operators::EQUAL {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
            }));
        }
        parse_pointer += 1; // Skip `=`

        let (delta, spec) = Type::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        Ok((parse_pointer, Self { name, spec }))
    }
}

#[cfg(test)]
mod tests {

    use std::assert_eq;

    use super::*;
    use rstest::rstest;

    #[rstest]

    #[case("    type nullable text ", 22,
        TypeExpression::PrimaryType(
            PrimaryType::Nullable(
                Box::new(
                    Type::PrimaryType(PrimaryType::PrimitiveType( PrimitiveType {  text: "text"}))
                )
            )
        )
    )]
    #[case("    type null", 13, TypeExpression::PrimaryType(PrimaryType::PrimitiveType(PrimitiveType {  text: "null"})))]
    #[case("    type datetime  ", 17, TypeExpression::PrimaryType( PrimaryType::PrimitiveType(PrimitiveType {  text: "datetime"})))]
    fn test_type_expression(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] expected: TypeExpression,
    ) {
        let (delta, res) = TypeExpression::try_parse(input_text)
            .expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case("     null", 9, PrimaryType::PrimitiveType(PrimitiveType {  text: "null"}))]
    #[case("    datetime  ", 12, PrimaryType::PrimitiveType(PrimitiveType {  text: "datetime"}))]
    fn test_primary_type(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] expected: PrimaryType,
    ) {
        let (delta, res) = PrimaryType::try_parse(input_text)
            .expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case("    null", "null", 8)]
    #[case("    datetime  ", "datetime", 12)]
    fn test_primitive_type(#[case] input_text: &str, #[case] name: &str, #[case] exp_delta: usize) {
        let (delta, res) = PrimitiveType::try_parse(input_text)
            .expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(name, res.text);
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case("  ident = null", 14, FieldSpecification {
        name: Identifier::new("ident"),
        spec: Type::PrimaryType(PrimaryType::PrimitiveType(PrimitiveType { text: "null" }))
    })]
    fn test_field_specification(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] expected: FieldSpecification,
    ) {
        let (delta, res) = FieldSpecification::try_parse(input_text)
            .expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }


    #[rstest]
    #[case("  [ ident = null, val = date ]", 30, vec![FieldSpecification {
        name: Identifier::new("ident"),
        spec: Type::PrimaryType(PrimaryType::PrimitiveType(PrimitiveType { text: "null" }))
    }, 
        FieldSpecification {
        name: Identifier::new("val"),
        spec: Type::PrimaryType(PrimaryType::PrimitiveType(PrimitiveType { text: "date" }))
    }
    ])]
    #[case("  [ ident = null ]", 18, vec![FieldSpecification {
        name: Identifier::new("ident"),
        spec: Type::PrimaryType(PrimaryType::PrimitiveType(PrimitiveType { text: "null" }))
    }])]
    fn test_field_specification_list(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] expected: Vec<FieldSpecification>,
    ) {
        let (delta, res) = Vec::<FieldSpecification>::try_parse(input_text)
            .expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }




    #[rstest]
    #[case(r#"table [#"Submission Type" = _t, Identifyer = _t]"#,
        48,
        TableType {
            row_spec:
        vec![FieldSpecification {
        name: Identifier::new("Submission Type"),
        spec: Type::Primary(PrimaryExpression::Identifier(Identifier::new( "_t" ))),
    }, 
        FieldSpecification {
        name: Identifier::new("Identifyer"),
        spec: Type::Primary(PrimaryExpression::Identifier(Identifier::new( "_t" ))),
    }
    ]})]
    fn test_table_type(
        #[case] input_text: &str,
        #[case] exp_delta: usize,
        #[case] expected: TableType,
    ) {
        let (delta, res) = TableType::try_parse(input_text)
            .expect(format!("Couldn't parse input, {0}", input_text).as_str());
        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }
}
