//! Function Expression
//!
//! https://learn.microsoft.com/en-us/powerquery-m/m-spec-consolidated-grammar#function-expression

use serde::Serialize;

use crate::parser::core::TryParse;
use crate::parser::identifier::Identifier;
use crate::parser::parse_utils::{
    followed_by_valid_seperator, followed_by_whitespace, gen_error_ctx, next_char, skip_whitespace,
    ParseResult,
};
use crate::ParseError;

use super::{Expression, type_expressions::PRIMITIVE_TYPES};

/// function-expression:
/// `(` parameter-listopt `)` return-type[opt] `=>` function-body
/// function-body:
///     expression
/// parameter-list:
///     fixed-parameter-list
///     fixed-parameter-list , optional-parameter-list
///     optional-parameter-list
/// fixed-parameter-list:
///     parameter
///     parameter , fixed-parameter-list
/// parameter:
///     parameter-name parameter-type[opt]
/// parameter-name:
///     identifier
/// parameter-type:
///     assertion
/// return-type:
///     assertion
/// assertion:
///     `as` nullable-primitive-type
/// optional-parameter-list:
///     optional-parameter
///     optional-parameter `,` optional-parameter-list
/// optional-parameter:
///     `optional` parameter
#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct FunctionExpression<'a> {
    parameters: FunctionParameters<'a>,
    return_type: Option<Assertion<'a>>,
    body: Expression<'a>,
}

impl<'a> FunctionExpression<'a> {
    #[cfg(test)]
    pub(crate) fn new(
        parameters: FunctionParameters<'a>,
        return_type: Option<Assertion<'a>>,
        body: Expression<'a>,
    ) -> Self {
        Self {
            parameters,
            return_type,
            body,
        }
    }
}

impl<'a> TryParse<'a> for FunctionExpression<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut parse_pointer = skip_whitespace(text);

        // Must start with open `(`
        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == '(') {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        };
        parse_pointer += 1; // Skip `(`
        let (delta, parameters) = FunctionParameters::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        // Close Params with `)`
        if !(next_char(&text[parse_pointer..]).unwrap_or(' ') == ')') {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        }
        parse_pointer += 1; // Skip `)`

        let (delta, return_type) = match Assertion::try_parse(&text[parse_pointer..]) {
            Ok((i, v)) => (i, Some(v)),
            Err(_) => (0, None),
        };

        parse_pointer += delta;
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        // Go to the body
        if !(text[parse_pointer..].starts_with("=>")
            && followed_by_whitespace(&text[parse_pointer..], 2))
        {
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        }

        parse_pointer += 2; // Skip `=>`

        let (delta, body) = Expression::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((
            parse_pointer,
            Self {
                parameters,
                return_type,
                body,
            },
        ))
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct FunctionParameters<'a> {
    fixed: Vec<FuncParameter<'a>>,
    optional: Vec<FuncParameter<'a>>,
}

impl<'a> FunctionParameters<'a> {
    #[cfg(test)]
    pub(crate) fn new(fixed: Vec<FuncParameter<'a>>, optional: Vec<FuncParameter<'a>>) -> Self {
        Self { fixed, optional }
    }
}

impl<'a> TryParse<'a> for FunctionParameters<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let mut fixed = vec![];
        let mut optional = vec![];

        let mut parse_pointer = skip_whitespace(text);
        // First fixed
        loop {
            match FuncParameter::try_parse(&text[parse_pointer..]) {
                Ok((delta, param)) => {
                    parse_pointer += delta;
                    fixed.push(param);
                }
                Err(_) => break, // That's OK, we don't need fixed params
            };

            // Lookahead for ,
            let lookahead_pointer = skip_whitespace(&text[parse_pointer..]);
            if text[parse_pointer..].chars().next().unwrap_or(' ') != ',' {
                // No comma, means there are no more parameters
                break;
            }
            parse_pointer += lookahead_pointer + 1 // Plus one for the comma
        }

        // Then optional
        loop {
            parse_pointer += skip_whitespace(&text[parse_pointer..]);
            // Check for optional keyword
            if !(text[parse_pointer..].starts_with("optional")
                && followed_by_whitespace(&text[parse_pointer..], 8))
            {
                break; // No more optional parameters
            };
            parse_pointer += 8;

            let (delta, param) = FuncParameter::try_parse(&text[parse_pointer..])?;
            parse_pointer += delta;
            optional.push(param);
            // Lookahead for ,
            let lookahead_pointer = skip_whitespace(&text[parse_pointer..]);
            if text[parse_pointer..].chars().next().unwrap_or(' ') != ',' {
                // No comma, means there are no more parameters
                break;
            }
            parse_pointer += lookahead_pointer + 1 // Plus one for the comma
        }

        Ok((parse_pointer, Self { fixed, optional }))
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct FuncParameter<'a> {
    name: Identifier<'a>,
    param_type: Option<Assertion<'a>>,
}

impl<'a> FuncParameter<'a> {
    #[cfg(test)]
    pub(crate) fn new(name: Identifier<'a>, param_type: Option<Assertion<'a>>) -> Self {
        Self { name, param_type }
    }
}

impl<'a> TryParse<'a> for FuncParameter<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);
        let (delta, ident) = Identifier::try_parse(&text[parse_pointer..])?;

        parse_pointer += delta;

        let lookahead_pointer = parse_pointer + skip_whitespace(&text[parse_pointer..]);
        let next_val = text[lookahead_pointer..].chars().next().unwrap_or(',');
        if [',', ')'].contains(&next_val) {
            return Ok((
                parse_pointer,
                Self {
                    name: ident,
                    param_type: None,
                },
            ));
        };

        let (delta, param_type) = Assertion::try_parse(&text[parse_pointer..])?;
        parse_pointer += delta;

        Ok((
            parse_pointer,
            Self {
                name: ident,
                param_type: Some(param_type),
            },
        ))
    }
}

#[derive(Debug, PartialEq, Serialize)]
pub(crate) struct Assertion<'a> {
    value: &'a str,
}

impl<'a> Assertion<'a> {
    #[cfg(test)]
    pub(crate) fn new(value: &'a str) -> Self {
        Self { value }
    }
}

impl<'a> TryParse<'a> for Assertion<'a> {
    fn try_parse(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = skip_whitespace(text);

        if !(text[parse_pointer..].starts_with("as")
            && followed_by_whitespace(&text[parse_pointer..], 2))
        {
            // TODO: Add Constant for Parse Pointer context size
            return Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }));
        };

        parse_pointer += 2; // skip `as`
        parse_pointer += skip_whitespace(&text[parse_pointer..]);

        // nullable-primitive-type allows the text "nullable" to appear
        if (text[parse_pointer..].starts_with("nullable")
            && followed_by_whitespace(&text[parse_pointer..], 8))
        {
            parse_pointer += 8;
            parse_pointer += skip_whitespace(&text[parse_pointer..])
        };

        let mut value = None;
        for type_name in PRIMITIVE_TYPES {
            if text[parse_pointer..].starts_with(type_name)
                && followed_by_valid_seperator(&text[parse_pointer..], type_name.len())
            {
                parse_pointer += type_name.len();
                value = Some(type_name);
                break;
            };
        }

        if let Some(val) = value {
            Ok((parse_pointer, Self { value: val }))
        } else {
            Err(Box::new(ParseError::InvalidInput {
                pointer: parse_pointer,
                ctx: gen_error_ctx(text, parse_pointer, 5),
            }))
        }
    }
}

#[cfg(test)]
mod tests {

    use std::{assert_eq, vec};

    use crate::parser::expressions::primary_expressions::{Invocation, PrimaryExpression};

    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case(
        "as nullable time, more stuff",
        16,

        Assertion {
            value: "time"
        })]
    fn parse_assertion(#[case] input: &str, #[case] exp_delta: usize, #[case] expected: Assertion) {
        let (delta, res) = Assertion::try_parse(input).expect("Unable to parse input");

        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case(
        "   thing as nullable time, more stuff",
        25,
        FuncParameter {
            name: Identifier::new("thing"), 
            param_type: Some( Assertion { value: "time" }) 
        }
    )]
    fn parse_func_parameter(
        #[case] input: &str,
        #[case] exp_delta: usize,
        #[case] expected: FuncParameter,
    ) {
        let (delta, res) = FuncParameter::try_parse(input).expect("Unable to parse input");

        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case(
        "  thing, baz)",
        12,
        FunctionParameters {
            fixed: vec![ FuncParameter {
            name: Identifier::new("thing"),
            param_type: None
            },
                FuncParameter {
                    name:Identifier::new("baz"),
                    param_type: None
                }
            ],
            optional: vec![]

        }
    )]
    #[case(
        "  thing as nullable time, optional baz)",
        38,
        FunctionParameters {
            fixed: vec![ FuncParameter {
            name: Identifier::new("thing"), 
            param_type: Some( Assertion { value: "time" })
            } ],
            optional: vec![ FuncParameter {name:Identifier::new("baz"), param_type: None}]

        }
    )]
    #[case(
        "  optional foo, optional baz)",
        28,
        FunctionParameters {
            fixed: vec![  ],
            optional: vec![FuncParameter {
            name: Identifier::new("foo"), 
            param_type: None
            }, FuncParameter {name:Identifier::new("baz"), param_type: None}]

        }
    )]
    #[case(
        ")",
        0,
        FunctionParameters {
            fixed: vec![],
            optional: vec![]

        }
    )]
    fn parse_func_parameters(
        #[case] input: &str,
        #[case] exp_delta: usize,
        #[case] expected: FunctionParameters,
    ) {
        let (delta, res) = FunctionParameters::try_parse(input).expect("Unable to parse input");

        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }

    #[rstest]
    #[case(
        "(  optional foo, optional baz ) => func.call()",
        46,
        FunctionExpression {
            parameters: FunctionParameters {
            fixed: vec![  ],
                optional: vec![FuncParameter {
                    name: Identifier::new("foo"), 
                    param_type: None
                }, FuncParameter {name:Identifier::new("baz"), param_type: None}
                ]

        },
            return_type: None,
            body: Expression::Primary(
                PrimaryExpression::Invoke(
                    Box::new(
                        Invocation::new(
                            PrimaryExpression::Identifier(Identifier::new("func.call")),
                            vec![]
                        )
                    )
                )
            ),
        }
    )]
    #[case(
        "() => func.call()",
        17,
        FunctionExpression {
            parameters: FunctionParameters {
                fixed: vec![],
                optional: vec![]
            },
            return_type: None,
            body: Expression::Primary(
                PrimaryExpression::Invoke(
                    Box::new(
                        Invocation::new(
                            PrimaryExpression::Identifier(Identifier::new("func.call")),
                            vec![]
                        )
                    )
                )
            ),
        }
    )]
    fn parse_func_expression(
        #[case] input: &str,
        #[case] exp_delta: usize,
        #[case] expected: FunctionExpression,
    ) {
        let (delta, res) = FunctionExpression::try_parse(input).expect("Unable to parse input");

        assert_eq!(expected, res);
        assert_eq!(exp_delta, delta);
    }
}
