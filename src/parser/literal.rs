use crate::ERR_CONTEXT_SIZE;

use super::{
    keywords,
    parse_utils::{self, followed_by_valid_seperator, ParseError, ParseResult},
};
use serde::Serialize;

/// Literal:
///     LogicalLiteral
///     NumberLiteral
///     TextLiteral
///     NullLiteral
///     VerbatimLiteral
#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum Literal<'a> {
    Logical(bool),
    Text(&'a str),
    Number(NumberType),
    Null,
    Verbatim(&'a str),
}

#[derive(Debug, Serialize, PartialEq)]
pub(crate) enum NumberType {
    Int(isize),
    Float(f64),
}

impl<'a> Literal<'a> {
    pub fn try_parse(text: &'a str) -> ParseResult<Self> {
        // First Try Logical
        if let Ok(val) = Self::try_parse_logical(text) {
            return Ok(val);
        };

        if let Ok(val) = Self::try_parse_null(text) {
            return Ok(val);
        }

        if let Ok(val) = Self::try_parse_verbatim_literal(text) {
            return Ok(val);
        };

        if let Ok(val) = Self::try_parse_text(text) {
            return Ok(val);
        };

        if let Ok(val) = Self::try_parse_number(text) {
            return Ok(val);
        };

        Err(Box::new(ParseError::InvalidInput {
            pointer: 0,
            ctx: parse_utils::gen_error_ctx(text, 0, ERR_CONTEXT_SIZE),
        }))
    }

    fn try_parse_logical(text: &str) -> ParseResult<Self> {
        // true?
        let text_start = parse_utils::skip_whitespace(text);
        if text[text_start..].starts_with("true") {
            return Ok((text_start + 4, Self::Logical(true)));
        }
        if text[text_start..].starts_with("false") {
            return Ok((text_start + 5, Self::Logical(false)));
        }
        Err(Box::new(ParseError::InvalidInput {
            pointer: text_start,
            ctx: parse_utils::gen_error_ctx(text, text_start, ERR_CONTEXT_SIZE),
        }))
    }

    pub(crate) fn try_parse_text(text: &'a str) -> ParseResult<Self> {
        // is there the initial `"`?
        let mut text_start = parse_utils::skip_whitespace(text);
        if text.chars().nth(text_start).unwrap_or(' ') == '"' {
            // Find the terminal `"`? Remember Escapes!
            text_start += 1;
            let mut in_escape = false;
            let mut skip = false;
            let mut final_i = text_start;
            for (i, c) in text[text_start..].char_indices() {
                final_i = text_start + i;
                // In Skip state, we are skipping the next character.
                if skip {
                    skip = false;
                    continue;
                }
                if !in_escape {
                    //check for escape sequences
                    if c == '"' {
                        // Possibly End?
                        if text.chars().nth(text_start + i + 1).unwrap_or(' ') == '"' {
                            skip = true;
                            continue;
                        }
                        // THE END OF THE TEXT
                        break;
                    }
                    // lookahead to validate escape
                    if c == '#' && text.chars().nth(text_start + i + 1).unwrap_or(' ') == '(' {
                        in_escape = true;
                        skip = true;
                        continue;
                    }
                } else {
                    // TODO: Validate the escape characters are valid
                    if c == ')' {
                        in_escape = false;
                    }
                    continue;
                }
            }
            if in_escape {
                // Uh OH
                return Err(Box::new(ParseError::InvalidInput {
                    pointer: text_start,
                    ctx: parse_utils::gen_error_ctx(text, text_start, ERR_CONTEXT_SIZE),
                }));
            }
            Ok((final_i + 1, Self::Text(&text[text_start..final_i])))
        } else {
            Err(Box::new(ParseError::InvalidInput {
                pointer: text_start,
                ctx: parse_utils::gen_error_ctx(text, text_start, ERR_CONTEXT_SIZE),
            }))
        }
    }

    fn try_parse_null(text: &'a str) -> ParseResult<Self> {
        let text_start = parse_utils::skip_whitespace(text);
        // What if Null is the Final entity?
        if text[text_start..].len() == 4 {
            if &text[text_start..=text_start + 3] == "null" {
                // Still Plus 4 because we want the next thing to point to the end of the string,
                // not "l" (i.e) the value we pass out should == len of the text
                assert!(text.len() == text_start + 4);
                Ok((text_start + 4, Literal::Null))
            } else {
                Err(Box::new(ParseError::InvalidInput {
                    pointer: text_start,
                    ctx: parse_utils::gen_error_ctx(text, text_start, ERR_CONTEXT_SIZE),
                }))
            }
        } else if text[text_start..].starts_with(keywords::NULL)
            && followed_by_valid_seperator(&text[text_start..], 4)
        {
            Ok((text_start + 4, Literal::Null))
        } else {
            Err(Box::new(ParseError::InvalidInput {
                pointer: text_start,
                ctx: parse_utils::gen_error_ctx(text, text_start, ERR_CONTEXT_SIZE),
            }))
        }
    }

    // number-literal:
    //      decimal-number-literal
    //      hexadecimal-number-literal
    // decimal-digits:
    //      decimal-digit decimal-digitsopt
    // decimal-digit: one of
    //      0 1 2 3 4 5 6 7 8 9
    // hexadecimal-number-literal:
    //      0x hex-digits
    //      0X hex-digits
    // hex-digits:
    //      hex-digit hex-digitsopt
    //      hex-digit: one of
    //      0 1 2 3 4 5 6 7 8 9 A B C D E F a b c d e f
    // decimal-number-literal:
    //      decimal-digits . decimal-digits
    //      exponent-partopt
    //      . decimal-digits
    //      exponent-partopt
    //      decimal-digits
    //      exponent-partopt
    // exponent-part:
    //      e signopt
    // decimal-digits
    //      E signopt
    //      decimal-digits
    // sign: one of
    //      + -
    fn try_parse_number(text: &'a str) -> ParseResult<Self> {
        let mut parse_pointer = parse_utils::skip_whitespace(text);

        // 0x1234

        // Hex number
        if text[parse_pointer..].starts_with("0x") || text[parse_pointer..].starts_with("0X") {
            parse_pointer += 2; // Skip 0x
            let num_start = parse_pointer;
            let num_delta = text[num_start..]
                .chars()
                .take_while(|c| c.is_ascii_hexdigit())
                .count();

            if num_delta == 0 {
                // Hex digit must have _a_ value
                return Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }));
            }
            parse_pointer += num_delta;

            // TODO: What if the next character is an invalid character for this to be a number-literal
            return Ok((
                parse_pointer, // count() is not zero indexed, so we have to
                // shift pointer value back by one,
                Self::Number(NumberType::Int(
                    // Skip the first two because from radix doesn't like the "0x" prefix.
                    isize::from_str_radix(&text[num_start..num_start + num_delta], 16).unwrap(),
                )),
            ));
        } else {
            // DecimalNumber
            // decimal-number-literal:
            //      decimal-digits . decimal-digits exponent-partopt
            //      . decimal-digits exponent-partopt
            //      decimal-digits exponent-partopt
            // exponent-part:
            //      e signopt decimal-digits
            //      E signopt decimal-digits
            // sign: one of
            //      + -
            let num_delta = text[parse_pointer..]
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .count();

            let mut num_end = parse_pointer + num_delta;

            let has_integer_part = num_end > parse_pointer;

            // Handle the fraction portion
            if text[num_end..].starts_with('.') {
                num_end += text[num_end..]
                    .chars()
                    .skip(1)
                    .take_while(|c| c.is_ascii_digit())
                    .count()
                    + 1; // Plus 1 because we skipped the decimal point

                if !has_integer_part && num_end <= parse_pointer + 1 {
                    // This is just a '.' we can't make a number from that
                    return Err(Box::new(ParseError::InvalidInput {
                        pointer: parse_pointer,
                        ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                    }));
                }
            }
            // handle Optional Exponent
            let mut exponent_iter = text[num_end..].char_indices();
            let mut signed = false;
            if [(0, 'E'), (0, 'e')].contains(&exponent_iter.next().unwrap_or((0, ' '))) {
                let delta = exponent_iter
                    .take_while(|(i, c)| {
                        // -/+ are valid values for a number to take in the first position
                        if (*c == '-' || *c == '+') && *i == 1_usize {
                            signed = true;
                            true
                        } else {
                            (*c).is_ascii_digit()
                        }
                    })
                    .count();

                if delta > 0 {
                    num_end += delta + 1; // To account for the E/e
                }
            }
            // Return parsed value:
            if parse_pointer == num_end {
                Err(Box::new(ParseError::InvalidInput {
                    pointer: parse_pointer,
                    ctx: parse_utils::gen_error_ctx(text, parse_pointer, ERR_CONTEXT_SIZE),
                }))
            } else {
                Ok((
                    num_end, // The Returned delta should be pointing at the final digit in the
                    // number
                    Self::Number(NumberType::Float(
                        text[parse_pointer..num_end].parse().unwrap(),
                    )),
                ))
            }
        }
    }

    fn try_parse_verbatim_literal(text: &'a str) -> ParseResult<Self> {
        // Is there the initial `"`?
        let text_start = parse_utils::skip_whitespace(text);
        if text[text_start..].starts_with(r#"#!""#) {
            // Find the terminal `"`? Remember Escapes!
            let mut skip = false;
            let mut final_i = text_start;
            for (i, c) in text[text_start..].char_indices().skip(3) {
                final_i = i;
                // In Skip state, we are skipping the next character.
                if skip {
                    skip = false;
                    continue;
                }
                //check for escape sequence
                if c == '"' {
                    if text[text_start + i + 1..].chars().next().unwrap_or(' ') == '"' {
                        // Not the end, just an escaped '"'
                        skip = true;
                        continue;
                    }
                    // THE END OF THE TEXT
                    break;
                }
            }
            Ok((
                text_start + final_i + 1, // Account for the final `"`
                Self::Verbatim(&text[text_start + 3..text_start + final_i]),
            )) // ADD Three to skip the #!"
        } else {
            Err(Box::new(ParseError::InvalidInput {
                pointer: text_start,
                ctx: parse_utils::gen_error_ctx(text, text_start, ERR_CONTEXT_SIZE),
            }))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use rstest::rstest;

    #[rstest]
    #[case("true, 'more stuff', yadda yadda", Literal::Logical(true), 4)]
    #[case("false, 'more stuff', yadda yadda", Literal::Logical(false), 5)]
    fn test_logical_literal_parser(
        #[case] input: &str,
        #[case] expected: Literal,
        #[case] expected_delta: usize,
    ) {
        let (delta, out) = Literal::try_parse_logical(input).unwrap();
        assert_matches!(expected, out);
        assert_eq!(expected_delta, delta);
    }

    #[rstest]
    #[case(
        r##""false, 'more stuff', yadda yadda""##,
        Literal::Text("false, 'more stuff', yadda yadda"),
        "false, 'more stuff', yadda yadda",
        34
    )]
    #[case(
        r#""""false""", More Stuff"#,
        Literal::Text(r#"""false"""#),
        r#"""false"""#,
        11
    )]
    #[case(
        r#""This is some#(tab) text", More Stuff"#,
        Literal::Text("This is some#(tab) text"),
        "This is some#(tab) text",
        25
    )]
    #[case(r#" """""""" "#, Literal::Text(r#""""""""#), r#""""""""#, 9)]
    fn test_text_literal_parser(
        #[case] input: &str,
        #[case] expected: Literal,
        #[case] value: &str,
        #[case] expected_delta: usize,
    ) {
        let (delta, out) = Literal::try_parse_text(input).unwrap();
        assert!(matches!(expected, out));
        assert_eq!(expected_delta, delta);
        match out {
            Literal::Text(text) => assert_eq!(value, text),
            _ => unreachable!(),
        }
    }

    #[rstest]
    #[case(
        r#"   #!"This is verbaitm text""#,
        Literal::Verbatim("This is verbaitm text"),
        "This is verbaitm text",
        28
    )]
    #[case(
        r#"#!"Thi""s is verbaitm text""#,
        Literal::Verbatim("This is verbaitm text"),
        r#"Thi""s is verbaitm text"#,
        27
    )]
    #[case(
        r#"#!"This is verbaitm text""#,
        Literal::Verbatim("This is verbaitm text"),
        "This is verbaitm text",
        25
    )]
    // #[case(r#" !#"""""""" "#, Literal::Text(r#""""""""""#), r#""""""""""#)]
    fn test_verbatim_literal_parser(
        #[case] input: &str,
        #[case] expected: Literal,
        #[case] value: &str,
        #[case] expected_delta: usize,
    ) {
        let (delta, out) = Literal::try_parse_verbatim_literal(input).unwrap();
        assert!(matches!(expected, out));
        assert_eq!(expected_delta, delta);
        match out {
            Literal::Verbatim(text) => assert_eq!(value, text),
            _ => unreachable!(),
        }
    }

    #[rstest]
    #[case("    nottext, 'more stuff', yadda yadda")]
    // Should we Have this, or should we let people write bad text?
    #[case("Broken escape #(lt")]
    fn text_literal_parser_errors(#[case] input: &str) {
        let out = Literal::try_parse_text(input);
        match out {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[rstest]
    #[case(r#" null "#)]
    #[case(r#"null "#)]
    #[case(r#"null"#)]
    fn null_literal_parser(#[case] input: &str) {
        let (_, out) = Literal::try_parse_null(input).unwrap();
        assert!(matches!(Literal::Null, out));
    }

    #[rstest]
    #[case(r#"0x1234"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 6)]
    #[case(r#"0X1234"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 6)]
    #[case(r#"0X1234,"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 6)]
    #[case(r#"0x1234,"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 6)]
    #[case(r#"0X1234  ,"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 6)]
    #[case(r#"0x1234  ,"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 6)]
    #[case(r#"   0X1234  ,"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 9)]
    #[case(r#"   0x1234  ,"#, Literal::Number(NumberType::Int(0x1234)), 0x1234, 9)]
    fn hex_int_literal_parser(
        #[case] input: &str,
        #[case] expected: Literal,
        #[case] value: isize,
        #[case] exp_delta: usize,
    ) {
        let (delta, out) = Literal::try_parse_number(input).unwrap();
        assert!(matches!(expected, out));
        assert_eq!(exp_delta, delta);
        match out {
            Literal::Number(NumberType::Int(v)) => assert_eq!(v, value),
            _ => assert!(false),
        }
    }

    #[rstest]
    #[case("0Xyz")]
    fn text_hex_parser_fails(#[case] input: &str) {
        let out = Literal::try_parse_number(input);
        match out {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[rstest]
    #[case(r#"1234"#, Literal::Number(NumberType::Float(1234.)), 1234.0, 4)]
    #[case(r#"1234 "#, Literal::Number(NumberType::Float(1234.)), 1234.0, 4)]
    #[case(r#" 1234 "#, Literal::Number(NumberType::Float(1234.)), 1234.0, 5)]
    #[case(r#"1234.25"#, Literal::Number(NumberType::Float(1234.25)), 1234.25, 7)]
    #[case(
        r#"1234.25E5"#,
        Literal::Number(NumberType::Float(1234.25E5)),
        1234.25E5,
        9
    )]
    #[case(
        r#"1234.25e5"#,
        Literal::Number(NumberType::Float(1234.25E5)),
        1234.25E5,
        9
    )]
    #[case(
        r#"   1234.25E-5 "#,
        Literal::Number(NumberType::Float(1234.25E-5)),
        1234.25E-5,
        13
    )]
    #[case(
        r#"1234.25EX5"#,
        Literal::Number(NumberType::Float(1234.25)),
        1234.25,
        7
    )]
    #[case(
        r#"1234.25E-5"#,
        Literal::Number(NumberType::Float(1234.25E-5)),
        1234.25E-5,
        10
    )]
    fn decimal_number_parser(
        #[case] input: &str,
        #[case] expected: Literal,
        #[case] value: f64,
        #[case] exp_delta: usize,
    ) {
        let (delta, _out) = Literal::try_parse_number(input).unwrap();
        assert!(matches!(expected, _out));
        assert_eq!(exp_delta, delta);
        match _out {
            Literal::Number(NumberType::Float(v)) => assert_eq!(v, value),
            _ => assert!(false),
        }
    }

    #[rstest]
    #[case(".")]
    fn text_decimal_parser_fails(#[case] input: &str) {
        let out = Literal::try_parse_number(input);
        match out {
            Err(_) => assert!(true),
            _ => assert!(false),
        }
    }
}
