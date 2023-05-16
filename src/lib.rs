use std::num;

use thiserror::Error;

type ParseResult<T> = Result<(usize, T), Box<ParseError>>;

const HEX_DIGITS: [char; 22] = [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'a', 'b', 'c',
    'd', 'e', 'f',
];

#[derive(Debug, Error)]
enum ParseError {
    #[error("Input is Invalid, Unable to proceed")]
    InvalidInput,
}

pub enum ParserState<'a> {
    Let,
    VariableList,
    Variable,
    VariableName(Identifier<'a>),
}

fn is_identifier_part(c: &char) -> bool {
    // For now just '.', rather than finding a group for Mn, Mc or Pc
    // to represent continuation characters
    c.is_alphabetic() || c.is_digit(10) || *c == '_' || *c == '.'
}

#[inline]
fn skip_whitespace(text: &str) -> usize {
    text.char_indices()
        .take_while(|(_, c)| (*c).is_whitespace())
        .count()
}

pub struct Identifier<'a> {
    text: &'a str,
    start: Option<usize>,
    end: Option<usize>,
}

impl<'a> Identifier<'a> {
    fn new(text: &'a str) -> Self {
        Self {
            text,
            start: None,
            end: None,
        }
    }

    pub(crate) fn parse(&mut self, start: usize) -> &str {
        // Get the start of the identifier
        let ident_offset = self.text[start..]
            .char_indices()
            .take_while(|(_, c)| (*c).is_whitespace())
            .count();

        let ident_text: &str;

        if ident_offset == 0 {
            self.start = Some(start);
            ident_text = &self.text;
        } else {
            self.start = Some(start + ident_offset);
            ident_text = &self.text[start + ident_offset..];
        }
        // Check if it is a Quoted Identifier
        let is_quoted = if ident_text.starts_with("#") {
            // Can unwrap because we know we have initialized the value already ^^^
            self.start = Some(self.start.unwrap() + 2);
            true
        } else {
            false
        };

        let s = self.start.unwrap();
        // Get the identifier range
        self.end = Some({
            s + self.text[s..]
                .char_indices()
                .take_while(|(_, c)| {
                    if is_quoted {
                        *c != '"'
                    } else {
                        is_identifier_part(c)
                    }
                })
                .count()
        });

        &self.text()
    }

    pub fn end(&self) -> Option<usize> {
        self.end
    }

    pub fn text(&self) -> &str {
        // Eventually fix this with Valid States
        &self.text[self.start.unwrap()..self.end.unwrap()]
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
    pub fn parse(&mut self, text: &'state str) {
        // This takes us past the let statement
        // Skip the Variable List state, because we know where we are.
        self.parser_state = ParserState::VariableName(Identifier::new(text));
        let mut subparser = Identifier::new(text);
        // Skip let part of the statement
        let ident = subparser.parse(3);
        // split on the = sign, now pass that in
        let var_txt = text[subparser.end().unwrap() + 1..]
            .splitn(2, '=')
            .last()
            .unwrap();
        // let supbarser = MExpresion::parse(var_txt);
    }
}

/// Used to parse A variable name.
struct Variable<'a> {
    identifier: &'a str,
    value: PrimaryExpression<'a>,
}

// primary-expression:
//       literal-expression
//       list-expression
//       record-expression
// x       identifier-expression
//       section-access-expression
//       parenthesized-expression
//       field-access-expression
//       item-access-expression
//       invoke-expression
//       not-implemented-expression
//
/// For now We are only implementing a parser for Identifier Expression and
/// Invoke Expressions. This is the minimum we need for the task.
enum PrimaryExpression<'a> {
    /// invoke-expression:
    ///     primary-expression <(> argument-listopt <)>
    /// argument-list:
    ///     expression
    ///     expression , argument-list
    IdentifierExpression(Identifier<'a>),
    InvokeExpression(Box<Invocation<'a>>),
    LiteralExpression(Literal<'a>),
}

impl<'a> PrimaryExpression<'a> {
    // parses the stuff and returns an instance of itself
    fn try_parse(text: &str) -> Result<(usize, Self), ParseError> {
        unimplemented!()
    }
}

/// Literal:
///     LogicalLiteral
///     NumberLiteral
///     TextLiteral
///     NullLiteral
///     VerbatimLiteral
enum Literal<'a> {
    LogicalLiteral(bool),
    TextLiteral(&'a str),
    NumberLiteral(NumberType),
    NullLiteral,
    VerbatimLiteral,
}

enum NumberType {
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

        if let Ok(val) = Self::try_parse_text(text) {
            return Ok(val);
        };

        if let Ok(val) = Self::try_parse_number(text) {
            return Ok(val);
        };

        return Err(Box::new(ParseError::InvalidInput));
    }

    fn try_parse_logical(text: &str) -> ParseResult<Self> {
        // true?
        let text_start = skip_whitespace(text);
        if &text[text_start..text_start + 4] == "true" {
            return Ok((text_start + 4, Self::LogicalLiteral(true)));
        }
        if &text[text_start..text_start + 5] == "false" {
            return Ok((text_start + 4, Self::LogicalLiteral(false)));
        }
        Err(Box::new(ParseError::InvalidInput))
    }

    fn try_parse_text(text: &'a str) -> ParseResult<Self> {
        // is there the initial `"`?
        let text_start = skip_whitespace(text);
        if &text.chars().nth(text_start).unwrap_or(' ') == &'"' {
            // Find the terminal `"`? Remember Escapes!
            let mut in_escape = false;
            let mut skip = false;
            let mut final_i = text_start;
            for (i, c) in text[text_start..].char_indices() {
                final_i = i;
                // In Skip state, we are skipping the next character.
                if skip {
                    skip = false;
                    continue;
                }
                if !in_escape {
                    //check for escape sequence
                    if c == '"' && i != 0 {
                        // Possibly End?
                        if text.chars().nth(i + 1).unwrap_or(' ') == '"' {
                            skip = true;
                            continue;
                        }
                        // THE END OF THE TEXT
                        break;
                    }
                    if c == '#' && text.chars().nth(i + 1).unwrap_or(' ') == '(' {
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
                return Err(Box::new(ParseError::InvalidInput));
            }
            Ok((final_i, Self::TextLiteral(&text[text_start..=final_i])))
        } else {
            Err(Box::new(ParseError::InvalidInput))
        }
    }

    fn try_parse_null(text: &'a str) -> ParseResult<Self> {
        let text_start = skip_whitespace(text);
        // What if Null is the Final entity?
        if text[text_start..].len() == 4 {
            if &text[text_start..=text_start + 3] == "null" {
                // Still Plus 4 because we want the next thing to point to the end of the string,
                // not "l" (i.e) the value we pass out should == len of the text
                assert!(text.len() == text_start + 4);
                Ok((text_start + 4, Literal::NullLiteral))
            } else {
                Err(Box::new(ParseError::InvalidInput))
            }
        } else {
            if &text[text_start..=text_start + 4] == "null " {
                Ok((text_start + 4, Literal::NullLiteral))
            } else {
                Err(Box::new(ParseError::InvalidInput))
            }
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
        let num_start = skip_whitespace(text);

        // Hex number
        if text[num_start..].starts_with("0x") || text[num_start..].starts_with("0X") {
            let num_end = text[num_start + 2..] // Skip the 0x part
                .chars()
                .take_while(|c| HEX_DIGITS.contains(c))
                .count()
                + (num_start + 2); //To account for the skipped indicies at the start

            // TODO: What if the next character is an invalid character for this to be a number-literal
            if num_end == num_start + 2 {
                // Hex digit must have _a_ value
                return Err(Box::new(ParseError::InvalidInput));
            } else {
                dbg!(&text[num_start + 2..num_end]);
                return Ok((
                    num_end,
                    Self::NumberLiteral(NumberType::Int(
                        isize::from_str_radix(&text[num_start + 2..num_end], 16).unwrap(),
                    )),
                ));
            }
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
            let mut num_end = text[num_start..]
                .chars()
                .take_while(|c| c.is_digit(10))
                .count()
                + num_start;
            let has_integer_part = num_end > num_start;

            // Handle the fraction portion
            if text[num_end..].starts_with(".") {
                num_end += text[num_end..]
                    .chars()
                    .skip(1)
                    .take_while(|c| c.is_digit(10))
                    .count()
                    + 1; // Plus 1 because we skipped the decimal point

                if !has_integer_part && num_end <= num_start + 1 {
                    // This is just a '.' we can't make a number from that
                    return Err(Box::new(ParseError::InvalidInput));
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
                            (*c).is_digit(10)
                        }
                    })
                    .count();

                if delta > 0 {
                    num_end += delta + 1; // To account for the E/e
                }
            }
            // Return parsed value:
            return Ok((
                num_end,
                Self::NumberLiteral(NumberType::Float(text[num_start..num_end].parse().unwrap())),
            ));
        }
    }
}

struct InvocationParser<'a> {
    text: &'a str,
    start: usize,
    end: Option<usize>,
}

impl<'a> InvocationParser<'a> {
    fn new(text: &'a str, start: usize) -> Self {
        Self {
            text,
            start,
            end: None,
        }
    }

    pub fn try_parse(self) -> ParseResult<Invocation<'a>> {
        // To start, we need to identifiy the calling Expresion. Lets try:
        let mut invoker = Identifier::new(self.text);
        invoker.parse(self.start);
        // For and invocation we expect that we can be in a call so lets try something here:
        let mut args = vec![];
        // parsing the function calls
        let arglist = &self.text[invoker.end.unwrap()..];
        // Skip the Calling Parenthesis
        let mut arglist_start = arglist
            .char_indices()
            .take_while(|(_, c)| *c != '(')
            .count();
        // Now we need to Parse the contents of the function invocation
        loop {
            let (delta, arg) = PrimaryExpression::try_parse(&self.text[arglist_start..])?;
            args.push(arg);
            arglist_start += delta;
            // Handle whitspace, incase we have a pyscho
            if self.text[arglist_start..]
                .chars()
                .skip_while(|c| (*c).is_whitespace())
                .nth(0)
                .unwrap()
                == ')'
            {
                break;
            }
        }

        Ok((
            arglist_start,
            Invocation {
                invoker: PrimaryExpression::IdentifierExpression(invoker),
                args,
            },
        ))
    }
}

struct Invocation<'a> {
    pub invoker: PrimaryExpression<'a>,
    pub args: Vec<PrimaryExpression<'a>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case("This = Not a variable", "This")]
    #[case("This=Not a variable", "This")]
    #[case("   This = Not a variable", "This")]
    #[case(r##"#"This is some text" = Not a variable"##, "This is some text")]
    #[case(r##"   #"This is some text" = Not a variable"##, "This is some text")]
    // Keeping this malformed name for now, just want to make sure the parser doesn't panic on it.
    // The expectation is that the input is lexically valid
    #[case(r##"#"Malformed name"##, "Malformed name")]
    #[case("ThisIsTheEND", "ThisIsTheEND")]
    fn test_parse_variable_name(#[case] input: &str, #[case] expected: &str) {
        let mut parser = Identifier::new(input);
        let out = parser.parse(0);
        assert_eq!(expected, out)
    }

    // #[rstest]
    fn test_invokation_parser() {
        let input_text = "This('Not a variable')";
        let mut parser = InvocationParser::new(input_text, 0);
        let (_, invokation) = parser
            .try_parse()
            .expect(format!("failed to parse test input '{}'", &input_text).as_str());

        if let PrimaryExpression::IdentifierExpression(invoker) = invokation.invoker {
            assert_eq!(invoker.text(), "This")
        }
    }

    #[rstest]
    #[case("true, 'more stuff', yadda yadda", Literal::LogicalLiteral(true))]
    #[case("false, 'more stuff', yadda yadda", Literal::LogicalLiteral(false))]
    fn test_logical_literal_parser(#[case] input: &str, #[case] expected: Literal) {
        let (_, out) = Literal::try_parse(input).unwrap();
        assert!(matches!(expected, out))
    }

    #[rstest]
    #[case(
        r##""false, 'more stuff', yadda yadda""##,
        Literal::TextLiteral(r#""false, 'more stuff', yadda yadda""#),
        r#""false, 'more stuff', yadda yadda""#
    )]
    #[case(
        r#""""false""", More Stuff"#,
        Literal::TextLiteral(r#""""false""""#),
        r#""""false""""#
    )]
    #[case(
        r#""This is some#(tab) text", More Stuff"#,
        Literal::TextLiteral(r#""This is some#(tab) text""#),
        r#""This is some#(tab) text""#
    )]
    #[case(r#" """""""" "#, Literal::TextLiteral(r#""""""""""#), r#""""""""""#)]
    fn test_text_literal_parser(
        #[case] input: &str,
        #[case] expected: Literal,
        #[case] value: &str,
    ) {
        let (_, out) = Literal::try_parse_text(input).unwrap();
        assert!(matches!(expected, out));
        match out {
            Literal::TextLiteral(text) => assert_eq!(value, text),
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
        assert!(matches!(Literal::NullLiteral, out));
    }

    #[rstest]
    #[case(r#"0x1234"#, Literal::NumberLiteral(NumberType::Int(0x1234)), 0x1234)]
    #[case(r#"0X1234"#, Literal::NumberLiteral(NumberType::Int(0x1234)), 0x1234)]
    #[case(r#"0X1234,"#, Literal::NumberLiteral(NumberType::Int(0x1234)), 0x1234)]
    #[case(r#"0x1234,"#, Literal::NumberLiteral(NumberType::Int(0x1234)), 0x1234)]
    #[case(
        r#"0X1234  ,"#,
        Literal::NumberLiteral(NumberType::Int(0x1234)),
        0x1234
    )]
    #[case(
        r#"0x1234  ,"#,
        Literal::NumberLiteral(NumberType::Int(0x1234)),
        0x1234
    )]
    #[case(
        r#"   0X1234  ,"#,
        Literal::NumberLiteral(NumberType::Int(0x1234)),
        0x1234
    )]
    #[case(
        r#"   0x1234  ,"#,
        Literal::NumberLiteral(NumberType::Int(0x1234)),
        0x1234
    )]
    fn hex_int_literal_parser(
        #[case] input: &str,
        #[case] expected: Literal,
        #[case] value: isize,
    ) {
        let (_, out) = Literal::try_parse_number(input).unwrap();
        assert!(matches!(expected, out));
        match out {
            Literal::NumberLiteral(NumberType::Int(v)) => assert_eq!(v, value),
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
    #[case(r#"1234"#, Literal::NumberLiteral(NumberType::Float(1234.)), 1234.0)]
    #[case(r#"1234 "#, Literal::NumberLiteral(NumberType::Float(1234.)), 1234.0)]
    #[case(r#" 1234 "#, Literal::NumberLiteral(NumberType::Float(1234.)), 1234.0)]
    #[case(
        r#"1234.25"#,
        Literal::NumberLiteral(NumberType::Float(1234.25)),
        1234.25
    )]
    #[case(
        r#"1234.25E5"#,
        Literal::NumberLiteral(NumberType::Float(1234.25E5)),
        1234.25E5
    )]
    #[case(
        r#"1234.25e5"#,
        Literal::NumberLiteral(NumberType::Float(1234.25E5)),
        1234.25E5
    )]
    #[case(
        r#"   1234.25E-5 "#,
        Literal::NumberLiteral(NumberType::Float(1234.25E-5)),
        1234.25E-5
    )]
    #[case(
        r#"1234.25EX5"#,
        Literal::NumberLiteral(NumberType::Float(1234.25)),
        1234.25
    )]
    #[case(
        r#"1234.25E-5"#,
        Literal::NumberLiteral(NumberType::Float(1234.25E-5)),
        1234.25E-5
    )]
    fn decimal_number_parser(#[case] input: &str, #[case] expected: Literal, #[case] value: f64) {
        let (_, out) = Literal::try_parse_number(input).unwrap();
        assert!(matches!(expected, out));
        match out {
            Literal::NumberLiteral(NumberType::Float(v)) => assert_eq!(v, value),
            _ => assert!(false),
        }
    }
}
