pub enum ParserState<'a> {
    Let,
    VariableList,
    Variable,
    VariableName(Identifier<'a>),
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
        let ident_range = {
        self.end = Some({s + self.text[s..]
                .char_indices()
                .take_while(|(_, c)| {
                    if is_quoted {
                        *c != '"'
                    } else {
                        !(*c).is_whitespace()
                    }
                })
                .count()});
            s..(self.end.unwrap())
        };

        &self.text[ident_range]
    }

    pub fn end(&self) -> Option<usize> {
        self.end
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

///
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
        // Go on to just pass the = sign
    }
}

/// Used to parse A variable name.
struct Variable {
    identifier: &'static str,
    value: MExpression,
}

enum MExpression {
    InvokeExpression(ArgumentList),
    Value(ValueType),
}

enum ValueType {
    StringLiteral(&'static str),
    Integer(isize),
}

struct ArgumentList {
    pub args: Vec<MExpression>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case("This = Not a variable", "This")]
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
}
