pub enum ParserState {
    Let,
    VariableList,
    Variable,
    VariableName,
}

pub struct Parser {
    variables: Vec<&'static str>,
    parser_state: ParserState,
}

impl Default for Parser {
    fn default() -> Self {
        Self {
            variables: Vec::default(),
            parser_state: ParserState::Let,
        }
    }
}

impl Parser {
    pub fn parse<'txt>(&mut self, text: &'txt str) {
        // This takes us past the let statement
        // Skip the Variable List state, because we know where we are.
        self.parser_state = ParserState::VariableName;
        // FIXME: Make sure i don't read too far
        let ident = parse_variable_name(&text[3..]);
    }
}

/// Used to parse A variable name.
fn parse_variable_name<'txt>(text: &'txt str) -> &'txt str {
    let mut is_quoted = false;


    // Get the start of the identifier
    let (ident_start, _) = text
        .chars()
        .enumerate()
        .take_while(|(i, c)| (*c).is_whitespace())
        .last()
        .unwrap_or((0, ' '));


    let ident_text: &str;
    if ident_start == 0 {
        ident_text = &text;
    }
    else {
        ident_text = &text[ident_start+1..];
    }

    //
    if ident_text.starts_with("#") {
        is_quoted = true;
    }

    let mut start: usize = 0;
    let mut end: usize;

    if is_quoted {
        start = 2;
        (end, _) = ident_text
            .chars()
            .enumerate()
            .skip(2)
            .take_while(|(i, c)| *c != '"')
            .last()
            .unwrap()
    } else {
        (end, _) = ident_text
            .chars()
            .enumerate()
            .take_while(|(i, c)| !(*c).is_whitespace())
            .last()
            .unwrap()
    }

    &ident_text[start..end + 1]
}
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
        let out = parse_variable_name(input);
        assert_eq!(expected, out)
    }
}
