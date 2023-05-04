pub enum ParserState<'a> {
    Let,
    VariableList,
    Variable,
    VariableName(VariableName<'a>),
}

pub struct VariableName<'a> {
    text: &'a str,
    start: Option<usize>,
    end: Option<usize>,
}

impl<'a> VariableName<'a> {
    fn new(text: &'a str) -> Self {
        Self {
            text,
            start: None,
            end: None,
        }
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
        self.parser_state = ParserState::VariableName(VariableName::new(text));
        // Skip let part of the statement
        let ident = parse_variable_name(&text[3..]);
        // Go on to just pass the = sign
    }
}

/// Used to parse A variable name.
fn parse_variable_name<'txt>(text: &'txt str) -> &'txt str {
    // Get the start of the identifier
    let (ident_start, _) = text
        .char_indices()
        .take_while(|(_, c)| (*c).is_whitespace())
        .last()
        .unwrap_or((0, ' '));

    let ident_text: &str;
    if ident_start == 0 {
        ident_text = &text;
    } else {
        ident_text = &text[ident_start + 1..];
    }

    // Check if it is a Quoted Identifier
    let mut is_quoted = false;
    if ident_text.starts_with("#") {
        is_quoted = true;
    }

    // Get the Identifer range
    let ident_range = if is_quoted {
        let (end, _) = ident_text
            .chars()
            .enumerate()
            .skip(2)
            .take_while(|(_, c)| *c != '"')
            .last()
            .unwrap();
        // because we skip the first two characters
        2..=end
    } else {
        let (end, _) = ident_text
            .chars()
            .enumerate()
            .take_while(|(_, c)| !(*c).is_whitespace())
            .last()
            .unwrap();
        0..=end
    };

    &ident_text[ident_range]
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
