mod parser;
pub use parser::parse_utils::ParseError;
pub use parser::try_parse;

pub(crate) const ERR_CONTEXT_SIZE: usize = 10;
