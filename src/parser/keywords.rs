//! Keywords
//!
//! https://learn.microsoft.com/en-us/powerquery-m/m-spec-consolidated-grammar#keywords-and-predefined-identifiers
//!
//!    and as each else error false if in is let meta not null or otherwise
//!    section shared then true try type #binary #date #datetime
//!    #datetimezone #duration #infinity #nan #sections #shared #table #time

pub const AND: &str = "and";
pub const AS: &str = "as";
pub const EACH: &str = "each";
pub const ELSE: &str = "else";
pub const ERROR: &str = "error";
pub const FALSE: &str = "false";
pub const IF: &str = "if";
pub const IN: &str = "in";
pub const IS: &str = "is";
pub const LET: &str = "let";
pub const META: &str = "meta";
pub const NOT: &str = "not";
pub const NULL: &str = "null";
pub const OR: &str = "or";
pub const OTHERWISE: &str = "otherwise";
pub const SECTION: &str = "section";
pub const SHARED: &str = "shared";
pub const THEN: &str = "then";
pub const TRUE: &str = "true";
pub const TRY: &str = "try";
pub const TYPE: &str = "type";
pub const BINARY: &str = "#binary";
pub const DATE: &str = "#date";
pub const DATETIME: &str = "#datetime";
pub const DATETIMEZONE: &str = "#datetimezone";
pub const DURATION: &str = "#duration";
pub const INFINITY: &str = "#infinity";
pub const NAN: &str = "#nan";
pub const SECTIONS: &str = "#sections";
pub const SHARED_HASH: &str = "#shared";
pub const TABLE: &str = "#table";
pub const TIME: &str = "#time";

const FUNC_KEYWORDS: [&str; 7] = [BINARY, DATE, DATETIME, DATETIMEZONE, DURATION, TABLE, TIME];

const KEYWORDS: [&str; 32] = [
    AND,
    AS,
    EACH,
    ELSE,
    ERROR,
    FALSE,
    IF,
    IN,
    IS,
    LET,
    META,
    NOT,
    NULL,
    OR,
    OTHERWISE,
    SECTION,
    SHARED,
    THEN,
    TRUE,
    TRY,
    TYPE,
    BINARY,
    DATE,
    DATETIME,
    DATETIMEZONE,
    DURATION,
    INFINITY,
    NAN,
    SECTIONS,
    SHARED_HASH,
    TABLE,
    TIME,
];

#[inline]
pub fn is_keyword(val: &str) -> bool {
    KEYWORDS.contains(&val)
}

#[inline]
pub fn is_func_keyword(val: &str) -> bool {
    FUNC_KEYWORDS.contains(&val)
}
