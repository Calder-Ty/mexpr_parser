//! Keywords
//!
//! https://learn.microsoft.com/en-us/powerquery-m/m-spec-consolidated-grammar#keywords-and-predefined-identifiers
//!
//!    and as each else error false if in is let meta not null or otherwise
//!    section shared then true try type #binary #date #datetime
//!    #datetimezone #duration #infinity #nan #sections #shared #table #time

const AND: &str = "and";
const AS: &str = "as";
const EACH: &str = "each";
const ELSE: &str = "else";
const ERROR: &str = "error";
const FALSE: &str = "false";
const IF: &str = "if";
const IN: &str = "in";
const IS: &str = "is";
const LET: &str = "let";
const META: &str = "meta";
const NOT: &str = "not";
const NULL: &str = "null";
const OR: &str = "or";
const OTHERWISE: &str = "otherwise";
const SECTION: &str = "section";
const SHARED: &str = "shared";
const THEN: &str = "then";
const TRUE: &str = "true";
const TRY: &str = "try";
const TYPE: &str = "type";

const BINARY: &str = "#binary";
const DATE: &str = "#date";
const DATETIME: &str = "#datetime";
const DATETIMEZONE: &str = "#datetimezone";
const DURATION: &str = "#duration";
const INFINITY: &str = "#infinity";
const NAN: &str = "#nan";
const SECTIONS: &str = "#sections";
const SHARED_HASH: &str = "#shared";
const TABLE: &str = "#table";
const TIME: &str = "#time";

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
