#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    Null,
    Number(f64),
    String(String),
    Bool(bool),

    // Identifiers
    Ident(String),

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Equals,
    EqualsEquals,
    NotEquals,
    LessThan,
    LessThanEquals,
    GreaterThan,
    GreaterThanEquals,
    And,
    Or,
    Not,

    // Symbols
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Comma,
    Dot,

    // Keywords
    Let,
    Struct,
    If,
    Else,
    While,
    For,
    Continue,
    Break,
    Return,
    Try,
    Catch,

    // Comments
    LineComment,
    BlockCommentStart,
    BlockCommentEnd,
}
