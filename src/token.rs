#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    // Literals
    Null,
    Number(f64),
    Str(String),
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
    Semicolon,
    Colon,
    Pipe,

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
    New,
    Fn,
}

impl std::hash::Hash for Token {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}

impl std::cmp::Eq for Token {}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Null => write!(f, "null"),
            Token::Number(n) => write!(f, "{n}"),
            Token::Str(s) => write!(f, "{s}"),
            Token::Bool(b) => write!(f, "{b}"),
            Token::Ident(s) => write!(f, "{s}"),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Percent => write!(f, "%"),
            Token::Equals => write!(f, "="),
            Token::EqualsEquals => write!(f, "=="),
            Token::NotEquals => write!(f, "!="),
            Token::LessThan => write!(f, "<"),
            Token::LessThanEquals => write!(f, "<="),
            Token::GreaterThan => write!(f, ">"),
            Token::GreaterThanEquals => write!(f, ">="),
            Token::And => write!(f, "&&"),
            Token::Or => write!(f, "||"),
            Token::Not => write!(f, "!"),
            Token::LeftParen => write!(f, "("),
            Token::RightParen => write!(f, ")"),
            Token::LeftBrace => write!(f, "{{"),
            Token::RightBrace => write!(f, "}}"),
            Token::LeftBracket => write!(f, "["),
            Token::RightBracket => write!(f, "]"),
            Token::Comma => write!(f, ","),
            Token::Dot => write!(f, "."),
            Token::Let => write!(f, "let"),
            Token::Struct => write!(f, "struct"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::While => write!(f, "while"),
            Token::For => write!(f, "for"),
            Token::Continue => write!(f, "continue"),
            Token::Break => write!(f, "break"),
            Token::Return => write!(f, "return"),
            Token::Try => write!(f, "try"),
            Token::Catch => write!(f, "catch"),
            Token::New => write!(f, "new"),
            Token::Semicolon => write!(f, ";"),
            Token::Pipe => write!(f, "|"),
            Token::Colon => write!(f, ":"),
            Token::Fn => write!(f, "fn"),
        }
    }
}
