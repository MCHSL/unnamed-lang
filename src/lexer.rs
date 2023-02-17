use chumsky::prelude::*;

use crate::token::Token;

pub fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    // Literals
    let null = text::keyword("null").map(|_| Token::Null);
    let true_ = text::keyword("true").map(|_| Token::Bool(true));
    let false_ = text::keyword("false").map(|_| Token::Bool(false));
    let boolean = choice((true_, false_));
    let number = text::digits(10)
        .chain::<char, _, _>(just('.').chain(text::digits(10)).or_not())
        .collect()
        .map(|s: String| s.parse::<f64>().unwrap())
        .map(Token::Number);
    let string = just('"')
        .ignore_then(filter(|c| *c != '"').repeated())
        .then_ignore(just('"'))
        .collect()
        .map(Token::String);

    let literal = choice((null, boolean, number, string)).labelled("literal");

    // Identifiers
    let ident = text::ident().map(Token::Ident);

    // Operators
    let plus = just('+').map(|_| Token::Plus);
    let minus = just('-').map(|_| Token::Minus);
    let star = just('*').map(|_| Token::Star);
    let slash = just('/').map(|_| Token::Slash);
    let percent = just('%').map(|_| Token::Percent);
    let equals = just('=').map(|_| Token::Equals);
    let equals_equals = text::keyword("==").map(|_| Token::EqualsEquals);
    let not_equals = text::keyword("!=").map(|_| Token::NotEquals);
    let less_than = just('<').map(|_| Token::LessThan);
    let less_than_equals = text::keyword("<=").map(|_| Token::LessThanEquals);
    let greater_than = just('>').map(|_| Token::GreaterThan);
    let greater_than_equals = text::keyword(">=").map(|_| Token::GreaterThanEquals);
    let and = text::keyword("&&").map(|_| Token::And);
    let or = text::keyword("||").map(|_| Token::Or);
    let not = text::keyword("!").map(|_| Token::Not);

    let operator = choice((
        plus,
        minus,
        star,
        slash,
        percent,
        equals,
        equals_equals,
        not_equals,
        less_than,
        less_than_equals,
        greater_than,
        greater_than_equals,
        and,
        or,
        not,
    ))
    .labelled("operator");

    // Symbols
    let left_paren = just('(').map(|_| Token::LeftParen);
    let right_paren = just(')').map(|_| Token::RightParen);
    let left_brace = just('{').map(|_| Token::LeftBrace);
    let right_brace = just('}').map(|_| Token::RightBrace);
    let left_bracket = just('[').map(|_| Token::LeftBracket);
    let right_bracket = just(']').map(|_| Token::RightBracket);
    let comma = just(',').map(|_| Token::Comma);
    let dot = just('.').map(|_| Token::Dot);

    let symbol = choice((
        left_paren,
        right_paren,
        left_brace,
        right_brace,
        left_bracket,
        right_bracket,
        comma,
        dot,
    ))
    .labelled("symbol");

    // Keywords
    let let_ = text::keyword("let").map(|_| Token::Let);
    let struct_ = text::keyword("struct").map(|_| Token::Struct);
    let if_ = text::keyword("if").map(|_| Token::If);
    let else_ = text::keyword("else").map(|_| Token::Else);
    let while_ = text::keyword("while").map(|_| Token::While);
    let for_ = text::keyword("for").map(|_| Token::For);
    let continue_ = text::keyword("continue").map(|_| Token::Continue);
    let break_ = text::keyword("break").map(|_| Token::Break);
    let return_ = text::keyword("return").map(|_| Token::Return);
    let try_ = text::keyword("try").map(|_| Token::Try);
    let catch = text::keyword("catch").map(|_| Token::Catch);

    let keyword = choice((
        let_, struct_, if_, else_, while_, for_, continue_, break_, return_, try_, catch,
    ))
    .labelled("keyword");

    // Comments
    let line_comment = text::keyword("//").map(|_| Token::LineComment);
    let block_comment_start = text::keyword("/*").map(|_| Token::BlockCommentStart);
    let block_comment_end = text::keyword("*/").map(|_| Token::BlockCommentEnd);

    let comment =
        choice((line_comment, block_comment_start, block_comment_end)).labelled("comment");

    // The lexer
    choice((literal, ident, operator, symbol, keyword, comment))
        .padded()
        .repeated()
        .labelled("lexer")
}
