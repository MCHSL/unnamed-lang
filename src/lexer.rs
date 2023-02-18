use std::ops::Range;

use chumsky::prelude::*;

use crate::{common::Spanned, token::Token};

pub fn lexer() -> impl Parser<char, Vec<Spanned<Token>>, Error = Simple<char>> {
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
        .map(Token::Str);

    let literal = choice((null, boolean, number, string))
        .map_with_span(|t, s| (t, s))
        .labelled("literal");

    // Identifiers
    let ident = text::ident().map_with_span(|i, s| (Token::Ident(i), s));

    // Operators
    let operator = choice((
        just('+').map(|_| Token::Plus),
        just('-').map(|_| Token::Minus),
        just('*').map(|_| Token::Star),
        just('/').map(|_| Token::Slash),
        just('%').map(|_| Token::Percent),
        just("==").map(|_| Token::EqualsEquals),
        just("!=").map(|_| Token::NotEquals),
        just("<=").map(|_| Token::LessThanEquals),
        just(">=").map(|_| Token::GreaterThanEquals),
        just('<').map(|_| Token::LessThan),
        just('=').map(|_| Token::Equals),
        just('>').map(|_| Token::GreaterThan),
        just("&&").map(|_| Token::And),
        just("||").map(|_| Token::Or),
        just('!').map(|_| Token::Not),
    ))
    .map_with_span(|t, s| (t, s))
    .labelled("operator");

    // Symbols
    let symbol = choice((
        just('(').map(|_| Token::LeftParen),
        just(')').map(|_| Token::RightParen),
        just('{').map(|_| Token::LeftBrace),
        just('}').map(|_| Token::RightBrace),
        just('[').map(|_| Token::LeftBracket),
        just(']').map(|_| Token::RightBracket),
        just(',').map(|_| Token::Comma),
        just('.').map(|_| Token::Dot),
        just(';').map(|_| Token::Semicolon),
    ))
    .map_with_span(|t, s| (t, s))
    .labelled("symbol");

    // Keywords
    let keyword = choice((
        text::keyword("let").map(|_| Token::Let),
        text::keyword("struct").map(|_| Token::Struct),
        text::keyword("if").map(|_| Token::If),
        text::keyword("else").map(|_| Token::Else),
        text::keyword("while").map(|_| Token::While),
        text::keyword("for").map(|_| Token::For),
        text::keyword("continue").map(|_| Token::Continue),
        text::keyword("break").map(|_| Token::Break),
        text::keyword("return").map(|_| Token::Return),
        text::keyword("try").map(|_| Token::Try),
        text::keyword("catch").map(|_| Token::Catch),
    ))
    .map_with_span(|t, s| (t, s))
    .labelled("keyword");

    // Comments
    let line_comment = just("//").then(take_until(text::newline())).ignored();
    let block_comment = just("/*").then(take_until(just("*/"))).ignored();
    let comment = choice((line_comment, block_comment)).padded().repeated();

    // The lexer
    choice((literal, operator, symbol, keyword, ident))
        .padded()
        .padded_by(comment)
        .repeated()
        .then_ignore(end())
        .labelled("lexer")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literals() {
        let input = "null true false 123 123.456 \"hello world\"";
        let tokens: Vec<_> = lexer()
            .parse(input)
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        assert_eq!(
            tokens,
            vec![
                Token::Null,
                Token::Bool(true),
                Token::Bool(false),
                Token::Number(123.0),
                Token::Number(123.456),
                Token::Str("hello world".to_string()),
            ]
        )
    }

    #[test]
    fn identifiers() {
        let input = "foo bar baz";
        let tokens: Vec<_> = lexer()
            .parse(input)
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        assert_eq!(
            tokens,
            vec![
                Token::Ident("foo".to_string()),
                Token::Ident("bar".to_string()),
                Token::Ident("baz".to_string()),
            ]
        )
    }

    #[test]
    fn operators() {
        let input = "+ - * / % == != < <= > >= && || !";
        let tokens: Vec<_> = lexer()
            .parse(input)
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        assert_eq!(
            tokens,
            vec![
                Token::Plus,
                Token::Minus,
                Token::Star,
                Token::Slash,
                Token::Percent,
                Token::EqualsEquals,
                Token::NotEquals,
                Token::LessThan,
                Token::LessThanEquals,
                Token::GreaterThan,
                Token::GreaterThanEquals,
                Token::And,
                Token::Or,
                Token::Not,
            ]
        )
    }

    #[test]
    fn symbols() {
        let input = "( ) { } [ ] , .";
        let tokens: Vec<_> = lexer()
            .parse(input)
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        assert_eq!(
            tokens,
            vec![
                Token::LeftParen,
                Token::RightParen,
                Token::LeftBrace,
                Token::RightBrace,
                Token::LeftBracket,
                Token::RightBracket,
                Token::Comma,
                Token::Dot,
            ]
        )
    }

    #[test]
    fn keywords() {
        let input = "let struct if else while for continue break return try catch";
        let tokens: Vec<_> = lexer()
            .parse(input)
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        assert_eq!(
            tokens,
            vec![
                Token::Let,
                Token::Struct,
                Token::If,
                Token::Else,
                Token::While,
                Token::For,
                Token::Continue,
                Token::Break,
                Token::Return,
                Token::Try,
                Token::Catch,
            ]
        )
    }

    #[test]
    fn comments() {
        let input = "// line comment
		a = 1
		/* block comment */
		b = 2";
        let tokens: Vec<_> = lexer()
            .parse(input)
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::Equals,
                Token::Number(1.0),
                Token::Ident("b".to_string()),
                Token::Equals,
                Token::Number(2.0),
            ]
        )
    }

    #[test]
    fn whitespace() {
        let input = "a = 1



		          b = 2";
        let tokens: Vec<_> = lexer()
            .parse(input)
            .unwrap()
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        assert_eq!(
            tokens,
            vec![
                Token::Ident("a".to_string()),
                Token::Equals,
                Token::Number(1.0),
                Token::Ident("b".to_string()),
                Token::Equals,
                Token::Number(2.0),
            ]
        )
    }

    #[test]
    fn spans() {
        let input = "a = 1";
        let tokens: Vec<_> = lexer().parse(input).unwrap().into_iter().collect();
        assert_eq!(
            tokens,
            vec![
                (Token::Ident("a".to_string()), 0..1),
                (Token::Equals, 2..3),
                (Token::Number(1.0), 4..5),
            ]
        )
    }
}
