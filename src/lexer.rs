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
    let plus = just('+').map(|_| Token::Plus);
    let minus = just('-').map(|_| Token::Minus);
    let star = just('*').map(|_| Token::Star);
    let slash = just('/').map(|_| Token::Slash);
    let percent = just('%').map(|_| Token::Percent);
    let equals_equals = just("==").map(|_| Token::EqualsEquals);
    let not_equals = just("!=").map(|_| Token::NotEquals);
    let less_than_equals = just("<=").map(|_| Token::LessThanEquals);
    let greater_than_equals = just(">=").map(|_| Token::GreaterThanEquals);
    let less_than = just('<').map(|_| Token::LessThan);
    let equals = just('=').map(|_| Token::Equals);
    let greater_than = just('>').map(|_| Token::GreaterThan);
    let and = just("&&").map(|_| Token::And);
    let or = just("||").map(|_| Token::Or);
    let not = just('!').map(|_| Token::Not);

    let operator = choice((
        plus,
        minus,
        star,
        slash,
        percent,
        equals_equals,
        not_equals,
        less_than_equals,
        greater_than_equals,
        less_than,
        greater_than,
        equals,
        and,
        or,
        not,
    ))
    .map_with_span(|t, s| (t, s))
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
    .map_with_span(|t, s| (t, s))
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

mod tests {
    use super::*;

    #[test]
    fn test_literals() {
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
    fn test_identifiers() {
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
    fn test_operators() {
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
    fn test_symbols() {
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
    fn test_keywords() {
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
    fn test_comments() {
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
    fn test_whitespace() {
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
    fn test_spans() {
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
