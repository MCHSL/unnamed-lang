use std::collections::HashSet;

use chumsky::prelude::*;

use crate::{
    common::{Span, Spanned},
    exprs::Expr,
    token::Token,
};

pub fn parser() -> impl Parser<Token, Spanned<Expr>, Error = Simple<Token>> {
    let ident =
        select! { |span| Token::Ident(ident) => (Expr::Ident(ident), span) }.labelled("identifier");

    // let ident = any().try_map(|t, span| match t {
    //     Token::Ident(ident) => Ok((Expr::Ident(ident), span)),
    //     t => Err(Simple::custom(
    //         span,
    //         format!("Expected identifier, got {t}"),
    //     )),
    // });

    let statement = recursive(|stmt| {
        let block = just(Token::LeftBrace)
            .ignore_then(stmt.repeated())
            .then_ignore(just(Token::RightBrace))
            .map_with_span(|stmts, span: Span| (Expr::Block(stmts), span))
            .labelled("block");

        let expression = recursive(|expr| {
            let argument_list = expr
                .clone()
                .separated_by(just(Token::Comma))
                .delimited_by(just(Token::LeftParen), just(Token::RightParen))
                .map_with_span(|exprs, span: Span| (exprs, span))
                .labelled("argument_list");

            let literal = select! {
                Token::Null => Expr::Null,
                Token::Bool(b) => Expr::Bool(b),
                Token::Number(n) => Expr::Number(n),
                Token::Str(s) => Expr::Str(s),
            }
            .map_with_span(|expr, span: Span| (expr, span))
            .labelled("literal");

            let paren_expression = expr
                .clone()
                .delimited_by(just(Token::LeftParen), just(Token::RightParen))
                .labelled("paren_expression");

            let if_ = just(Token::If)
                .map_with_span(|_, span: Span| ((), span))
                .then(expr.clone())
                .then(block.clone())
                .then(just(Token::Else).ignore_then(block.clone()).or_not())
                .map_with_span(
                    |(((((), if_span), condition), then), else_), else_span: Span| {
                        (
                            Expr::If {
                                condition: Box::new(condition),
                                then_branch: Box::new(then),
                                else_branch: else_.map(Box::new),
                            },
                            if_span.start()..else_span.end(),
                        )
                    },
                );

            let while_ = just(Token::While)
                .map_with_span(|_, span: Span| ((), span))
                .then(expr.clone())
                .then(block.clone())
                .map_with_span(|((((), while_span), condition), body), body_span: Span| {
                    (
                        Expr::While {
                            condition: Box::new(condition),
                            body: Box::new(body),
                        },
                        while_span.start()..body_span.end(),
                    )
                });

            let atom = choice((literal, paren_expression, if_, while_, block.clone(), ident));

            let call = atom
                .clone()
                .then(argument_list.repeated())
                .foldl(|lhs, rhs| {
                    let span = lhs.1.start()..rhs.1.end();
                    (
                        Expr::Call {
                            name: Box::new(lhs),
                            args: (rhs.0.into_iter().map(Box::new).collect(), rhs.1),
                        },
                        span,
                    )
                });

            let unary = just(Token::Minus)
                .or(just(Token::Not))
                .map_with_span(|op, span: Span| (op, span))
                .repeated()
                .then(call.clone())
                .foldr(|op, atom| match op {
                    (Token::Minus, t_span) => (
                        Expr::Neg(Box::new(atom.clone())),
                        t_span.start()..atom.1.end(),
                    ),
                    (Token::Not, t_span) => (
                        Expr::Not(Box::new(atom.clone())),
                        t_span.start()..atom.1.end(),
                    ),
                    _ => unreachable!(),
                });

            let product = unary
                .clone()
                .then(
                    just(Token::Star)
                        .or(just(Token::Slash))
                        .then(unary)
                        .repeated(),
                )
                .foldl(|lhs, (op, rhs)| match op {
                    Token::Star => {
                        let span = lhs.1.start()..rhs.1.end();
                        (Expr::Mul(Box::new(lhs), Box::new(rhs)), span)
                    }
                    Token::Slash => {
                        let span = lhs.1.start()..rhs.1.end();
                        (Expr::Div(Box::new(lhs), Box::new(rhs)), span)
                    }

                    _ => unreachable!(),
                })
                .labelled("product");

            let sum = product
                .clone()
                .then(
                    just(Token::Plus)
                        .or(just(Token::Minus))
                        .then(product)
                        .repeated(),
                )
                .foldl(|lhs, (op, rhs)| match op {
                    Token::Plus => {
                        let span = lhs.1.start()..rhs.1.end();
                        (Expr::Add(Box::new(lhs), Box::new(rhs)), span)
                    }
                    Token::Minus => {
                        let span = lhs.1.start()..rhs.1.end();
                        (Expr::Sub(Box::new(lhs), Box::new(rhs)), span)
                    }
                    _ => unreachable!(),
                });

            let comparison = sum
                .clone()
                .then(
                    just(Token::EqualsEquals)
                        .or(just(Token::NotEquals))
                        .or(just(Token::LessThan))
                        .or(just(Token::GreaterThan))
                        .or(just(Token::LessThanEquals))
                        .or(just(Token::GreaterThanEquals))
                        .then(sum)
                        .repeated(),
                )
                .foldl(|lhs, (op, rhs)| {
                    let span = lhs.1.start()..rhs.1.end();
                    (
                        match op {
                            Token::EqualsEquals => Expr::EqualsEquals,
                            Token::NotEquals => Expr::NotEquals,
                            Token::LessThan => Expr::LessThan,
                            Token::GreaterThan => Expr::GreaterThan,
                            Token::LessThanEquals => Expr::LessThanEquals,
                            Token::GreaterThanEquals => Expr::GreaterThanEquals,
                            _ => unreachable!(),
                        }(Box::new(lhs), Box::new(rhs)),
                        span,
                    )
                })
                .labelled("comparison");

            let logicals = comparison
                .clone()
                .then(
                    just(Token::And)
                        .or(just(Token::Or))
                        .then(comparison)
                        .repeated(),
                )
                .foldl(|lhs, (op, rhs)| {
                    let span = lhs.1.start()..rhs.1.end();
                    (
                        match op {
                            Token::And => Expr::And,
                            Token::Or => Expr::Or,
                            _ => unreachable!(),
                        }(Box::new(lhs), Box::new(rhs)),
                        span,
                    )
                })
                .labelled("and_or");

            let assignment = ident
                .clone()
                .then_ignore(just(Token::Equals))
                .then(logicals.clone())
                .map(|(name, value)| {
                    let span = name.1.start()..value.1.end();
                    (
                        Expr::Assign {
                            name: name.0.ident_string(),
                            value: Box::new(value),
                        },
                        span,
                    )
                });

            choice((assignment, logicals))
        });

        let let_ = just(Token::Let)
            .map_with_span(|_, span: Span| ((), span))
            .then(ident)
            .then_ignore(just(Token::Equals))
            .then(expression.clone())
            .map_with_span(
                |(((_, let_span), (name, _name_span)), initializer), init_span: Span| {
                    (
                        Expr::Let {
                            name: name.ident_string(),
                            initializer: Box::new(initializer),
                        },
                        let_span.start()..init_span.end(),
                    )
                },
            );

        choice((let_, expression)).then_ignore(just(Token::Semicolon).or_not())
    });

    statement
        .repeated()
        .then_ignore(end())
        .map_with_span(|stmts, span: Span| (Expr::Block(stmts), span))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lexer;
    use chumsky::Stream;

    #[test]
    fn simple_parser() {
        use Token::*;
        let input = "1 + 2 * 3";
        let tokens = vec![
            (Number(1.0), 0..1),
            (Plus, 2..3),
            (Number(2.0), 4..5),
            (Star, 6..7),
            (Number(3.0), 8..9),
        ];
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap().0;
        assert_eq!(
            result,
            Expr::Block(vec![(
                Expr::Add(
                    Box::new((Expr::Number(1.0), 0..1usize)),
                    Box::new((
                        Expr::Mul(
                            Box::new((Expr::Number(2.0), 4..5usize)),
                            Box::new((Expr::Number(3.0), 8..9usize))
                        ),
                        4..9usize
                    ))
                ),
                0..9usize
            )])
        );
    }
}
