use ariadne::{Color, ColorGenerator, Config, Fmt, Label, Report, ReportKind, Source};
use chumsky::{error::SimpleReason, prelude::*, Stream};

mod common;
mod exprs;
mod interpreter;
mod lexer;
mod parser;
mod token;

use lexer::lexer;
use parser::parser;
use token::Token;

fn show_lexer_errors(input: &str, errors: Vec<Simple<char>>) {
    let mut colors = ColorGenerator::new();

    let a = colors.next();

    let mut report = Report::build(ReportKind::Error, "src.txt", 0);

    for error in errors {
        report = report.with_message("Syntax error").with_label(
            Label::new(("src.txt", error.span()))
                .with_message("Unexpected character")
                .with_color(a),
        );
    }

    report
        .finish()
        .print(("src.txt", Source::from(input)))
        .unwrap();
}

fn show_parser_errors(input: &str, errors: Vec<Simple<Token>>) {
    let mut colors = ColorGenerator::new();

    let a = colors.next();

    let mut report = Report::build(ReportKind::Error, "src.txt", 12);

    for error in errors {
        let mut message = match error.found() {
            None => {
                if let SimpleReason::Unexpected = error.reason() {
                    "Unexpected end of input".to_owned()
                } else {
                    "".to_owned()
                }
            }
            Some(t) => format!("Unexpected token: {t}"),
        };

        if let SimpleReason::Custom(s) = error.reason() {
            message.push_str(&format!(" {s}"));
        }

        let expected = error.expected();
        let len = expected.len();
        for (i, e) in expected.enumerate() {
            if i == 0 {
                message.push_str(", expected ");
            } else if i == len - 1 {
                message.push_str(" or ");
            } else {
                message.push_str(", ");
            }
            let e = match e {
                Some(e) => e.to_string(),
                None => "EOF".to_owned(),
            };
            message.push_str(&e);
        }

        report = report.with_message("Syntax error").with_label(
            Label::new(("src.txt", error.span()))
                .with_message(message)
                .with_color(a),
        );
    }

    report
        .finish()
        .print(("src.txt", Source::from(input)))
        .unwrap();
}

fn show_interpreter_error(input: &str, error: interpreter::Exception) {
    let mut colors = ColorGenerator::new();

    let a = colors.next();

    let mut report = Report::build(ReportKind::Error, "src.txt", 12);

    report = report.with_message("Interpreter error").with_label(
        Label::new(("src.txt", error.expr().1.clone()))
            .with_message(error.message())
            .with_color(a),
    );

    report
        .finish()
        .print(("src.txt", Source::from(input)))
        .unwrap();
}

fn main() {
    let input = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();
    let tokens = lexer().parse(input.clone());
    let result = match tokens {
        Ok(t) => {
            let len = input.chars().count();
            let (result, errors) =
                parser().parse_recovery(Stream::from_iter(len..len + 1, t.into_iter()));
            if errors.is_empty() {
                result.unwrap()
            } else {
                show_parser_errors(&input, errors);
                return;
            }
        }
        Err(e) => {
            show_lexer_errors(&input, e);
            return;
        }
    };

    let mut interpreter = interpreter::Interpreter::new();
    let result = interpreter.eval(&result);
    match result {
        Ok(o) => {
            println!("{o:?}");
        }
        Err(e) => {
            show_interpreter_error(&input, e);
        }
    }
}
