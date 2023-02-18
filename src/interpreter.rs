use std::collections::HashMap;

use crate::{
    common::{Span, Spanned},
    exprs::Expr,
};

struct Scope {
    locals: HashMap<String, Expr>,
}

#[derive(Debug)]
pub struct Exception {
    message: String,
    expr: Spanned<Expr>,
}

impl Exception {
    fn new(message: String) -> Self {
        Self {
            message,
            expr: (Expr::Null, 0..0),
        }
    }

    fn new_with_expr(message: String, expr: Spanned<Expr>) -> Self {
        Self { message, expr }
    }

    pub fn expr(&self) -> &Spanned<Expr> {
        &self.expr
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for Exception {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Exception(\"{}\")", self.message)
    }
}

macro_rules! exception {
	($e:expr, $fmt_str:literal) => {
		Err(Exception::new_with_expr($fmt_str, $e))
	};

    ($e:expr, $fmt_str:literal, $($args:expr),*) => {
        Err(Exception::new_with_expr(format!($fmt_str, $($args),*), $e))
    };
}

type IResult<T> = Result<T, Exception>;

impl Scope {
    fn new(locals: HashMap<String, Expr>) -> Self {
        Self { locals }
    }

    fn new_empty() -> Self {
        Self::new(HashMap::new())
    }

    fn get(&self, name: &str) -> Option<&Expr> {
        self.locals.get(name)
    }

    fn set(&mut self, name: String, value: Expr) {
        self.locals.insert(name, value);
    }

    fn remove(&mut self, name: &str) {
        self.locals.remove(name);
    }

    fn contains(&self, name: &str) -> bool {
        self.locals.contains_key(name)
    }

    fn extend(&mut self, other: &mut Self) {
        self.locals.extend(other.locals.drain());
    }

    fn extend_with(&mut self, other: &mut Self) {
        self.locals.extend(other.locals.clone());
    }
}

pub struct Interpreter {
    scopes: Vec<Scope>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::new_empty()],
        }
    }

    fn get(&self, name: &str) -> Option<&Expr> {
        for scope in self.scopes.iter().rev() {
            if let Some(expr) = scope.get(name) {
                return Some(expr);
            }
        }

        None
    }

    fn set(&mut self, name: String, value: Expr) {
        self.scopes.last_mut().unwrap().set(name, value);
    }

    fn create_scope(&mut self, locals: HashMap<String, Expr>) {
        self.scopes.push(Scope::new(locals));
    }

    fn remove_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn eval(&mut self, expr: &Spanned<Expr>) -> IResult<Expr> {
        use Expr::*;
        match &expr.0 {
            // Literals are evaluated to themselves
            Null => Ok(Null),
            Bool(b) => Ok(Bool(*b)),
            Number(n) => Ok(Number(*n)),
            Str(s) => Ok(Str(s.clone())),

            // Identifiers
            Ident(name) => {
                if let Some(expr) = self.get(name) {
                    Ok(expr.clone())
                } else {
                    exception!(expr.clone(), "Undefined variable '{}'", name)
                }
            }

            // Binary expressions
            Add(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs + rhs)),
                    (Str(lhs), Str(rhs)) => Ok(Str(lhs + &rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot add {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            Sub(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs - rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot subtract {:?} from {:?}", rhs, lhs)
                    }
                }
            }
            Mul(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs * rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot multiply {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            Div(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs / rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot divide {:?} by {:?}", lhs, rhs)
                    }
                }
            }

            _ => exception!(expr.clone(), "Not implemented yet: {:?}", expr.0),
        }
    }
}

mod tests {
    use super::*;
    use crate::lexer::lexer;
    use crate::parser::parser;
    use chumsky::prelude::*;
    use chumsky::Stream;

    #[test]
    fn test_literals() {
        let input = "1";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(result.get(0).unwrap());
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Expr::Number(1.0));
    }

    #[test]
    fn test_addition() {
        let input = "1 + 1";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(result.get(0).unwrap());
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Expr::Number(2.0));
    }

    #[test]
    fn test_error() {
        let input = "1 + \"a\"";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(result.get(0).unwrap());
        assert!(result.is_err());
    }
}
