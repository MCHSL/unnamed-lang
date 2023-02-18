use std::collections::HashMap;

use crate::{common::Spanned, exprs::Expr};

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

    fn set_new(&mut self, name: String, value: Expr) {
        self.scopes.last_mut().unwrap().set(name, value);
    }

    fn set(&mut self, name: String, value: Expr) -> bool {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains(&name) {
                scope.set(name, value);
                return true;
            }
        }
        false
    }

    fn has(&self, name: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if scope.contains(name) {
                return true;
            }
        }
        false
    }

    fn create_scope(&mut self, locals: HashMap<String, Expr>) {
        self.scopes.push(Scope::new(locals));
    }

    fn remove_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn eval_block(
        &mut self,
        block: &Spanned<Expr>,
        locals: HashMap<String, Expr>,
    ) -> IResult<Expr> {
        let block = match &block.0 {
            Expr::Block(exprs) => exprs,
            _ => return exception!(block.clone(), "Expected block, got {:?}", block.0),
        };

        self.create_scope(locals);
        let mut result = Expr::Null;
        for expr in block {
            result = self.eval(expr)?;
        }
        self.remove_scope();

        Ok(result)
    }

    pub fn eval(&mut self, expr: &Spanned<Expr>) -> IResult<Expr> {
        use Expr::*;
        match &expr.0 {
            // Freestanding blocks are evaluated as if they were expressions
            Block(_) => self.eval_block(expr, HashMap::new()),

            // Literals are evaluated to themselves
            Null | Bool(_) | Number(_) | Str(_) | List(_) | Lambda { .. } => Ok(expr.0.clone()),

            // Identifiers
            Ident(name) => {
                if let Some(expr) = self.get(name) {
                    Ok(expr.clone())
                } else {
                    exception!(expr.clone(), "Undefined variable '{}'", name)
                }
            }

            // Unary expressions
            Neg(e) => {
                let e = self.eval(e)?;
                match e {
                    Number(n) => Ok(Number(-n)),
                    e => exception!(expr.clone(), "Cannot negate {:?}", e),
                }
            }
            Not(e) => {
                let e = self.eval(e)?;
                Ok(Bool(!e.is_truthy()))
            }

            // Binary arithmetic expressions
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
            Mod(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs % rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot modulo {:?} by {:?}", lhs, rhs)
                    }
                }
            }

            // Binary logical expressions
            And(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs.is_truthy() && rhs.is_truthy()))
            }
            Or(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs.is_truthy() || rhs.is_truthy()))
            }

            // Comparison expressions
            EqualsEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs == rhs))
            }
            NotEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs != rhs))
            }
            LessThan(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs < rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            LessThanEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs <= rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            GreaterThan(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs > rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            GreaterThanEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs >= rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }

            // Variable Assigment
            Let { name, initializer } => {
                let value = self.eval(initializer)?;
                self.set_new(name.clone(), value.clone());
                Ok(value)
            }

            Assign { name, value } => {
                let value = self.eval(value)?;

                if self.has(name) {
                    self.set(name.clone(), value.clone());
                    Ok(value)
                } else {
                    exception!(expr.clone(), "Undefined variable '{}'", name)
                }
            }

            // Control flow
            If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.eval(condition)?;

                if condition.is_truthy() {
                    self.eval_block(then_branch, HashMap::new())
                } else {
                    match else_branch {
                        Some(else_branch) => self.eval(else_branch),
                        None => Ok(Expr::Null),
                    }
                }
            }

            While { condition, body } => {
                let mut result = Expr::Null;

                while self.eval(condition)?.is_truthy() {
                    result = self.eval_block(body, HashMap::new())?;
                }
                Ok(result)
            }

            For {
                iteration_variable,
                iterated_expression,
                body,
            } => {
                let iterated_expression = self.eval(iterated_expression)?;

                let mut result = Expr::Null;
                match iterated_expression {
                    Expr::List(list) => {
                        for item in list.iter() {
                            let mut scope = HashMap::new();
                            scope.insert(iteration_variable.clone(), self.eval(item)?);
                            result = self.eval_block(body, scope)?;
                        }
                        Ok(result)
                    }
                    _ => exception!(
                        expr.clone(),
                        "Cannot iterate over {:?}",
                        iterated_expression
                    ),
                }
            }

            // Freestanding call
            Call { name, args } => {
                let name = name.0.ident_string();
                let args: IResult<Vec<Expr>> = args.0.iter().map(|a| self.eval(a)).collect();
                let args = args?;

                let function = self.get(&name).cloned();
                if function.is_none() {
                    return exception!(expr.clone(), "Undefined variable {}", name);
                };
                let function = function.unwrap();
                let (arg_names, body) = match function {
                    Expr::Lambda { args, body } => (args, body),
                    _ => return exception!(expr.clone(), "Cannot call {:?}", function),
                };

                let mut scope = HashMap::new();
                for (arg_name, arg) in arg_names.iter().zip(args.iter()) {
                    scope.insert(arg_name.clone(), arg.clone());
                }

                self.eval_block(&body, scope)
            }

            _ => exception!(expr.clone(), "Not implemented yet: {:?}", expr.0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lexer;
    use crate::parser::parser;
    use chumsky::prelude::*;
    use chumsky::Stream;

    #[test]
    fn literals() {
        let input = "1";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(&result);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Expr::Number(1.0));
    }

    #[test]
    fn addition() {
        let input = "1 + 1";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(&result);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Expr::Number(2.0));
    }

    #[test]
    fn error() {
        let input = "1 + \"a\"";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(&result);
        assert!(result.is_err());
    }
}
