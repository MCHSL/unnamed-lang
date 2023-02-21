use crate::{
    common::Spanned,
    exprs::Expr,
    interpreter::MethodType,
    structs::{StructBuilder, StructInterface},
};

#[derive(Debug)]
pub struct Exception {
    message: String,
    expr: Spanned<Expr>,
}

impl Exception {
    pub fn new<S: AsRef<str>>(message: S) -> Self {
        Self {
            message: message.as_ref().to_owned(),
            expr: (Expr::Null, 0..0),
        }
    }

    pub fn new_with_expr<S: AsRef<str>>(message: S, expr: Spanned<Expr>) -> Self {
        Self {
            message: message.as_ref().to_owned(),
            expr,
        }
    }

    pub fn expr(&self) -> &Spanned<Expr> {
        &self.expr
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn __str__(&mut self) -> Result<Expr, Self> {
        Ok(Expr::Str(self.message.clone()))
    }
}

impl std::fmt::Display for Exception {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Exception(\"{}\")", self.message)
    }
}

#[macro_export]
macro_rules! except {
	($e:expr, $fmt_str:literal) => {
		Err(Exception::new_with_expr($fmt_str, $e))
	};

    ($e:expr, $fmt_str:literal, $($args:expr),*) => {
        Err(Exception::new_with_expr(format!($fmt_str, $($args),*), $e))
    };
}

impl StructInterface for Exception {
    fn get(&self, name: &str) -> Option<Expr> {
        match name {
            "message" => Some(Expr::Str(self.message.clone())),
            _ => None,
        }
    }

    fn set(&mut self, name: &str, _value: Expr) {
        if name == "message" {
            panic!("Cannot set `message` on Exception");
        }
    }

    fn get_method(&self, name: &str) -> Option<MethodType> {
        match name {
            "__str__" => Some(MethodType::Native(|interpreter, _args| {
                interpreter.with_this(|this: &mut Self| this.__str__())
            })),
            _ => None,
        }
    }
}

#[derive(Clone)]
pub struct ExceptionBuilder {}
impl StructBuilder for ExceptionBuilder {
    fn construct(&self, args: Vec<(String, Expr)>) -> Result<Box<dyn StructInterface>, Exception> {
        let arg = args
            .get(0)
            .ok_or_else(|| Exception::new("Expected string or null"))?;

        if arg.0 != "message" {
            return Err(Exception::new("Missing `message` argument"));
        }

        let message = match &arg.1 {
            Expr::Str(s) => s.clone(),
            Expr::Null => String::new(),
            _ => return Err(Exception::new("Expected string or null")),
        };

        Ok(Box::new(Exception::new(message)))
    }
}
