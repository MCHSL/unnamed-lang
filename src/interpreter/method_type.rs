use crate::{
    compiler::{common::Spanned, exprs::Expr},
    native_structs::exception::Exception,
};

use super::Interpreter;

pub type NativeFuncPtr = fn(&mut Interpreter, Vec<Expr>) -> Result<Expr, Exception>;

#[derive(Clone)]
pub struct NativeFunc(pub NativeFuncPtr);
pub type NativeMethod = fn(&mut Interpreter, Vec<Expr>) -> Result<Expr, Exception>;

impl PartialEq for NativeFunc {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self as *const _, other as *const _)
    }
}

impl std::fmt::Debug for NativeFunc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NativeFunc ({:p})", self.0 as *const ())
    }
}

#[derive(Clone)]
pub enum MethodType {
    Native(NativeMethod),
    UserDefined {
        args: Vec<String>,
        body: Spanned<Expr>,
    },
}

impl PartialEq for MethodType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Native(f), Self::Native(g)) => std::ptr::eq(f as *const _, g as *const _),
            (
                Self::UserDefined { args, body },
                Self::UserDefined {
                    args: args2,
                    body: body2,
                },
            ) => args == args2 && body == body2,
            _ => false,
        }
    }
}

impl std::fmt::Debug for MethodType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Native(_) => write!(f, "Native"),
            Self::UserDefined { args, body } => {
                write!(f, "UserDefined {{ args: {args:?}, body: {body:?} }}")
            }
        }
    }
}
