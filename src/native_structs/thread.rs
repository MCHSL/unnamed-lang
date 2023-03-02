use crate::{
    compiler::exprs::{CallableKind, Expr},
    interpreter::{method_type::MethodType, structs::StructInterface},
};

use super::exception::{Exception, IResult};

#[derive(Debug)]
pub struct ThreadHandle {
    handle: Option<std::thread::JoinHandle<IResult<Expr>>>,
}

impl ThreadHandle {
    pub fn new(handle: std::thread::JoinHandle<IResult<Expr>>) -> Self {
        Self {
            handle: Some(handle),
        }
    }

    pub fn join(&mut self) -> IResult<Expr> {
        match &mut self.handle {
            Some(_) => {
                let handle = self.handle.take().unwrap();
                let result = handle.join().unwrap();
                result
            }
            None => Err(Exception::new("Thread already joined")),
        }
    }
}

impl StructInterface for ThreadHandle {
    fn get(&self, name: &str) -> Option<Expr> {
        match name {
            "join" => Some(Expr::Callable(CallableKind::Method(Box::new(
                MethodType::Native(|interpreter, _args| {
                    interpreter.with_this(|this: &mut Self| this.join())
                }),
            )))),
            _ => None,
        }
    }
}
