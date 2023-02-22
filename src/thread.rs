use crate::{
    exception::Exception,
    exprs::Expr,
    interpreter::{IResult, MethodType},
    structs::StructInterface,
};

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
            Some(handle) => {
                let handle = self.handle.take().unwrap();
                let result = handle.join().unwrap();
                result
            }
            None => Err(Exception::new("Thread already joined")),
        }
    }
}

impl StructInterface for ThreadHandle {
    fn get_method(&self, name: &str) -> Option<MethodType> {
        match name {
            "join" => Some(MethodType::Native(|interpreter, _args| {
                interpreter.with_this(|this: &mut Self| this.join())
            })),
            _ => None,
        }
    }
}
