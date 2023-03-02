use std::collections::HashMap;

use crate::{
    compiler::exprs::Expr,
    interpreter::{
        method_type::MethodType,
        structs::{StructDefKind, StructInterface},
        Interpreter,
    },
};

#[derive(Debug)]
pub struct Module {
    pub interpreter: Interpreter,
    pub file: String,
    pub fields: HashMap<String, Expr>,
}

impl Module {
    pub fn new(interpreter: Interpreter, file: String, fields: HashMap<String, Expr>) -> Self {
        Self {
            interpreter,
            file,
            fields,
        }
    }
}

impl StructInterface for Module {
    fn get(&self, name: &str) -> Option<Expr> {
        self.fields.get(name).cloned()
    }
}
