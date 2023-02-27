use std::collections::HashMap;

use crate::{
    compiler::exprs::Expr,
    interpreter::{
        method_type::MethodType,
        structs::{StructDefKind, StructInterface},
    },
};

pub struct Module {
    file: String,
    fields: HashMap<String, Expr>,
}

impl Module {
    pub fn new(file: String, fields: HashMap<String, Expr>) -> Self {
        Self { file, fields }
    }
}

impl StructInterface for Module {
    fn get(&self, name: &str) -> Option<Expr> {
        self.fields.get(name).cloned()
    }

    fn get_method(&self, name: &str) -> Option<MethodType> {
        None
    }
}
