use std::collections::HashMap;

use crate::compiler::exprs::Expr;

use super::structs::StructDefKind;

#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub locals: HashMap<String, Expr>,
    pub struct_definitions: HashMap<String, StructDefKind>,
}

impl Scope {
    pub fn new(locals: HashMap<String, Expr>) -> Self {
        Self {
            locals,
            struct_definitions: HashMap::new(),
        }
    }

    pub fn new_empty() -> Self {
        Self::new(HashMap::new())
    }

    pub fn get(&self, name: &str) -> Option<&Expr> {
        self.locals.get(name)
    }

    pub fn set(&mut self, name: String, value: Expr) {
        self.locals.insert(name, value);
    }

    pub fn remove(&mut self, name: &str) {
        self.locals.remove(name);
    }

    pub fn contains(&self, name: &str) -> bool {
        self.locals.contains_key(name)
    }

    pub fn extend(&mut self, other: &mut Self) {
        self.locals.extend(other.locals.drain());
    }

    pub fn get_struct(&self, name: &str) -> Option<&StructDefKind> {
        self.struct_definitions.get(name)
    }

    pub fn set_struct(&mut self, name: String, value: StructDefKind) {
        self.struct_definitions.insert(name, value);
    }

    pub fn extend_with(&mut self, other: &Self) {
        self.locals.extend(other.locals.clone());
        self.struct_definitions
            .extend(other.struct_definitions.clone());
    }
}
