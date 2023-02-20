use std::collections::HashMap;

use downcast_rs::{impl_downcast, Downcast};
use dyn_clone::{clone_trait_object, DynClone};

use crate::{common::Spanned, exception::Exception, exprs::Expr, interpreter::MethodType};

#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    pub name: String,
    pub fields: HashMap<String, Spanned<Expr>>,
    pub methods: HashMap<String, MethodType>,
}

#[derive(Clone)]
pub enum StructDefKind {
    Native(Box<dyn StructBuilder>),
    UserDefined(StructDef),
}

impl std::fmt::Debug for StructDefKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Native(_) => write!(f, "Native"),
            Self::UserDefined(def) => write!(f, "UserDefined {{ {:#?} }}", def),
        }
    }
}

impl PartialEq for StructDefKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Native(f), Self::Native(g)) => std::ptr::eq(f as *const _, g as *const _),
            (Self::UserDefined(f), Self::UserDefined(g)) => f == g,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructInstance {
    pub name: String,
    pub fields: HashMap<String, Expr>,
    pub methods: HashMap<String, MethodType>,
}

pub trait StructInterface: Downcast {
    fn get(&self, name: &str) -> Option<Expr>;
    fn set(&mut self, name: &str, value: Expr);
    fn get_method(&self, name: &str) -> Option<MethodType>;
}

impl_downcast!(StructInterface);

impl StructInterface for StructInstance {
    fn get(&self, name: &str) -> Option<Expr> {
        self.fields.get(name).cloned()
    }

    fn set(&mut self, name: &str, value: Expr) {
        self.fields.insert(name.to_owned(), value);
    }

    fn get_method(&self, name: &str) -> Option<MethodType> {
        self.methods.get(name).cloned()
    }
}

pub trait StructBuilder: DynClone {
    fn construct(&self, args: Vec<(String, Expr)>) -> Result<Box<dyn StructInterface>, Exception>;
}

clone_trait_object!(StructBuilder);
