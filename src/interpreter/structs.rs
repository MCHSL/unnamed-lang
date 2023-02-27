use std::collections::HashMap;

use downcast_rs::{impl_downcast, Downcast};
use dyn_clone::{clone_trait_object, DynClone};

use crate::{
    compiler::{common::Spanned, exprs::Expr},
    native_structs::exception::Exception,
};

use super::{method_type::MethodType, Interpreter};

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
            Self::UserDefined(def) => write!(f, "UserDefined {{ {def:#?} }}"),
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

pub trait StructInterface: Downcast + Send + Sync {
    fn type_name(&self) -> String {
        std::any::type_name::<Self>().to_owned()
    }
    fn get(&self, _name: &str) -> Option<Expr> {
        None
    }
    fn set(&mut self, _name: &str, _value: Expr) {}
    fn get_method(&self, name: &str) -> Option<MethodType>;
    fn iter(&self) -> Option<Box<dyn Iterable>> {
        None
    }
}

impl_downcast!(StructInterface);

impl StructInterface for StructInstance {
    fn type_name(&self) -> String {
        self.name.clone()
    }

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

pub trait StructBuilder: DynClone + Send + Sync {
    fn construct(&self, args: Vec<(String, Expr)>) -> Result<Box<dyn StructInterface>, Exception>;
}

clone_trait_object!(StructBuilder);

pub trait Iterable {
    fn next(&mut self, interpreter: &mut Interpreter) -> Option<Expr>;
}
