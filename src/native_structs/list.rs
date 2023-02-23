use crate::{
    compiler::exprs::Expr,
    interpreter::{
        method_type::MethodType,
        structs::{Iterable, StructBuilder, StructInterface},
        Interpreter,
    },
};

use super::exception::Exception;

#[derive(Clone)]
pub struct List {
    items: Vec<Expr>,
}

impl List {
    pub fn new(items: Vec<Expr>) -> Self {
        Self { items }
    }

    pub fn push(&mut self, item: Expr) {
        self.items.push(item);
    }

    pub fn get(&self, index: usize) -> Option<Expr> {
        self.items.get(index).cloned()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }
}

impl StructInterface for List {
    fn get_method(&self, name: &str) -> Option<MethodType> {
        match name {
            "push" => Some(MethodType::Native(|interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let item = args[0].clone();
                    this.push(item);
                    Ok(Expr::Null)
                })
            })),
            "get" => Some(MethodType::Native(|interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let index = match args[0] {
                        Expr::Number(n) => n as usize,
                        _ => return Err(Exception::new("Index must be a number")),
                    };
                    this.get(index)
                        .ok_or_else(|| Exception::new("Index out of bounds"))
                })
            })),
            "len" => Some(MethodType::Native(|interpreter, _args| {
                interpreter.with_this(|this: &mut Self| Ok(Expr::Number(this.len() as f64)))
            })),
            _ => None,
        }
    }

    fn iter(&self) -> Option<Box<dyn Iterable>> {
        Some(Box::new(ListIterator::new(self.clone())))
    }
}

#[derive(Clone)]
pub struct ListBuilder {}
impl StructBuilder for ListBuilder {
    fn construct(&self, args: Vec<(String, Expr)>) -> Result<Box<dyn StructInterface>, Exception> {
        let items = args.into_iter().map(|(_, e)| e).collect();
        Ok(Box::new(List::new(items)))
    }
}

pub struct ListIterator {
    list: List,
    index: usize,
}

impl ListIterator {
    pub fn new(list: List) -> Self {
        Self { list, index: 0 }
    }
}

impl Iterable for ListIterator {
    fn next(&mut self, _: &mut Interpreter) -> Option<Expr> {
        let item = self.list.get(self.index);
        self.index += 1;
        item
    }
}
