use crate::{
    compiler::exprs::{CallableKind, Expr},
    interpreter::{
        method_type::MethodType,
        structs::{Iterable, StructDefinitionInterface, StructInterface},
        Interpreter,
    },
};

use super::exception::Exception;

#[derive(Clone, Debug)]
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
    fn get(&self, name: &str) -> Option<Expr> {
        let val = MethodType::Native(match name {
            "push" => |interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let item = args[0].clone();
                    this.push(item);
                    Ok(Expr::Null)
                })
            },
            "get" => |interpreter, args| {
                interpreter.with_this(|this: &mut Self| {
                    let index = match args[0] {
                        Expr::Number(n) => n as usize,
                        _ => return Err(Exception::new("Index must be a number")),
                    };
                    this.get(index)
                        .ok_or_else(|| Exception::new("Index out of bounds"))
                })
            },
            "len" => |interpreter, _args| {
                interpreter.with_this(|this: &mut Self| Ok(Expr::Number(this.len() as f64)))
            },
            _ => return None,
        });

        Some(Expr::Callable(CallableKind::Method(Box::new(val))))
    }

    fn iter(&self) -> Option<Box<dyn Iterable>> {
        Some(Box::new(ListIterator::new(self.clone())))
    }
}

#[derive(Clone)]
pub struct ListBuilder {}
impl StructDefinitionInterface for ListBuilder {
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
