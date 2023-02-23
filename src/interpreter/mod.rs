use std::{
    collections::HashMap,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock, RwLockWriteGuard,
    },
    thread::JoinHandle,
};

use crate::{
    compiler::{common::Spanned, exprs::Expr},
    except,
    interpreter::structs::{StructBuilder, StructDef, StructInstance},
    native_structs::{
        exception::{Exception, ExceptionBuilder, IResult},
        list::ListBuilder,
        socket::SocketBuilder,
        thread::ThreadHandle,
    },
};

use self::{
    method_type::{MethodType, NativeFunc, NativeFuncPtr},
    scope::Scope,
    structs::{StructDefKind, StructInterface},
};

pub mod method_type;
pub mod scope;
pub mod structs;

pub type InstanceMap = Arc<RwLock<HashMap<usize, Arc<RwLock<Box<dyn StructInterface>>>>>>;

pub struct Interpreter {
    scopes: Vec<Scope>,
    pub instances: InstanceMap,
    pub next_id: Arc<AtomicUsize>,
    this: Option<usize>,
}

macro_rules! binary_op_case {
	($self:ident, $lhs:expr, $rhs:expr, $op:tt, $expr:expr, $error:expr) => {
		{
			let lhs = $self.eval($lhs)?;
			let rhs = $self.eval($rhs)?;

			match (lhs, rhs) {
				(Number(lhs), Number(rhs)) => Ok(Number(lhs $op rhs)),
				(Str(lhs), Str(rhs)) => Ok(Str(lhs + &rhs)),
				(lhs, rhs) => {
					except!($expr.clone(), $error, lhs, rhs)
				}
			}
		}
	};
}

pub struct MetaInterpreter {
    instances: InstanceMap,
    next_id: Arc<AtomicUsize>,
}

impl MetaInterpreter {
    pub fn new() -> Self {
        let instances = Arc::new(RwLock::new(HashMap::new()));

        Self {
            instances,
            next_id: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn spawn(&mut self, block: Spanned<Expr>) -> JoinHandle<IResult<Expr>> {
        let instances = self.instances.clone();
        let next_id = self.next_id.clone();
        std::thread::spawn(move || {
            let mut interpreter = Interpreter::new(instances, next_id);
            interpreter.eval_block(&block, HashMap::new())
        })
    }

    // pub fn get_instance(
    //     &self,
    //     id: usize,
    // ) -> RwLockReadGuard<'_, Option<&Box<dyn StructInterface>>> {
    //     self.instances.read().unwrap().get(&id)
    // }

    // pub fn get_instance_mut(&mut self, id: usize) -> Option<&mut Box<dyn StructInterface>> {
    //     self.instances.write().unwrap().get_mut(&id)
    // }

    // pub fn with_instance<U>(
    //     &mut self,
    //     id: usize,
    //     f: impl FnOnce(&mut Box<dyn StructInterface>) -> U,
    // ) -> U {
    //     let mut instances = self.instances.write().unwrap();
    //     let instance = instances.get_mut(&id).unwrap();
    //     f(instance)
    // }

    // pub fn get_next_id(&mut self) -> usize {
    //     let mut next_id = self.next_id.write().unwrap();
    //     let id = *next_id;
    //     *next_id += 1;
    //     id
    // }
}

impl Interpreter {
    pub fn new(instances: InstanceMap, next_id: Arc<AtomicUsize>) -> Self {
        let mut this = Self {
            scopes: vec![Scope::new_empty()],
            instances,
            next_id,
            this: None,
        };

        this.add_standard_library();

        this
    }

    // pub fn get_instance(
    //     &self,
    //     id: usize,
    // ) -> RwLockReadGuard<'_, Option<&Box<dyn StructInterface>>> {
    //     self.instances.read().unwrap().get(&id)
    // }

    // pub fn get_instance_mut(&mut self, id: usize) -> Option<&mut Box<dyn StructInterface>> {
    //     self.instances.write().unwrap().get_mut(&id)
    // }

    pub fn with_instance<U>(
        &mut self,
        id: usize,
        f: impl FnOnce(RwLockWriteGuard<'_, Box<dyn StructInterface>>) -> U,
    ) -> U {
        let instance = {
            let instances = self.instances.read().unwrap();
            instances.get(&id).unwrap().clone()
        };
        let lock = instance.write().unwrap();
        f(lock)
    }

    pub fn add_instance(&mut self, instance: Box<dyn StructInterface>) -> usize {
        let id = self.next_id.fetch_add(1, Ordering::SeqCst);
        self.instances
            .write()
            .unwrap()
            .insert(id, Arc::new(RwLock::new(instance)));
        id
    }

    pub fn with_this<T: StructInterface, U>(&mut self, f: impl FnOnce(&mut T) -> U) -> U {
        let instance = {
            let instances = self.instances.read().unwrap();
            instances.get(&self.this.unwrap()).unwrap().clone()
        };
        let mut this = instance.write().unwrap();
        let this = this.downcast_mut::<T>().unwrap();
        f(this)
    }

    pub fn with_set_this(
        &mut self,
        id: usize,
        f: impl FnOnce(&mut Self) -> IResult<Expr>,
    ) -> IResult<Expr> {
        let old_this = self.this;
        self.this = Some(id);
        let result = f(self);
        self.this = old_this;
        result
    }

    fn add_standard_library(&mut self) {
        self.add_native_function("str", |interpreter, args| {
            if args.len() != 1 {
                return Err(Exception::new("str() takes exactly one argument"));
            }
            let arg = args[0].clone();
            let result = match arg {
                Expr::Str(s) => s,
                Expr::Number(i) => i.to_string(),
                Expr::Bool(b) => b.to_string(),
                Expr::Null => "null".to_owned(),
                Expr::Reference(id) => {
                    let method = interpreter.with_instance(id, |instance| {
                        instance
                            .get_method("__str__")
                            .ok_or_else(|| Exception::new("Invalid reference"))
                    })?;
                    match interpreter.with_set_this(id, |interp| match method {
                        MethodType::Native(f) => f(interp, vec![]),
                        MethodType::UserDefined { args: _, body } => {
                            let mut h = HashMap::new();
                            h.insert("self".to_owned(), Expr::Reference(id));
                            interp.eval_block(&body, h)
                        }
                    })? {
                        Expr::Str(s) => s,
                        _ => return Err(Exception::new("Invalid return type from __str__ method")),
                    }
                }
                _ => return Err(Exception::new("Invalid argument to str()")),
            };
            Ok(Expr::Str(result))
        });

        self.add_native_function("num", |_, args| {
            if args.len() != 1 {
                return Err(Exception::new("num() takes exactly one argument"));
            }
            let arg = args[0].clone();
            let result = match arg {
                Expr::Str(s) => s
                    .parse::<f64>()
                    .map_err(|_| Exception::new(format!("Could not parse \"{s}\" as a number")))?,
                Expr::Number(i) => i,
                Expr::Bool(b) => b as i64 as f64,
                Expr::Null => 0.0,
                _ => return Err(Exception::new("Invalid argument to num()")),
            };
            Ok(Expr::Number(result))
        });

        self.add_native_function("print", |_, args| {
            for arg in args {
                print!("{arg}");
            }
            println!();
            Ok(Expr::Null)
        });

        self.add_native_function("sleep", |_, args| {
            if args.len() != 1 {
                return Err(Exception::new("sleep() takes exactly one argument"));
            }
            let arg = args[0].clone();
            let result = match arg {
                Expr::Number(i) => i,
                _ => return Err(Exception::new("Invalid argument to sleep()")),
            };
            std::thread::sleep(std::time::Duration::from_millis(result as u64));
            Ok(Expr::Null)
        });

        self.add_native_function("spawn", |interpreter, args| {
            if args.len() != 1 {
                return Err(Exception::new("spawn() takes exactly one argument"));
            }
            let arg = args[0].clone();

            let instances = interpreter.instances.clone();
            let next_id = interpreter.next_id.clone();
            let environment = interpreter.clone_environment();
            let thread = std::thread::spawn(move || {
                let mut interpreter = Self::new(instances, next_id);
                interpreter.invoke_lambda(&arg, vec![], environment)
            });

            let thread = Box::new(ThreadHandle::new(thread));
            let id = interpreter.add_instance(thread);
            Ok(Expr::Reference(id))
        });

        self.add_native_struct(
            "Exception",
            StructDefKind::Native(Box::new(ExceptionBuilder {})),
        );

        self.add_native_struct("Socket", StructDefKind::Native(Box::new(SocketBuilder {})));
    }

    fn invoke_lambda(
        &mut self,
        lambda: &Expr,
        _args: Vec<Expr>,
        env: HashMap<String, Expr>,
    ) -> IResult<Expr> {
        match lambda {
            Expr::Lambda {
                arg_names: _,
                body,
                environment: _,
            } => self.eval_block(body, env),
            _ => Err(Exception::new("Invalid lambda")),
        }
    }

    fn get(&self, name: &str) -> Option<&Expr> {
        for scope in self.scopes.iter().rev() {
            if let Some(expr) = scope.get(name) {
                return Some(expr);
            }
        }

        None
    }

    fn set_new(&mut self, name: String, value: Expr) {
        self.scopes.last_mut().unwrap().set(name, value);
    }

    fn set(&mut self, name: String, value: Expr) -> bool {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains(&name) {
                scope.set(name, value);
                return true;
            }
        }
        false
    }

    fn has(&self, name: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if scope.contains(name) {
                return true;
            }
        }
        false
    }

    fn get_struct(&self, name: &str) -> Option<&StructDefKind> {
        for scope in self.scopes.iter().rev() {
            if let Some(struct_def) = scope.get_struct(name) {
                return Some(struct_def);
            }
        }
        None
    }

    fn add_struct(&mut self, name: String, struct_def: StructDefKind) {
        self.scopes.last_mut().unwrap().set_struct(name, struct_def);
    }

    fn clone_environment(&self) -> HashMap<String, Expr> {
        HashMap::from_iter(self.scopes.iter().rev().flat_map(|s| s.locals.clone()))
    }

    fn create_scope(&mut self, locals: HashMap<String, Expr>) {
        let scope = Scope::new(locals);
        self.scopes.push(scope);
    }

    fn remove_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn add_native_function<S: AsRef<str>>(&mut self, name: S, function: NativeFuncPtr) {
        let name = name.as_ref().to_owned();
        self.set_new(
            name.clone(),
            Expr::NativeFunction {
                name,
                function: NativeFunc(function),
            },
        );
    }

    pub fn add_native_struct<S: AsRef<str>>(&mut self, name: S, struct_def: StructDefKind) {
        let name = name.as_ref().to_owned();
        self.add_struct(name, struct_def);
    }

    pub fn eval_block(
        &mut self,
        block: &Spanned<Expr>,
        locals: HashMap<String, Expr>,
    ) -> IResult<Expr> {
        let block = match &block.0 {
            Expr::Block(exprs) => exprs,
            _ => return except!(block.clone(), "Expected block, got {:?}", block.0),
        };

        self.create_scope(locals);
        let mut result = Expr::Null;
        for expr in block {
            result = self.eval(expr)?;
        }
        self.remove_scope();

        Ok(result)
    }

    pub fn eval(&mut self, expr: &Spanned<Expr>) -> IResult<Expr> {
        use Expr::*;
        match &expr.0 {
            // Freestanding blocks are evaluated as if they were expressions
            Block(_) => self.eval_block(expr, HashMap::new()),

            // Literals are evaluated to themselves
            Null | Bool(_) | Number(_) | Str(_) | Reference(_) | NativeFunction { .. } => {
                Ok(expr.0.clone())
            }

            // Lists are a special kind of literal that creates a new object
            ListInitializer { items } => {
                let items: Result<Vec<Expr>, Exception> =
                    items.iter().map(|e| self.eval(e)).collect();
                let items = items? // unfortunately arguments must be named and I'm too lazy to change that
                    .into_iter()
                    .enumerate()
                    .map(|(i, e)| (i.to_string(), e))
                    .collect();
                let list = (ListBuilder {}).construct(items)?;
                let id = self.add_instance(list);
                Ok(Reference(id))
            }

            Lambda {
                arg_names: args,
                body,
                ..
            } => {
                let environ = self.clone_environment();
                Ok(Lambda {
                    arg_names: args.clone(),
                    body: body.clone(),
                    environment: environ,
                })
            }

            // Identifiers
            Ident(name) => {
                if let Some(expr) = self.get(name) {
                    Ok(expr.clone())
                } else {
                    except!(expr.clone(), "Undefined variable '{}'", name)
                }
            }

            // Unary expressions
            Neg(e) => {
                let e = self.eval(e)?;
                match e {
                    Number(n) => Ok(Number(-n)),
                    e => except!(expr.clone(), "Cannot negate {:?}", e),
                }
            }
            Not(e) => {
                let e = self.eval(e)?;
                Ok(Bool(!e.is_truthy()))
            }

            // Binary arithmetic expressions
            Add(lhs, rhs) => binary_op_case!(self, lhs, rhs, +, expr, "Cannot add {:?} and {:?}"),
            Sub(lhs, rhs) => {
                binary_op_case!(self, lhs, rhs, -, expr, "Cannot subtract {:?} from {:?}")
            }
            Mul(lhs, rhs) => {
                binary_op_case!(self, lhs, rhs, *, expr, "Cannot multiply {:?} and {:?}")
            }
            Div(lhs, rhs) => {
                binary_op_case!(self, lhs, rhs, /, expr, "Cannot divide {:?} by {:?}")
            }
            Mod(lhs, rhs) => {
                binary_op_case!(self, lhs, rhs, %, expr, "Cannot modulo {:?} by {:?}")
            }

            // Binary logical expressions
            And(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs.is_truthy() && rhs.is_truthy()))
            }
            Or(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs.is_truthy() || rhs.is_truthy()))
            }

            // Comparison expressions
            EqualsEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs == rhs))
            }
            NotEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                Ok(Bool(lhs != rhs))
            }
            LessThan(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs < rhs)),
                    (lhs, rhs) => {
                        except!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            LessThanEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs <= rhs)),
                    (lhs, rhs) => {
                        except!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            GreaterThan(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs > rhs)),
                    (lhs, rhs) => {
                        except!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            GreaterThanEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs >= rhs)),
                    (lhs, rhs) => {
                        except!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }

            // Variable Assigment
            Let { name, initializer } => {
                let value = self.eval(initializer)?;
                self.set_new(name.clone(), value.clone());
                Ok(value)
            }

            Assign { name, value } => {
                let value = self.eval(value)?;

                if self.has(name) {
                    self.set(name.clone(), value.clone());
                    Ok(value)
                } else {
                    except!(expr.clone(), "Undefined variable '{}'", name)
                }
            }

            // Control flow
            If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.eval(condition)?;

                if condition.is_truthy() {
                    self.eval_block(then_branch, HashMap::new())
                } else {
                    match else_branch {
                        Some(else_branch) => self.eval(else_branch),
                        None => Ok(Expr::Null),
                    }
                }
            }

            While { condition, body } => {
                let mut result = Expr::Null;

                while self.eval(condition)?.is_truthy() {
                    result = self.eval_block(body, HashMap::new())?;
                }
                Ok(result)
            }

            For {
                iteration_variable,
                iterated_expression,
                body,
            } => {
                let iterated_expression = self.eval(iterated_expression)?;

                let mut result = Expr::Null;
                match iterated_expression {
                    Reference(id) => {
                        let iterated_expression =
                            self.with_instance(id, |instance| instance.iter());
                        let mut iterated_expression = match iterated_expression {
                            Some(i) => i,
                            None => {
                                return except!(expr.clone(), "Cannot iterate over {:?}", expr.0)
                            }
                        };

                        let mut iter_locals = HashMap::new();

                        while let Some(e) = iterated_expression.next(self) {
                            iter_locals.insert(iteration_variable.clone(), e);
                            result = self.eval_block(body, iter_locals.clone())?;
                        }
                        Ok(result)
                    }
                    _ => except!(
                        expr.clone(),
                        "Cannot iterate over {:?}",
                        iterated_expression
                    ),
                }
            }

            // Freestanding call
            Call { name, args } => {
                let name = name.0.ident_string();
                let args: IResult<Vec<Expr>> = args.0.iter().map(|a| self.eval(a)).collect();
                let args = args?;

                let function = self.get(&name).cloned();
                if function.is_none() {
                    return except!(expr.clone(), "Undefined variable {}", name);
                };
                let function = function.unwrap();
                match function {
                    Expr::Lambda {
                        arg_names,
                        body,
                        environment,
                    } => {
                        let mut scope = HashMap::new();
                        for (arg_name, arg) in arg_names.iter().zip(args.iter()) {
                            scope.insert(arg_name.clone(), arg.clone());
                        }
                        scope.extend(environment);

                        self.eval_block(&body, scope)
                    }
                    Expr::NativeFunction {
                        name: _name,
                        function,
                    } => {
                        let result = (function.0)(self, args);
                        result.map_err(|e| Exception::new_with_expr(e.message(), expr.clone()))
                    }
                    _ => except!(expr.clone(), "Cannot call {:?}", function),
                }
            }

            // Struct definition
            StructDefinition {
                name,
                fields,
                methods,
            } => {
                let field_map = HashMap::from_iter(fields.iter().map(Clone::clone));
                let mut method_map = HashMap::new();
                for (name, args, body) in methods.iter().cloned() {
                    let method = MethodType::UserDefined { args, body };
                    method_map.insert(name, method);
                }

                self.add_struct(
                    name.clone(),
                    StructDefKind::UserDefined(StructDef {
                        name: name.clone(),
                        fields: field_map,
                        methods: method_map,
                    }),
                );
                Ok(Expr::Null)
            }

            // Struct instantiation
            New { name, args } => {
                let args: Vec<(String, Result<_, _>)> = args
                    .iter()
                    .map(|(name, value)| (name.clone(), self.eval(value)))
                    .collect();
                let args: IResult<Vec<(String, Expr)>> = args
                    .into_iter()
                    .map(|(name, value)| value.map(|value| (name, value)))
                    .collect();
                let args = args?;

                let struct_def = self.get_struct(name).cloned();
                if struct_def.is_none() {
                    return except!(expr.clone(), "Undefined struct {}", name);
                };
                let struct_def = struct_def.unwrap();

                let instance = match struct_def {
                    StructDefKind::UserDefined(struct_def) => {
                        let mut fields = HashMap::new();
                        for (field_name, default) in struct_def.fields.into_iter() {
                            fields.insert(field_name, self.eval(&default)?);
                        }
                        for (field_name, value) in args {
                            fields.insert(field_name.clone(), value);
                        }

                        let mut methods = HashMap::new();
                        for (method_name, method) in struct_def.methods.into_iter() {
                            methods.insert(method_name, method);
                        }

                        Box::new(StructInstance {
                            name: name.clone(),
                            fields,
                            methods,
                        })
                    }
                    StructDefKind::Native(constructor) => {
                        let result = constructor.construct(args);
                        result.map_err(|e| Exception::new_with_expr(e.message(), expr.clone()))?
                    }
                };
                let id = self.add_instance(instance);

                Ok(Expr::Reference(id))
            }

            // Struct field access
            FieldAccess { base, field } => {
                let base = self.eval(base)?;
                match base {
                    Reference(id) => self.with_instance(id, |instance| {
                        let value = instance.get(field);
                        if let Some(value) = value {
                            Ok(value)
                        } else {
                            except!(expr.clone(), "Undefined field {}", field)
                        }
                    }),
                    _ => except!(expr.clone(), "Expected reference, got {:?}", base),
                }
            }

            MethodCall { base, method, args } => {
                let base = self.eval(base)?;
                let params: Result<Vec<Expr>, Exception> =
                    args.iter().map(|p| self.eval(p)).collect();
                let params = params?;
                match base {
                    Reference(id) => {
                        let omethod =
                            self.with_instance(id, |instance| instance.get_method(method));

                        if let Some(method) = omethod {
                            match method {
                                MethodType::Native(func) => {
                                    let result =
                                        self.with_set_this(id, |interp| func(interp, params));
                                    result.map_err(|e| {
                                        Exception::new_with_expr(e.message(), expr.clone())
                                    })
                                }
                                MethodType::UserDefined { args, body } => {
                                    let mut new_vars = HashMap::new();
                                    for (name, val) in args.iter().zip(params.into_iter()) {
                                        new_vars.insert(name.clone(), val);
                                    }
                                    new_vars.insert("self".to_string(), Reference(id));
                                    self.eval_block(&body, new_vars)
                                }
                            }
                        } else {
                            let omethod = self.with_instance(id, |instance| instance.get(method));
                            if let Some(method) = omethod {
                                match method {
                                    Expr::Lambda {
                                        arg_names: args,
                                        body,
                                        environment,
                                    } => {
                                        let mut new_vars = HashMap::new();
                                        for (name, val) in args.iter().zip(params.into_iter()) {
                                            new_vars.insert(name.clone(), val);
                                        }
                                        new_vars.extend(environment);
                                        new_vars.insert("self".to_string(), Reference(id));
                                        self.eval_block(&body, new_vars)
                                    }
                                    _ => except!(
                                        expr.clone(),
                                        "Cannot call {:?} on {:?}",
                                        method,
                                        base
                                    ),
                                }
                            } else {
                                except!(expr.clone(), "Undefined method {} on {:?}", method, base)
                            }
                        }
                    }
                    _ => except!(expr.clone(), "Expected reference, got {:?}", base),
                }
            }

            FieldAssignment { base, field, value } => {
                let base = self.eval(base)?;
                let value = self.eval(value)?;

                match base {
                    Reference(id) => {
                        self.with_instance(id, |mut instance| {
                            instance.set(field, value);
                        });
                        Ok(Expr::Null)
                    }
                    _ => except!(expr.clone(), "Expected reference, got {:?}", base),
                }
            } //_ => except!(expr.clone(), "Not implemented yet: {:?}", expr.0),
        }
    }
}
/*
#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lexer;
    use crate::parser::parser;
    use chumsky::prelude::*;
    use chumsky::Stream;

    #[test]
    fn literals() {
        let input = "1";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(&result);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Expr::Number(1.0));
    }

    #[test]
    fn addition() {
        let input = "1 + 1";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(&result);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Expr::Number(2.0));
    }

    #[test]
    fn error() {
        let input = "1 + \"a\"";
        let tokens = lexer().parse(input).unwrap();
        let len = input.chars().count();
        let (result, errors) =
            parser().parse_recovery(Stream::from_iter(len..len + 1, tokens.into_iter()));
        assert!(errors.is_empty());
        let result = result.unwrap();

        let mut interpreter = Interpreter::new();
        let result = interpreter.eval(&result);
        assert!(result.is_err());
    }
}
*/
