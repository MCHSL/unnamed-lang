use std::collections::HashMap;

use crate::{common::Spanned, exprs::Expr};

pub type NativeFunc = fn(&mut Interpreter, Vec<Expr>) -> Result<Expr, Exception>;
pub type NativeMethod = fn(&mut StructInstance, Vec<Expr>) -> Result<Expr, Exception>;

#[derive(Clone)]
pub enum MethodType {
    Native(NativeMethod),
    UserDefined {
        args: Vec<String>,
        body: Spanned<Expr>,
    },
}

impl std::fmt::Debug for MethodType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Native(_) => write!(f, "Native"),
            Self::UserDefined { args, body } => {
                write!(f, "UserDefined {{ args: {:?}, body: {:?} }}", args, body)
            }
        }
    }
}

#[derive(Debug, Clone)]
struct StructDef {
    name: String,
    fields: HashMap<String, Spanned<Expr>>,
    methods: HashMap<String, MethodType>,
}

#[derive(Debug, Clone)]
struct StructInstance {
    name: String,
    fields: HashMap<String, Expr>,
    methods: HashMap<String, MethodType>,
}

struct Scope {
    locals: HashMap<String, Expr>,
    struct_definitions: HashMap<String, StructDef>,
}

#[derive(Debug)]
pub struct Exception {
    message: String,
    expr: Spanned<Expr>,
}

impl Exception {
    fn new(message: String) -> Self {
        Self {
            message,
            expr: (Expr::Null, 0..0),
        }
    }

    fn new_with_expr(message: String, expr: Spanned<Expr>) -> Self {
        Self { message, expr }
    }

    pub fn expr(&self) -> &Spanned<Expr> {
        &self.expr
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for Exception {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Exception(\"{}\")", self.message)
    }
}

macro_rules! exception {
	($e:expr, $fmt_str:literal) => {
		Err(Exception::new_with_expr($fmt_str, $e))
	};

    ($e:expr, $fmt_str:literal, $($args:expr),*) => {
        Err(Exception::new_with_expr(format!($fmt_str, $($args),*), $e))
    };
}

type IResult<T> = Result<T, Exception>;

impl Scope {
    fn new(locals: HashMap<String, Expr>) -> Self {
        Self {
            locals,
            struct_definitions: HashMap::new(),
        }
    }

    fn new_empty() -> Self {
        Self::new(HashMap::new())
    }

    fn get(&self, name: &str) -> Option<&Expr> {
        self.locals.get(name)
    }

    fn set(&mut self, name: String, value: Expr) {
        self.locals.insert(name, value);
    }

    fn remove(&mut self, name: &str) {
        self.locals.remove(name);
    }

    fn contains(&self, name: &str) -> bool {
        self.locals.contains_key(name)
    }

    fn extend(&mut self, other: &mut Self) {
        self.locals.extend(other.locals.drain());
    }

    fn extend_with(&mut self, other: &mut Self) {
        self.locals.extend(other.locals.clone());
    }
}

pub struct Interpreter {
    scopes: Vec<Scope>,
    instances: HashMap<usize, StructInstance>,
    next_id: usize,
}

impl Interpreter {
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::new_empty()],
            instances: HashMap::new(),
            next_id: 0,
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

    fn create_scope(&mut self, locals: HashMap<String, Expr>) {
        self.scopes.push(Scope::new(locals));
    }

    fn remove_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn eval_block(
        &mut self,
        block: &Spanned<Expr>,
        locals: HashMap<String, Expr>,
    ) -> IResult<Expr> {
        let block = match &block.0 {
            Expr::Block(exprs) => exprs,
            _ => return exception!(block.clone(), "Expected block, got {:?}", block.0),
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
            Null | Bool(_) | Number(_) | Str(_) | List(_) | Lambda { .. } | Reference(_) => {
                Ok(expr.0.clone())
            }

            // Identifiers
            Ident(name) => {
                if let Some(expr) = self.get(name) {
                    Ok(expr.clone())
                } else {
                    exception!(expr.clone(), "Undefined variable '{}'", name)
                }
            }

            // Unary expressions
            Neg(e) => {
                let e = self.eval(e)?;
                match e {
                    Number(n) => Ok(Number(-n)),
                    e => exception!(expr.clone(), "Cannot negate {:?}", e),
                }
            }
            Not(e) => {
                let e = self.eval(e)?;
                Ok(Bool(!e.is_truthy()))
            }

            // Binary arithmetic expressions
            Add(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs + rhs)),
                    (Str(lhs), Str(rhs)) => Ok(Str(lhs + &rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot add {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            Sub(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs - rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot subtract {:?} from {:?}", rhs, lhs)
                    }
                }
            }
            Mul(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs * rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot multiply {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            Div(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs / rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot divide {:?} by {:?}", lhs, rhs)
                    }
                }
            }
            Mod(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Number(lhs % rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot modulo {:?} by {:?}", lhs, rhs)
                    }
                }
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
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            LessThanEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs <= rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            GreaterThan(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs > rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
                    }
                }
            }
            GreaterThanEquals(lhs, rhs) => {
                let lhs = self.eval(lhs)?;
                let rhs = self.eval(rhs)?;

                match (lhs, rhs) {
                    (Number(lhs), Number(rhs)) => Ok(Bool(lhs >= rhs)),
                    (lhs, rhs) => {
                        exception!(expr.clone(), "Cannot compare {:?} and {:?}", lhs, rhs)
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
                    exception!(expr.clone(), "Undefined variable '{}'", name)
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
                    Expr::List(list) => {
                        for item in list.iter() {
                            let mut scope = HashMap::new();
                            scope.insert(iteration_variable.clone(), self.eval(item)?);
                            result = self.eval_block(body, scope)?;
                        }
                        Ok(result)
                    }
                    _ => exception!(
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
                    return exception!(expr.clone(), "Undefined variable {}", name);
                };
                let function = function.unwrap();
                let (arg_names, body) = match function {
                    Expr::Lambda { args, body } => (args, body),
                    _ => return exception!(expr.clone(), "Cannot call {:?}", function),
                };

                let mut scope = HashMap::new();
                for (arg_name, arg) in arg_names.iter().zip(args.iter()) {
                    scope.insert(arg_name.clone(), arg.clone());
                }

                self.eval_block(&body, scope)
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

                self.scopes.last_mut().unwrap().struct_definitions.insert(
                    name.clone(),
                    StructDef {
                        name: name.clone(),
                        fields: field_map,
                        methods: method_map,
                    },
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

                let struct_def = self
                    .scopes
                    .last()
                    .unwrap()
                    .struct_definitions
                    .get(name)
                    .cloned();
                if struct_def.is_none() {
                    return exception!(expr.clone(), "Undefined struct {}", name);
                };
                let struct_def = struct_def.unwrap();

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

                let instance = StructInstance {
                    name: name.clone(),
                    fields,
                    methods,
                };

                let id = self.next_id;
                self.next_id += 1;
                self.instances.insert(id, instance);

                Ok(Expr::Reference(id))
            }

            // Struct field access
            FieldAccess { base, field } => {
                let base = self.eval(base)?;
                match base {
                    Reference(id) => {
                        let instance = self.instances.get(&id).unwrap();
                        Ok(instance.fields.get(field).unwrap().clone())
                    }
                    _ => exception!(expr.clone(), "Expected reference, got {:?}", base),
                }
            }

            MethodCall { base, method, args } => {
                let base = self.eval(base)?;
                let params: Result<Vec<Expr>, Exception> =
                    args.iter().map(|p| self.eval(p)).collect();
                let params = params?;
                match base {
                    Reference(id) => {
                        let instance = self.instances.get_mut(&id).unwrap();
                        let omethod = instance.methods.get(method).cloned();

                        if omethod.is_some() {
                            let method = omethod.unwrap();
                            match method {
                                MethodType::Native(func) => func(instance, params),
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
                            let omethod = instance.fields.get(method).cloned();
                            if omethod.is_some() {
                                let method = omethod.unwrap();
                                match method {
                                    Expr::Lambda { args, body } => {
                                        let mut new_vars = HashMap::new();
                                        for (name, val) in args.iter().zip(params.into_iter()) {
                                            new_vars.insert(name.clone(), val);
                                        }
                                        new_vars.insert("self".to_string(), Reference(id));
                                        self.eval_block(&body, new_vars)
                                    }
                                    _ => exception!(
                                        expr.clone(),
                                        "Cannot call {:?} on {:?}",
                                        method,
                                        base
                                    ),
                                }
                            } else {
                                exception!(
                                    expr.clone(),
                                    "Undefined method {} on {:?}",
                                    method,
                                    base
                                )
                            }
                        }
                    }
                    _ => exception!(expr.clone(), "Expected reference, got {:?}", base),
                }
            }

            FieldAssignment { base, field, value } => {
                let base = self.eval(base)?;
                let value = self.eval(value)?;

                match base {
                    Reference(id) => {
                        let instance = self.instances.get_mut(&id).unwrap();
                        instance.fields.insert(field.clone(), value);
                        Ok(Expr::Null)
                    }
                    _ => exception!(expr.clone(), "Expected reference, got {:?}", base),
                }
            } //_ => exception!(expr.clone(), "Not implemented yet: {:?}", expr.0),
        }
    }
}

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
