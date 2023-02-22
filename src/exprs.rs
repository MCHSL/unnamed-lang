use std::{collections::HashMap, fmt::Display};

use crate::{common::Spanned, interpreter};

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // Block of expressions
    Block(Vec<Spanned<Self>>),

    // Literal values
    Null,
    Number(f64),
    Str(String),
    Bool(bool),
    Ident(String),
    List(Vec<Spanned<Self>>),

    // Math operations
    Add(BExpr, BExpr),
    Sub(BExpr, BExpr),
    Mul(BExpr, BExpr),
    Div(BExpr, BExpr),
    Mod(BExpr, BExpr),

    // Comparison operations
    EqualsEquals(BExpr, BExpr),
    NotEquals(BExpr, BExpr),
    LessThan(BExpr, BExpr),
    LessThanEquals(BExpr, BExpr),
    GreaterThan(BExpr, BExpr),
    GreaterThanEquals(BExpr, BExpr),

    // Logical operations
    And(BExpr, BExpr),
    Or(BExpr, BExpr),

    // Unary operations
    Not(BExpr),
    Neg(BExpr),

    // Variable declaration
    Let {
        name: String,
        initializer: BExpr,
    },

    // Functions
    Lambda {
        arg_names: Vec<String>,
        body: BExpr,
        environment: HashMap<String, Expr>,
    },

    NativeFunction {
        name: String,
        function: interpreter::NativeFunc,
    },

    // Control flow
    If {
        condition: BExpr,
        then_branch: BExpr,
        else_branch: Option<BExpr>,
    },
    While {
        condition: BExpr,
        body: BExpr,
    },
    For {
        iteration_variable: String,
        iterated_expression: BExpr,
        body: BExpr,
    },
    Call {
        name: BExpr,
        args: Spanned<Vec<BExpr>>,
    },

    // Variable stuff
    Assign {
        name: String,
        value: BExpr,
    },

    // Structs
    StructDefinition {
        name: String,
        fields: Vec<(String, Spanned<Expr>)>,
        methods: Vec<(String, Vec<String>, Spanned<Expr>)>,
    },

    // Instance of a struct
    Reference(usize),

    // New instance
    New {
        name: String,
        args: Vec<(String, Spanned<Expr>)>,
    },

    FieldAccess {
        base: BExpr,
        field: String,
    },

    MethodCall {
        base: BExpr,
        method: String,
        args: Vec<BExpr>,
    },

    FieldAssignment {
        base: BExpr,
        field: String,
        value: BExpr,
    },
}

type BExpr = Box<Spanned<Expr>>;

impl Expr {
    pub fn ident_string(&self) -> String {
        match self {
            Expr::Ident(s) => s.clone(),
            _ => panic!("Internal compiler error: Expected identifier"),
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            Expr::Null => false,
            Expr::Number(n) => *n != 0.0,
            Expr::Str(s) => !s.is_empty(),
            Expr::Bool(b) => *b,
            _ => true,
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Block(exprs) => {
                write!(f, "{{")?;
                for expr in exprs {
                    write!(f, "{}", expr.0)?;
                }
                write!(f, "}}")
            }
            Expr::Null => write!(f, "null"),
            Expr::Number(n) => write!(f, "{n}"),
            Expr::Str(s) => write!(f, "{s}"),
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Ident(s) => write!(f, "{s}"),
            Expr::List(exprs) => {
                write!(f, "[")?;
                for expr in exprs {
                    write!(f, "{}", expr.0)?;
                }
                write!(f, "]")
            }
            Expr::Add(l, r) => write!(f, "({} + {})", l.0, r.0),
            Expr::Sub(l, r) => write!(f, "({} - {})", l.0, r.0),
            Expr::Mul(l, r) => write!(f, "({} * {})", l.0, r.0),
            Expr::Div(l, r) => write!(f, "({} / {})", l.0, r.0),
            Expr::Mod(l, r) => write!(f, "({} % {})", l.0, r.0),
            Expr::EqualsEquals(l, r) => write!(f, "({} == {})", l.0, r.0),
            Expr::NotEquals(l, r) => write!(f, "({} != {})", l.0, r.0),
            Expr::LessThan(l, r) => write!(f, "({} < {})", l.0, r.0),
            Expr::LessThanEquals(l, r) => write!(f, "({} <= {})", l.0, r.0),
            Expr::GreaterThan(l, r) => write!(f, "({} > {})", l.0, r.0),
            Expr::GreaterThanEquals(l, r) => write!(f, "({} >= {})", l.0, r.0),
            Expr::And(l, r) => write!(f, "({} && {})", l.0, r.0),
            Expr::Or(l, r) => write!(f, "({} || {})", l.0, r.0),
            Expr::Not(e) => write!(f, "(!{})", e.0),
            Expr::Neg(e) => write!(f, "(-{})", e.0),
            Expr::Let { name, initializer } => write!(f, "let {} = {};", name, initializer.0),
            Expr::Lambda {
                arg_names, body, ..
            } => {
                write!(f, "fn(")?;
                for arg in arg_names {
                    write!(f, "{arg}, ")?;
                }
                write!(f, ") {}", body.0)
            }
            Expr::NativeFunction { name, .. } => write!(f, "fn {name}"),
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                write!(f, "if {} {}", condition.0, then_branch.0)?;
                if let Some(else_branch) = else_branch {
                    write!(f, " else {}", else_branch.0)?;
                }
                Ok(())
            }
            Expr::While { condition, body } => write!(f, "while {} {}", condition.0, body.0),
            Expr::For {
                iteration_variable,
                iterated_expression,
                body,
            } => write!(
                f,
                "for {} in {} {}",
                iteration_variable, iterated_expression.0, body.0
            ),
            Expr::Call { name, args } => {
                write!(f, "{}(", name.0)?;
                for arg in &args.0 {
                    write!(f, "{}, ", arg.0)?;
                }
                write!(f, ")")
            }
            Expr::Assign { name, value } => write!(f, "{} = {};", name, value.0),
            Expr::StructDefinition {
                name,
                fields,
                methods,
            } => {
                write!(f, "struct {name} {{")?;
                for (name, value) in fields {
                    write!(f, "{}: {}, ", name, value.0)?;
                }
                for (name, args, body) in methods {
                    write!(f, "fn {name}(")?;
                    for arg in args {
                        write!(f, "{arg}, ")?;
                    }
                    write!(f, ") {}", body.0)?;
                }
                write!(f, "}}")
            }
            Expr::Reference(id) => write!(f, "ref({id})"),
            Expr::New { name, args } => {
                write!(f, "{name} {{")?;
                for (name, value) in args {
                    write!(f, "{}: {}, ", name, value.0)?;
                }
                write!(f, "}}")
            }
            Expr::FieldAccess { base, field } => write!(f, "{}.{}", base.0, field),
            Expr::MethodCall { base, method, args } => {
                write!(f, "{}.{}(", base.0, method)?;
                for arg in args {
                    write!(f, "{}, ", arg.0)?;
                }
                write!(f, ")")
            }
            Expr::FieldAssignment { base, field, value } => {
                write!(f, "{}.{} = {};", base.0, field, value.0)
            }
        }
    }
}
