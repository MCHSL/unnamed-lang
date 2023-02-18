use crate::common::Spanned;

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
