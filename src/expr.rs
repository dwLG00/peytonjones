use crate::lambda::{LambdaExpr};
use crate::symbols::{Symbol, SymbolTable};

// A file is a list of statements
#[derive(Debug)]
pub enum Statement {
    VarDef(Symbol, Expr),
    FuncDef(Symbol, Vec<Atom>, Expr)
}

#[derive(Debug)]
pub enum Expr {
    App(Box<Expr>, Box<Expr>), // Apply
    Binop(Binop, Box<Expr>, Box<Expr>),
    Atom(Atom),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    List(Vec<Expr>),
    ListCon(Box<Expr>, Box<Expr>), // [expr1:expr2]
    LetIn(Box<Statement>, Box<Expr>),
    //Where(Box<Expr>, Vec<(Atom, Expr)>)
}

#[derive(Debug)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
    Lt, // <
    Gt // >
}

#[derive(Debug)]
pub enum Atom {
    Term(Symbol),
    StringLit(String),
    IntLit(u32),
    BoolLit(bool)
}

