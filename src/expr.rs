use crate::lambda::{LambdaExpr};
use crate::symbols::{Symbol, SymbolTable};

// A file is a list of statements
pub enum Statement {
    VarDef(Symbol, Expr),
    FuncDef(Symbol, Vec<Atom>, Expr)
}

pub enum Expr {
    App(Symbol, Vec<Expr>), // Apply
    Binop(u32, Box<Expr>, Box<Expr>),
    Atom(Atom),
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    List(Vec<Expr>),
    Where(Box<Expr>, Vec<(Atom, Expr)>)
}

pub enum Atom {
    Term(Symbol),
    StringLit(String),
    IntLit(i32),
    BoolLit(bool),
    ListComp(Symbol, Symbol)
}

