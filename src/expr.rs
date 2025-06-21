use crate::lambda::{LambdaExpr};
use crate::symbols::{Symbol, SymbolTable};
use std::fmt;
use std::cmp::Ordering;

// A file is a list of statements
#[derive(Debug)]
pub enum Statement {
    FuncDef(Symbol, Vec<Atom>, Expr),
    MainDef(Expr) // main function
}

impl Statement {
    pub fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::MainDef(_), Self::MainDef(_)) => Ordering::Equal,
            (Self::MainDef(_), Self::FuncDef(_, _, _)) => Ordering::Greater,
            (Self::FuncDef(_, _, _), Self::MainDef(_)) => Ordering::Less,
            (Self::FuncDef(s1, _, _), Self::FuncDef(s2, _, _)) => s1.cmp(s2)
        }
    }
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
    Gt, // >
    Eq
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Atom {
    Term(Symbol),
    StringLit(String),
    IntLit(u32),
    BoolLit(bool)
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Write strictly the first element into the supplied output
        // stream: `f`. Returns `fmt::Result` which indicates whether the
        // operation succeeded or failed. Note that `write!` uses syntax which
        // is very similar to `println!`.
        match self {
            Atom::Term(s) => write!(f, "s{}", s.0),
            Atom::StringLit(string) => write!(f, "\"{}\")", string),
            Atom::IntLit(int) => write!(f, "{}", int),
            Atom::BoolLit(b) => if *b {
                write!(f, "true")
            } else {
                write!(f, "false")
            }
        }
    }
}

