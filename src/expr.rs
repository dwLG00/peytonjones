use crate::lambda::{LambdaExpr};
use crate::symbols::{Symbol, SymbolID, SymbolTable, AlphaSubbable};
use std::fmt;
use std::cmp::Ordering;

// A file is a list of statements
#[derive(Debug, Clone)]
pub enum Statement {
    FuncDef(Symbol, Vec<Arg>, Expr),
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

    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        match self {
            Statement::FuncDef(s, args, e) => {
                let new_s = s.alpha_subst(old, new);
                let new_args = args.iter().map(|a| a.alpha_subst(old, new)).collect();
                let new_e = e.alpha_subst(old, new);
                Statement::FuncDef(new_s, new_args, new_e)
            },
            Statement::MainDef(e) => Statement::MainDef(e.alpha_subst(old, new))
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
    LetIn(Vec<Statement>, Box<Expr>),
    //Where(Box<Expr>, Vec<(Atom, Expr)>)
}

impl Clone for Expr {
    fn clone(&self) -> Self {
        match self {
            Expr::App(e1, e2) => Expr::App(e1.clone(), e2.clone()),
            Expr::Binop(binop, e1, e2) => Expr::Binop(*binop, e1.clone(), e2.clone()),
            Expr::Atom(atom) => Expr::Atom(atom.clone()),
            Expr::IfElse(e1, e2, e3) => Expr::IfElse(e1.clone(), e2.clone(), e3.clone()),
            Expr::List(e_vec) => Expr::List(e_vec.iter().map(|e| e.clone()).collect()),
            Expr::ListCon(e1, e2) => Expr::ListCon(e1.clone(), e2.clone()),
            Expr::LetIn(s, e) => Expr::LetIn(s.clone(), e.clone())
        }
    }
}

impl AlphaSubbable for Expr {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        match self {
            Self::App(expr1, expr2) => 
                Self::App(
                    Box::new(expr1.alpha_subst(old, new)),
                    Box::new(expr2.alpha_subst(old, new))
                ),
            Self::Binop(binop, expr1, expr2) => 
                Self::Binop(
                    *binop, 
                    Box::new(expr1.alpha_subst(old, new)),
                    Box::new(expr2.alpha_subst(old, new))
                ),
            Self::Atom(atom) => Self::Atom(atom.alpha_subst(old, new)),
            Self::IfElse(cond, if_clause, else_clause) => 
                Self::IfElse(
                    Box::new(cond.alpha_subst(old, new)),
                    Box::new(if_clause.alpha_subst(old, new)),
                    Box::new(else_clause.alpha_subst(old, new))
                ),
            Self::List(expr_vec) => Self::List(expr_vec.iter().map(|e| e.alpha_subst(old, new)).collect()),
            Self::ListCon(expr1, expr2) =>
                Self::ListCon(
                    Box::new(expr1.alpha_subst(old, new)),
                    Box::new(expr2.alpha_subst(old, new))
                ),
            Self::LetIn(statements, expr) => Self::LetIn(statements.iter().map(|s| s.alpha_subst(old, new)).collect(), Box::new(expr.alpha_subst(old, new)))
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
    Lt, // <
    Gt, // >
    Eq
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Atom {
    Term(Symbol),
    StringLit(String),
    IntLit(u32),
    BoolLit(bool)
}

impl AlphaSubbable for Atom {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        match self {
            Atom::Term(s) => Atom::Term(s.alpha_subst(old, new)),
            _ => self.clone()
        }
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Atom::Term(s) => write!(f, "s{}", s.0),
            Atom::StringLit(string) => write!(f, "\"{}\"", string),
            Atom::IntLit(int) => write!(f, "{}", int),
            Atom::BoolLit(b) => if *b {
                write!(f, "true")
            } else {
                write!(f, "false")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Arg {
    Atom(Atom),
    ListCon(Box<Arg>, Box<Arg>),
    EmptyList
    //List(Vec<Arg>)
}

impl Arg {
    pub fn is_var(&self) -> bool {
        match self {
            Arg::Atom(a) => match a {
                Atom::Term(s) => !s.1,
                _ => false
            }
            _ => false
        }
    }

    pub fn like_var(&self) -> bool {
        // Weaker than is_var, counting cases where variables are in lists
        match self {
            Arg::Atom(a) => match a {
                Atom::Term(s) => !s.1, // Unbound variable (i.e. not previously defined)
                _ => false
            },
            Arg::ListCon(arg1, arg2) => arg1.like_var() || arg2.like_var(),
            Arg::EmptyList => false
        }
    }
}

impl AlphaSubbable for Arg {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        match self {
            Arg::Atom(a) => Arg::Atom(a.alpha_subst(old, new)),
            Arg::ListCon(arg1, arg2) => Arg::ListCon(Box::new(arg1.alpha_subst(old, new)), Box::new(arg2.alpha_subst(old, new))),
            Arg::EmptyList => Arg::EmptyList
        }
    }
}

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Arg::Atom(a) => a.fmt(f),
            Arg::ListCon(car, cdr) => write!(f, "{} : {}", car.to_string(), cdr.to_string()),
            Arg::EmptyList => write!(f, "[]")
        }
    }
}