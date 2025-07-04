use core::fmt;
use std::collections::btree_map::Keys;
use std::collections::HashMap;
use std::hash::Hash;

use crate::expr::{Atom, Arg, Binop};
use crate::symbols::{Symbol, SymbolID, AlphaSubbable};
use crate::aux::Recursible;

#[derive(Debug, Clone)]
pub enum AnnotatedLambdaExpr<S, N> where S: Copy, N: Copy {
    StringTerm(N, String),
    IntTerm(N, u32),
    BoolTerm(N, bool),
    VarTerm(N, S),
    OpTerm(N, OpTerm),
    EmptyList(N),
    ListCon(N, Box<AnnotatedLambdaExpr<S, N>>, Box<AnnotatedLambdaExpr<S, N>>),
    TermApplications(N, Box<AnnotatedLambdaExpr<S, N>>, Box<AnnotatedLambdaExpr<S, N>>),
    Lambda(N, S, Box<AnnotatedLambdaExpr<S, N>>),
    LetIn(N, Vec<(S, AnnotatedLambdaExpr<S, N>)>, Box<AnnotatedLambdaExpr<S, N>>),
    CaseOf(N, S, HashMap<Arg, AnnotatedLambdaExpr<S, N>>),
    TryThen(N, Box<AnnotatedLambdaExpr<S, N>>, Box<AnnotatedLambdaExpr<S, N>>),
    FAIL
}


impl<S: Copy, N: Copy> AnnotatedLambdaExpr<S, N> {
    pub fn map<N2, F>(self, f: &mut F) -> AnnotatedLambdaExpr<S, N2> 
        where F: FnMut(N) -> N2,
        N2: Copy
    {
        match self {
            Self::StringTerm(n, s) => AnnotatedLambdaExpr::StringTerm(f(n), s),
            Self::IntTerm(n, i) => AnnotatedLambdaExpr::IntTerm(f(n), i),
            Self::BoolTerm(n, b) => AnnotatedLambdaExpr::BoolTerm(f(n), b),
            Self::VarTerm(n, s) => AnnotatedLambdaExpr::VarTerm(f(n), s),
            Self::OpTerm(n, op) => AnnotatedLambdaExpr::OpTerm(f(n), op),
            Self::EmptyList(n) => AnnotatedLambdaExpr::EmptyList(f(n)),
            Self::ListCon(n, expr1, expr2) => AnnotatedLambdaExpr::ListCon(f(n), Box::new(expr1.map(f)), Box::new(expr2.map(f))),
            Self::TermApplications(n, expr1, expr2) => AnnotatedLambdaExpr::TermApplications(f(n), Box::new(expr1.map(f)), Box::new(expr2.map(f))),
            Self::Lambda(n, s, expr) => AnnotatedLambdaExpr::Lambda(f(n), s, Box::new(expr.map(f))),
            Self::LetIn(n, v, expr) => AnnotatedLambdaExpr::LetIn(f(n), v.into_iter().map(|(s, e)| (s, e.map(f))).collect(), Box::new(expr.map(f))),
            Self::CaseOf(n, s, hm) => AnnotatedLambdaExpr::CaseOf(f(n), s, hm.into_iter().map(|(arg, e)| (arg, e.map(f))).collect()),
            Self::TryThen(n, expr1, expr2) => AnnotatedLambdaExpr::TryThen(f(n), Box::new(expr1.map(f)), Box::new(expr2.map(f))),
            Self::FAIL => AnnotatedLambdaExpr::FAIL
        }
    }

    pub fn map_node<N2, F>(&self, f: F) -> Option<N2>
        where F: FnOnce(N) -> N2
    {
        match self {
            Self::StringTerm(n, _) | Self::IntTerm(n, _) | Self::BoolTerm(n, _)
            | Self::VarTerm(n, _) | Self::OpTerm(n, _) | Self::EmptyList(n)
            | Self::ListCon(n, _, _) | Self::TermApplications(n, _, _) | Self::Lambda(n, _, _)
            | Self::LetIn(n, _, _) | Self::CaseOf(n, _, _) | Self::TryThen(n, _, _) => Some(f(*n)),
            Self::FAIL => None
        }
    }
}

pub type LambdaExpr = AnnotatedLambdaExpr<SymbolID, ()>;

impl Recursible for LambdaExpr {
    fn recurse(&self, f: fn(LambdaExpr) -> LambdaExpr) -> LambdaExpr {
        match self {
            Self::ListCon(_, expr1, expr2) => f(Self::ListCon((), Box::new(expr1.recurse(f)), Box::new(expr2.recurse(f)))),
            Self::TermApplications(_, expr1, expr2) => f(Self::TermApplications((), Box::new(expr1.recurse(f)), Box::new(expr2.recurse(f)))),
            Self::Lambda(_, s, expr) => f(Self::Lambda((), *s, Box::new(expr.recurse(f)))),
            Self::LetIn(_, v, expr) => f(Self::LetIn((), v.iter().map(|(s, e)| (*s, e.recurse(f))).collect(), Box::new(expr.recurse(f)))),
            Self::CaseOf(_, s, hm) => f(Self::CaseOf((), *s, HashMap::from_iter(hm.iter().map(|(arg, e)| (arg.clone(), e.recurse(f)))))),
            Self::TryThen(_, expr1, expr2) => f(Self::TryThen((), Box::new(expr1.recurse(f)), Box::new(expr2.recurse(f)))),
            _ => f(self.clone())
        }
    }
}

impl AlphaSubbable for LambdaExpr {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        match self {
            //Self::SimpleTerm(a) => Self::SimpleTerm(a.alpha_subst(old, new)),
            Self::StringTerm(_, s) => Self::StringTerm((), s.clone()),
            Self::IntTerm(_, n) => Self::IntTerm((), *n),
            Self::BoolTerm(_, b) => Self::BoolTerm((), *b),
            Self::VarTerm(_, s) => Self::VarTerm((), s.alpha_subst(old, new)),
            Self::ListCon(_, car, cdr) => Self::ListCon((), Box::new(car.alpha_subst(old, new)), Box::new(cdr.alpha_subst(old, new))),
            Self::TermApplications(_, f, app) => Self::TermApplications(
                (),
                Box::new(f.alpha_subst(old, new)),
                Box::new(app.alpha_subst(old, new))
            ),
            Self::Lambda(_, s, expr) => Self::Lambda((), s.alpha_subst(old, new), Box::new(expr.alpha_subst(old, new))),
            Self::LetIn(_, v, expr) => Self::LetIn(
                (), 
                v.iter().map(|(s, e)| (s.alpha_subst(old, new), e.alpha_subst(old, new))).collect(),
                Box::new(expr.alpha_subst(old, new))
            ),
            Self::CaseOf(_, s, hm) => Self::CaseOf(
                (),
                s.alpha_subst(old, new),
                alpha_subst(hm, old, new)
            ),
            Self::TryThen(_, first, second) => Self::TryThen((), Box::new(first.alpha_subst(old, new)), Box::new(second.alpha_subst(old, new))),
            _ => self.clone()
        }
    }
}

impl<N> fmt::Display for AnnotatedLambdaExpr<SymbolID, N> where N: Copy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            //LambdaExpr::SimpleTerm(s) => write!(f, "{s}"),
            Self::StringTerm(_, s) => write!(f, "\"{s}\""),
            Self::IntTerm(_, n) => write!(f, "{n}"),
            Self::BoolTerm(_, b) => if *b {
                write!(f, "true")
            } else {
                write!(f, "false")
            },
            Self::VarTerm(_, s) => write!(f, "s{s}"),
            Self::OpTerm(_, op) => write!(f, "{op}"),
            Self::EmptyList(_) => write!(f, "[]"),
            Self::ListCon(_, car, cdr) => write!(f, "{car} : {cdr}"),
            Self::TermApplications(_, func, app) => {
                match **app {
                    //LambdaExpr::SimpleTerm(_) => write!(f, "{func} {app}"),
                    Self::StringTerm(_, _) | Self::BoolTerm(_, _) 
                        | Self::IntTerm(_, _) | Self::VarTerm(_, _) => write!(f, "{func} {app}"),
                    _ => write!(f, "{func} ({app})")
                }
            },
            Self::Lambda(_, s, expr) => {
                write!(f, "(λs{s}. {expr})")
            },
            Self::LetIn(_, vec, expr) => {
                let vec_s = vec.iter().map(|(s, e)| format!("s{s} := {e},")).collect::<String>();
                let vec_s = vec_s.trim_end_matches(",");
                write!(f, "(let {vec_s} in {expr})")
            },
            Self::CaseOf(_, s, hm) => {
                let vec_s = hm.iter().map(|(key, val)| format!("({key} => {val}),")).collect::<String>();
                let vec_s = vec_s.trim_end_matches(",");
                write!(f, "(case s{s}: {vec_s})")
            },
            Self::TryThen(_, first, second) => write!(f, "{first} █ {second}"),
            Self::FAIL => write!(f, "FAIL")
        }
    }
}

fn alpha_subst(hm: &HashMap<Arg, LambdaExpr>, old: SymbolID, new: SymbolID) -> HashMap<Arg, LambdaExpr> {
    let mut new_hm = HashMap::new();
    for (arg, e) in hm.iter() {
        new_hm.insert(arg.alpha_subst(old, new), e.alpha_subst(old, new));
    }
    new_hm
}

#[derive(Copy, Clone)]
pub enum OpTerm {
    Add,
    Sub,
    Mul,
    Div,
    Lt, // <
    Gt, // >
    Eq,
    IfElse
}

impl OpTerm {
    pub fn from_binop(b: Binop) -> Self {
        match b {
            Binop::Add => OpTerm::Add,
            Binop::Sub => OpTerm::Sub,
            Binop::Mul => OpTerm::Mul,
            Binop::Div => OpTerm::Div,
            Binop::Lt => OpTerm::Lt,
            Binop::Gt => OpTerm::Gt,
            Binop::Eq => OpTerm::Eq
        }
    }
}

impl fmt::Display for OpTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpTerm::Add => write!(f, "+"),
            OpTerm::Sub => write!(f, "-"),
            OpTerm::Mul => write!(f, "*"),
            OpTerm::Div => write!(f, "/"),
            OpTerm::Lt => write!(f, "<"),
            OpTerm::Gt => write!(f, ">"),
            OpTerm::Eq => write!(f, "="),
            OpTerm::IfElse => write!(f, "if")
        }
    }
}

impl fmt::Debug for OpTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(&self, f)
    }
}

enum Changed<T> {
    Changed(T),
    Unchanged(T)
}

impl<T> Changed<T> {
    fn merge<S>(self, s : S) -> Changed<(T, S)> {
        match self {
            Changed::Unchanged(t) => Changed::Unchanged((t, s)),
            Changed::Changed(t) => Changed::Changed((t, s))
        }
    }

    fn flipmerge<S>(self, s : S) -> Changed<(S, T)> {
        match self {
            Changed::Unchanged(t) => Changed::Unchanged((s, t)),
            Changed::Changed(t) => Changed::Changed((s, t))
        }
    }

    fn combine<S>(self, s : Changed<S>) -> Changed<(T, S)> {
        match (self, s) {
            (Changed::Changed(t_), Changed::Changed(s_)) => Changed::Changed((t_, s_)),
            (Changed::Changed(t_), Changed::Unchanged(s_)) => Changed::Changed((t_, s_)),
            (Changed::Unchanged(t_), Changed::Changed(s_)) => Changed::Changed((t_, s_)),
            (Changed::Unchanged(t_), Changed::Unchanged(s_)) => Changed::Unchanged((t_, s_))
        }
    }
}

// Implement mapping T -> Changed<T>'s on Vec<T>'s to get Changed<Vec<T>>'s
impl<T> std::iter::FromIterator<Changed<T>> for Changed<Vec<T>> {
    fn from_iter<I: IntoIterator<Item = Changed<T>>>(iter: I) -> Self {
        let mut v = Vec::new();
        let mut has_changed: bool = false;
        for item in iter {
            match item {
                Changed::Changed(t) => {
                    has_changed = true;
                    v.push(t);
                },
                Changed::Unchanged(t) => {
                    v.push(t);
                }
            };
        }
        if has_changed {
            Changed::Changed(v)
        } else {
            Changed::Unchanged(v)
        }
    }
}

pub fn simp_case(e: LambdaExpr) -> LambdaExpr {
    match e {
        LambdaExpr::CaseOf(_, s, ref hm) => {
            let vecify: Vec<(Arg, LambdaExpr)> = hm.iter().map(|(a, e)| (a.clone(), e.clone())).collect();
            if vecify.len() == 1 {
                let (a, e) = &vecify[0];
                if let Arg::Atom(a) = a {
                    if let Atom::Term(s_) = a {
                        let e = e.alpha_subst(s_.0, s); // Revert the symbols
                        return e;
                    }
                }
            }
        },
        _ => {}
    }
    e
}