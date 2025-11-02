use core::fmt;
use std::collections::btree_map::Keys;
use std::collections::HashMap;
use std::hash::Hash;

use crate::expr::{Atom, Arg, Binop};
use crate::symbols::{Symbol, SymbolID, AlphaSubbable};
use crate::aux::Recursible;

#[derive(Debug, Clone)]
pub enum SupercombinatorExpr<S, N> where S: Copy, N: Copy {
    StringTerm(N, String),
    IntTerm(N, u32),
    BoolTerm(N, bool),
    VarTerm(N, S),
    OpTerm(N, OpTerm),
    Supercombinator(N, u32),
    EmptyList(N),
    ListCon(N, Box<SupercombinatorExpr<S, N>>, Box<SupercombinatorExpr<S, N>>),
    TermApplications(N, Box<SupercombinatorExpr<S, N>>, Box<SupercombinatorExpr<S, N>>),
    LetIn(N, Vec<(S, SupercombinatorExpr<S, N>)>, Box<SupercombinatorExpr<S, N>>),
    CaseOf(N, S, HashMap<Arg, SupercombinatorExpr<S, N>>),
    TryThen(N, Box<SupercombinatorExpr<S, N>>, Box<SupercombinatorExpr<S, N>>),
    FAIL
}

impl<S: Copy, N: Copy> SupercombinatorExpr<S, N> {
    pub fn get_type(&self) -> &N {
        match self {
            Self::StringTerm(n, _) => n,
            Self::IntTerm(n, _) => n,
            Self::BoolTerm(n, _) => n,
            Self::VarTerm(n, _) => n,
            Self::OpTerm(n, _) => n,
            Self::Supercombinator(n, _) => n,
            Self::EmptyList(n) => n,
            Self::ListCon(n, _, _) => n,
            Self::TermApplications(n, _, _) => n,
            Self::LetIn(n, _, _) => n,
            Self::CaseOf(n, _, _) => n,
            Self::TryThen(n, _, _) => n,
            Self::FAIL => {
                panic!("Type of FAIL should never be checked")
            }
        }
    }
}

impl<S: Copy + AlphaSubbable, N: Copy> AlphaSubbable for SupercombinatorExpr<S, N> {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        match self {
            Self::VarTerm(n, s) => Self::VarTerm(*n, s.alpha_subst(old, new)),
            Self::ListCon(n, car, cdr) => Self::ListCon(*n, Box::new(car.alpha_subst(old, new)), Box::new(cdr.alpha_subst(old, new))),
            Self::TermApplications(n, func, arg) => Self::TermApplications(*n, Box::new(func.alpha_subst(old, new)), Box::new(arg.alpha_subst(old, new))),
            Self::LetIn(n, v, expr) => Self::LetIn(
                *n, 
                v.iter().map(|(s, e)| (s.alpha_subst(old, new), e.alpha_subst(old, new))).collect(),
                Box::new(expr.alpha_subst(old, new))
            ),
            Self::CaseOf(n, s, hm) => Self::CaseOf(
                *n,
                s.alpha_subst(old, new),
                supercombinator_alpha_subst(hm, old, new)
            ),
            Self::TryThen(n, first, second) => Self::TryThen(*n, Box::new(first.alpha_subst(old, new)), Box::new(second.alpha_subst(old, new))),
            _ => self.clone()
        }
    }
    fn alpha_multisubst(&self, map: &Vec<(SymbolID, SymbolID)>) -> Self {
        match self {
            Self::VarTerm(n, s) => Self::VarTerm(*n, s.alpha_multisubst(map)),
            Self::ListCon(n, car, cdr) => Self::ListCon(*n, Box::new(car.alpha_multisubst(map)), Box::new(cdr.alpha_multisubst(map))),
            Self::TermApplications(n, func, arg) => Self::TermApplications(*n, Box::new(func.alpha_multisubst(map)), Box::new(arg.alpha_multisubst(map))),
            Self::LetIn(n, v, expr) => Self::LetIn(
                *n, 
                v.iter().map(|(s, e)| (s.alpha_multisubst(map), e.alpha_multisubst(map))).collect(),
                Box::new(expr.alpha_multisubst(map))
            ),
            Self::CaseOf(n, s, hm) => Self::CaseOf(
                *n,
                s.alpha_multisubst(map),
                supercombinator_alpha_multisubst(hm, map)
            ),
            Self::TryThen(n, first, second) => Self::TryThen(*n, Box::new(first.alpha_multisubst(map)), Box::new(second.alpha_multisubst(map))),
            _ => self.clone()
        }
    }
}

impl<N> fmt::Display for SupercombinatorExpr<SymbolID, N> where N: Copy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Supercombinator(_, s) => write!(f, "$Y{s}"),
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

    pub fn at_node<F, E>(&self, f: &mut F) -> Result<(), E>
        where F: FnMut(N) -> Result<(), E>
    {
        match self {
            Self::StringTerm(n, _) | Self::IntTerm(n, _) | Self::BoolTerm(n, _) 
            | Self::VarTerm(n, _) | Self::OpTerm(n, _) | Self::EmptyList(n) => f(*n),
            Self::ListCon(n, expr1, expr2) | Self::TermApplications(n, expr1, expr2) | Self::TryThen(n, expr1, expr2) => {
                expr1.at_node(f)?;
                expr2.at_node(f)?;
                f(*n)
            },
            Self::Lambda(n, _, expr) => {
                expr.at_node(f)?;
                f(*n)
            },
            Self::LetIn(n, v, expr) => {
                for (_, e) in v.iter() {
                    e.at_node(f)?;
                }
                expr.at_node(f)?;
                f(*n)
            },
            Self::CaseOf(n, _, hm) => {
                for (_, e) in hm.iter() {
                    e.at_node(f)?;
                }
                f(*n)
            },
            Self::FAIL => Ok(())
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

impl<S: Copy + AlphaSubbable, T: Copy> AlphaSubbable for AnnotatedLambdaExpr<S, T> {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        match self {
            Self::VarTerm(t, s) => Self::VarTerm(*t, s.alpha_subst(old, new)),
            Self::ListCon(t, car, cdr) => Self::ListCon(*t, Box::new(car.alpha_subst(old, new)), Box::new(cdr.alpha_subst(old, new))),
            Self::TermApplications(t, f, app) => Self::TermApplications(
                *t,
                Box::new(f.alpha_subst(old, new)),
                Box::new(app.alpha_subst(old, new))
            ),
            Self::Lambda(t, s, expr) => Self::Lambda(*t, s.alpha_subst(old, new), Box::new(expr.alpha_subst(old, new))),
            Self::LetIn(t, v, expr) => Self::LetIn(
                *t, 
                v.iter().map(|(s, e)| (s.alpha_subst(old, new), e.alpha_subst(old, new))).collect(),
                Box::new(expr.alpha_subst(old, new))
            ),
            Self::CaseOf(t, s, hm) => Self::CaseOf(
                *t,
                s.alpha_subst(old, new),
                annotated_alpha_subst(hm, old, new)
            ),
            Self::TryThen(t, first, second) => Self::TryThen(*t, Box::new(first.alpha_subst(old, new)), Box::new(second.alpha_subst(old, new))),
            _ => self.clone()
        }
    }
    fn alpha_multisubst(&self, map: &Vec<(SymbolID, SymbolID)>) -> Self {
        match self {
            Self::VarTerm(t, s) => Self::VarTerm(*t, s.alpha_multisubst(map)),
            Self::ListCon(t, car, cdr) => Self::ListCon(*t, Box::new(car.alpha_multisubst(map)), Box::new(cdr.alpha_multisubst(map))),
            Self::TermApplications(t, f, app) => Self::TermApplications(
                *t,
                Box::new(f.alpha_multisubst(map)),
                Box::new(app.alpha_multisubst(map))
            ),
            Self::Lambda(t, s, expr) => Self::Lambda(*t, s.alpha_multisubst(map), Box::new(expr.alpha_multisubst(map))),
            Self::LetIn(t, v, expr) => Self::LetIn(
                *t, 
                v.iter().map(|(s, e)| (s.alpha_multisubst(map), e.alpha_multisubst(map))).collect(),
                Box::new(expr.alpha_multisubst(map))
            ),
            Self::CaseOf(t, s, hm) => Self::CaseOf(
                *t,
                s.alpha_multisubst(map),
                annotated_alpha_multisubst(hm, map)
            ),
            Self::TryThen(t, first, second) => Self::TryThen(*t, Box::new(first.alpha_multisubst(map)), Box::new(second.alpha_multisubst(map))),
            _ => self.clone()
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

fn annotated_alpha_subst<S : Copy + AlphaSubbable, N : Copy>(hm: &HashMap<Arg, AnnotatedLambdaExpr<S, N>>, old: SymbolID, new: SymbolID) -> HashMap<Arg, AnnotatedLambdaExpr<S, N>> {
    let mut new_hm = HashMap::new();
    for (arg, e) in hm.iter() {
        new_hm.insert(arg.alpha_subst(old, new), e.alpha_subst(old, new));
    }
    new_hm
}

fn annotated_alpha_multisubst<S : Copy + AlphaSubbable, N : Copy>(hm: &HashMap<Arg, AnnotatedLambdaExpr<S, N>>, map: &Vec<(SymbolID, SymbolID)>) -> HashMap<Arg, AnnotatedLambdaExpr<S, N>> {
    let mut new_hm = HashMap::new();
    for (arg, e) in hm.iter() {
        new_hm.insert(arg.alpha_multisubst(map), e.alpha_multisubst(map));
    }
    new_hm
}

fn supercombinator_alpha_subst<S : Copy + AlphaSubbable, N : Copy>(hm: &HashMap<Arg, SupercombinatorExpr<S, N>>, old: SymbolID, new: SymbolID) -> HashMap<Arg, SupercombinatorExpr<S, N>> {
    let mut new_hm = HashMap::new();
    for (arg, e) in hm.iter() {
        new_hm.insert(arg.alpha_subst(old, new), e.alpha_subst(old, new));
    }
    new_hm
}

fn supercombinator_alpha_multisubst<S : Copy + AlphaSubbable, N : Copy>(hm: &HashMap<Arg, SupercombinatorExpr<S, N>>, map: &Vec<(SymbolID, SymbolID)>) -> HashMap<Arg, SupercombinatorExpr<S, N>> {
    let mut new_hm = HashMap::new();
    for (arg, e) in hm.iter() {
        new_hm.insert(arg.alpha_multisubst(map), e.alpha_multisubst(map));
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