use core::fmt;
use std::collections::btree_map::Keys;
use std::collections::HashMap;
use std::hash::Hash;

use crate::expr::{Atom, Arg, Binop};
use crate::symbols::{Symbol, SymbolID, AlphaSubbable};
use crate::aux::Recursible;

#[derive(Clone)]
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

impl fmt::Display for LambdaExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            //LambdaExpr::SimpleTerm(s) => write!(f, "{s}"),
            LambdaExpr::StringTerm(_, s) => write!(f, "\"{s}\""),
            LambdaExpr::IntTerm(_, n) => write!(f, "{n}"),
            LambdaExpr::BoolTerm(_, b) => if *b {
                write!(f, "true")
            } else {
                write!(f, "false")
            },
            LambdaExpr::VarTerm(_, s) => write!(f, "s{s}"),
            LambdaExpr::OpTerm(_, op) => write!(f, "{op}"),
            LambdaExpr::EmptyList(_) => write!(f, "[]"),
            LambdaExpr::ListCon(_, car, cdr) => write!(f, "{car} : {cdr}"),
            LambdaExpr::TermApplications(_, func, app) => {
                match **app {
                    //LambdaExpr::SimpleTerm(_) => write!(f, "{func} {app}"),
                    LambdaExpr::StringTerm(_, _) | LambdaExpr::BoolTerm(_, _) 
                        | LambdaExpr::IntTerm(_, _) | LambdaExpr::VarTerm(_, _) => write!(f, "{func} {app}"),
                    _ => write!(f, "{func} ({app})")
                }
            },
            LambdaExpr::Lambda(_, s, expr) => {
                write!(f, "(λs{s}. {expr})")
            },
            LambdaExpr::LetIn(_, vec, expr) => {
                let vec_s = vec.iter().map(|(s, e)| format!("s{s} := {e},")).collect::<String>();
                let vec_s = vec_s.trim_end_matches(",");
                write!(f, "(let {vec_s} in {expr})")
            },
            LambdaExpr::CaseOf(_, s, hm) => {
                let vec_s = hm.iter().map(|(key, val)| format!("({key} => {val}),")).collect::<String>();
                let vec_s = vec_s.trim_end_matches(",");
                write!(f, "(case s{s}: {vec_s})")
            },
            LambdaExpr::TryThen(_, first, second) => write!(f, "{first} █ {second}"),
            LambdaExpr::FAIL => write!(f, "FAIL")
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

/*

pub fn reduce_all(e : LambdaExpr) -> LambdaExpr {
    match _reduce_all(e) {
        Changed::Changed(e) => reduce_all(e),
        Changed::Unchanged(e) => e
    }
}

fn _reduce_all(e : LambdaExpr) -> Changed<LambdaExpr> {
    match e {
        LambdaExpr::SimpleTerm(_) => Changed::Unchanged(e),
        LambdaExpr::TermApplications(expr1, expr2) => {
            let reduce_expr1 = _reduce_all(*expr1);
            let reduce_expr2 = _reduce_all(*expr2);

            match reduce_expr1.combine(reduce_expr2) {
                Changed::Changed((red_expr1, red_expr2)) => {
                    let temp = LambdaExpr::TermApplications(Box::new(red_expr1), Box::new(red_expr2));
                    reduce_cocktail(temp, true)
                },
                Changed::Unchanged((red_expr1, red_expr2)) => {
                    let temp = LambdaExpr::TermApplications(Box::new(red_expr1), Box::new(red_expr2));
                    reduce_cocktail(temp, false)
                }
            }
        },
        LambdaExpr::Lambda(s, expr) => {
            let reduce_expr = _reduce_all(*expr);
            match reduce_expr {
                Changed::Changed(red_expr) => {
                    let temp = LambdaExpr::Lambda(s, Box::new(red_expr));
                    reduce_cocktail(temp, true)
                },
                Changed::Unchanged(red_expr) => {
                    let temp = LambdaExpr::Lambda(s, Box::new(red_expr));
                    reduce_cocktail(temp, false)
                }
            }
        },
        LambdaExpr::LetIn(lets, expr) => {
            if lets.len() == 0 {
                let reduce_expr = _reduce_all(*expr);
                match reduce_expr {
                    Changed::Changed(red_expr) => reduce_cocktail(red_expr, true),
                    Changed::Unchanged(red_expr) => reduce_cocktail(red_expr, true)
                }
                
            } else {
                let new_vec : Changed<Vec<(Symbol, LambdaExpr)>> = lets.into_iter()
                    .map(|(s, e)| _reduce_all(e).flipmerge(s))
                    .collect();
                let new_expr = _reduce_all(*expr);
                match new_vec.combine(new_expr) {
                    Changed::Changed((nv, e)) => {
                        let temp = LambdaExpr::LetIn(nv, Box::new(e));
                        reduce_cocktail(temp, true)
                    },
                    Changed::Unchanged((nv, e)) => {
                        let temp = LambdaExpr::LetIn(nv, Box::new(e));
                        reduce_cocktail(temp, false)
                    }
                }
            }
        },
        LambdaExpr::CaseOf(s, hm) => {
            let mut new_hm = HashMap::<Arg, LambdaExpr>::new();
            let mut has_changed = false;

            for key in hm.keys() {
                let lambda_expr = hm.get(key);
                match lambda_expr {
                    Some(lambda_expr) => match _reduce_all(lambda_expr.clone()) {
                        Changed::Changed(new_lambda_expr) => {
                            has_changed = true;
                            new_hm.insert(key.clone(), new_lambda_expr);
                        },
                        Changed::Unchanged(new_lambda_expr) => {
                            new_hm.insert(key.clone(), new_lambda_expr);
                        }
                    },
                    None => {}
                }
            }
            if has_changed {
                Changed::Changed(LambdaExpr::CaseOf(s, new_hm))
            } else {
                Changed::Unchanged(LambdaExpr::CaseOf(s, new_hm))
            }
        }
    }
}

fn reduce_cocktail(e : LambdaExpr, changed: bool) -> Changed<LambdaExpr> {
    match eta_reduction(e) {
        Changed::Changed(e) => reduce_cocktail(e, true),
        Changed::Unchanged(e) => {
            match beta_reduction(e) {
                Changed::Changed(e) => reduce_cocktail(e, true),
                Changed::Unchanged(e) => if changed {
                    Changed::Changed(e)
                } else {
                    Changed::Unchanged(e)
                }
            }
        }
    }
}

fn alpha_reduction(e : LambdaExpr, to : Symbol) -> Changed<LambdaExpr> {
    // Only succeeds if the 
    match e {
        LambdaExpr::Lambda(s, terms) => match _alpha_reduction(&terms, s, to) {
            Changed::Changed(expr) => Changed::Changed(LambdaExpr::Lambda(s, Box::new(expr))),
            Changed::Unchanged(expr) => Changed::Unchanged(LambdaExpr::Lambda(s, Box::new(expr)))
        },
        _ => Changed::Unchanged(e)
    }
}

// rename vars
fn _alpha_reduction(e : &LambdaExpr, from : Symbol, to : Symbol) -> Changed<LambdaExpr> {
    match e {
        LambdaExpr::SimpleTerm(a) => {
            match a {
                Atom::Term(s) => if *s == from {
                    Changed::Changed(LambdaExpr::SimpleTerm(Atom::Term(to)))
                } else {
                    Changed::Unchanged(LambdaExpr::SimpleTerm(Atom::Term(from)))
                },
                a => Changed::Unchanged(LambdaExpr::SimpleTerm(a.clone()))
            }
        },
        LambdaExpr::TermApplications(expr1, expr2) => {
            let expr1_new = _alpha_reduction(expr1, from, to);
            let expr2_new = _alpha_reduction(expr2, from, to);
            match (expr1_new, expr2_new) {
                (Changed::Changed(new_expr1), Changed::Changed(new_expr2)) => {
                    Changed::Changed(LambdaExpr::TermApplications(Box::new(new_expr1), Box::new(new_expr2)))
                },
                (Changed::Changed(new_expr1), Changed::Unchanged(new_expr2)) => {
                    Changed::Changed(LambdaExpr::TermApplications(Box::new(new_expr1), Box::new(new_expr2)))
                },
                (Changed::Unchanged(new_expr1), Changed::Changed(new_expr2)) => {
                    Changed::Changed(LambdaExpr::TermApplications(Box::new(new_expr1), Box::new(new_expr2)))
                },
                (Changed::Unchanged(new_expr1), Changed::Unchanged(new_expr2)) => {
                    Changed::Unchanged(LambdaExpr::TermApplications(Box::new(new_expr1), Box::new(new_expr2)))
                }
            }
        },
        LambdaExpr::Lambda(s, expr) => {
            let inner = _alpha_reduction(expr, from, to);
            match inner {
                Changed::Changed(inner_expr) => Changed::Changed(LambdaExpr::Lambda(*s, Box::new(inner_expr))),
                Changed::Unchanged(inner_expr) => Changed::Unchanged(LambdaExpr::Lambda(*s, Box::new(inner_expr)))
            }
        },
        _ => Changed::Unchanged(e.clone())
    }
}

// (\lambda x. E) N = E[x:=N]
fn beta_reduction(e : LambdaExpr) -> Changed<LambdaExpr> {
    match e {
        LambdaExpr::TermApplications(expr1, expr2) => {
            let display_expr1 = display(&expr1);
            if let LambdaExpr::Lambda(s, expr) = *expr1 {
                println!("beta reduction {} [{} := {}]", display_expr1, s, display(&expr2));
                substitute(&expr, s.0, &expr2)
            } else {
                Changed::Unchanged(LambdaExpr::TermApplications(expr1, expr2))
            }
        },
        _ => Changed::Unchanged(e)
    }
}

fn substitute(e : &LambdaExpr, varname : SymbolID, replace : &LambdaExpr) -> Changed<LambdaExpr> {
    match e {
        LambdaExpr::SimpleTerm(s) => {
            if let Atom::Term(s_) = s {
                if s_.0 == varname {
                    Changed::Changed(replace.clone())
                } else {
                    Changed::Unchanged(LambdaExpr::SimpleTerm((*s).clone()))
                }
            } else {
                Changed::Unchanged(LambdaExpr::SimpleTerm((*s).clone()))
            }
        },
        LambdaExpr::TermApplications(expr1, expr2) => {
            let subst1 = substitute(expr1, varname, replace);
            let subst2 = substitute(expr2, varname, replace);
            match subst1.combine(subst2) {
                Changed::Changed((expr1, expr2)) => 
                    Changed::Changed(LambdaExpr::TermApplications(Box::new(expr1), Box::new(expr2))),
                Changed::Unchanged((expr1, expr2)) => 
                    Changed::Unchanged(LambdaExpr::TermApplications(Box::new(expr1), Box::new(expr2)))
            }
        },
        LambdaExpr::Lambda(s, expr) => {// we trust that variable names are not duplicated
            let subst = substitute(expr, varname, replace);
            match subst {
                Changed::Changed(expr) => Changed::Changed(LambdaExpr::Lambda(*s, Box::new(expr))),
                Changed::Unchanged(expr) => Changed::Unchanged(LambdaExpr::Lambda(*s, Box::new(expr)))
            }
        },
        LambdaExpr::LetIn(vec, expr) => {
            let new_vec: Changed<Vec<(Symbol, LambdaExpr)>> = vec.into_iter()
                .map(|(s, e)| substitute(e, varname, replace).flipmerge(*s))
                .collect();
            let new_expr = substitute(expr, varname, replace);
            match new_vec.combine(new_expr) {
                Changed::Changed((new_vec_, new_expr_)) => {
                    Changed::Changed(LambdaExpr::LetIn(new_vec_, Box::new(new_expr_)))
                },
                Changed::Unchanged((new_vec_, new_expr_)) => {
                    Changed::Unchanged(LambdaExpr::LetIn(new_vec_, Box::new(new_expr_)))
                }
            }
        },
        LambdaExpr::CaseOf(s, hm) => {
            if s.0 == varname {
                todo!();
            } else {
                let mut new_hm = HashMap::<Atom, LambdaExpr>::new();
                todo!();
            }
        }
    }
}

// (lambda x. f x) = f
fn eta_reduction(e : LambdaExpr) -> Changed<LambdaExpr> {
    match e {
        LambdaExpr::Lambda(s, ref expr) => {
            match &**expr {
                LambdaExpr::TermApplications(expr1, expr2) => {
                    match &**expr2 {
                        LambdaExpr::SimpleTerm(t) => {
                            if *t == Atom::Term(s) && !features_var(expr1, s.0) { // Only reduce if expr1 doesn't rely on s
                                let display_expr1 = display(expr1);
                                println!("eta reduction (λ{}. {} {}) -> {}", s, display_expr1, s, display_expr1);
                                Changed::Changed(*expr1.clone())
                            } else {
                                let new_expr2 = LambdaExpr::SimpleTerm(t.clone());
                                Changed::Unchanged(LambdaExpr::Lambda(s, Box::new(LambdaExpr::TermApplications(expr1.clone(), Box::new(new_expr2)))))
                            }
                        },
                        _ => Changed::Unchanged(LambdaExpr::Lambda(s, expr.clone()))
                    }
                },
                _ => Changed::Unchanged(LambdaExpr::Lambda(s, expr.clone()))
            }
        }
        _ => Changed::Unchanged(e)
    }
}

fn atom_is_symbol(a: &Atom, s: SymbolID) -> bool {
    if let Atom::Term(s_) = a {
        s_.0 == s
    } else {
        false
    }
}

fn arg_is_symbol(a: &Arg, s: SymbolID) -> bool {
    if let Arg::Atom(a) = a {
        atom_is_symbol(a, s)
    } else {
        false
    }
}

fn features_var(e : &LambdaExpr, s : SymbolID) -> bool {
    // Returns true if `s` shows up as a variable in LambdaExpr
    match e {
        LambdaExpr::SimpleTerm(t) => atom_is_symbol(t, s),
        LambdaExpr::TermApplications(expr1, expr2) => features_var(expr1, s) || features_var(expr2, s),
        LambdaExpr::Lambda(_, expr) => features_var(expr, s), // The assumption is that the lambda expr is valid
        LambdaExpr::LetIn(vec, expr) => {
            vec.into_iter().any(|(_, e)| features_var(e, s)) || features_var(expr, s)
        },
        LambdaExpr::CaseOf(s_, hm) => {
            s_.0 == s || hm.iter().any(|(key, val)| arg_is_symbol(key, s) || features_var(val, s))
        }
    }
}
*/