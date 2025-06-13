use crate::{expr::Atom, symbols::Symbol};


#[derive(Clone)]
pub enum LambdaExpr {
    SimpleTerm(Atom),
    TermApplications(Box<LambdaExpr>, Box<LambdaExpr>),
    Lambda(Symbol, Box<LambdaExpr>),
    LetIn(Vec<(String, LambdaExpr)>, Box<LambdaExpr>)
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
                let new_vec : Changed<Vec<(String, LambdaExpr)>> = lets.into_iter()
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
                substitute(&expr, s, &expr2)
            } else {
                Changed::Unchanged(LambdaExpr::TermApplications(expr1, expr2))
            }
        },
        _ => Changed::Unchanged(e)
    }
}

fn substitute(e : &LambdaExpr, varname : Symbol, replace : &LambdaExpr) -> Changed<LambdaExpr> {
    match e {
        LambdaExpr::SimpleTerm(s) => {
            if (*s).clone() == Atom::Term(varname) {
                Changed::Changed(replace.clone())
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
            let new_vec: Changed<Vec<(String, LambdaExpr)>> = vec.into_iter()
                .map(|(s, e)| substitute(e, varname, replace).flipmerge(s.to_string()))
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
                            if *t == Atom::Term(s) && !features_var(expr1, s) { // Only reduce if expr1 doesn't rely on s
                                let display_expr1 = display(&*expr1);
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

fn features_var(e : &LambdaExpr, s : Symbol) -> bool {
    // Returns true if `s` shows up as a variable in LambdaExpr
    match e {
        LambdaExpr::SimpleTerm(t) => *t == Atom::Term(s),
        LambdaExpr::TermApplications(expr1, expr2) => features_var(&*expr1, s) || features_var(&*expr2, s),
        LambdaExpr::Lambda(_, expr) => features_var(&*expr, s), // The assumption is that the lambda expr is valid
        LambdaExpr::LetIn(vec, expr) => {
            vec.into_iter().any(|(_, e)| features_var(&*e, s)) || features_var(&*expr, s)
        }
    }
}

pub fn display(e : &LambdaExpr) -> String {
    match e {
        LambdaExpr::SimpleTerm(s) => s.to_string(),
        LambdaExpr::TermApplications(expr1, expr2) => {
            let s1 = display(&*expr1);
            let s2 = display(&*expr2);
            format!("{s1} {s2}")
        },
        LambdaExpr::Lambda(s, expr) => {
            let s = s.0;
            let expr_s = display(&*expr);
            format!("(λs{s}. {expr_s})")
        },
        LambdaExpr::LetIn(vec, expr) => {
            let expr_s = display(&*expr);
            let vec_s = vec.iter().map(|(s, e)| format!("{} := {},", s, display(&*e))).collect::<String>();
            let vec_s = vec_s.trim_end_matches(",");
            format!("(let {} in {})", vec_s, expr_s)
        }
    }
}