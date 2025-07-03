use std::collections::HashMap;
use std::hash::Hash;
use std::fmt;
use disjoint::{DisjointSetVec, disjoint_set_vec};

use crate::aux::join;
use crate::expr::{Arg, Atom};
use crate::lambda::{AnnotatedLambdaExpr, LambdaExpr, OpTerm};
use crate::symbols::{Symbol, SymbolID};
use crate::typecheck::TypedLambdaExpr;

#[derive(Clone, Debug)]
pub enum Type {
    Infer(u32),
    Int,
    String,
    Bool,
    Func(Box<Type>, Box<Type>),
    List(Box<Type>)
}

impl Type {
    fn map_infer<F>(&self, f: &mut F) -> Option<Type> where F: FnMut(u32) -> Option<Type> {
        match self {
            Self::Int | Self::String | Self::Bool => Some(self.clone()),
            Self::List(t) => Some(Self::List(Box::new(t.map_infer(f)?))),
            Self::Func(t1, t2) => Some(Self::Func(Box::new(t1.map_infer(f)?), Box::new(t2.map_infer(f)?))),
            Self::Infer(id) => f(*id)
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => write!(f, "int"),
            Self::String => write!(f, "str"),
            Self::Bool => write!(f, "bool"),
            Self::Func(t1, t2) => match **t1 {
                Self::Func(_, _) => {
                    write!(f, "({}) -> {}", t1, t2)
                },
                _ => write!(f, "{} -> {}", t1, t2)
            },
            Self::List(t) => write!(f, "[{}]", t),
            Self::Infer(v) => write!(f, "T{}", v)
        }
    }
}

pub type ExprID = u32;
pub type ExprTypeTable = HashMap<ExprID, Type>;
pub type SymbolTypeMap = HashMap<SymbolID, Type>;
pub type LambdaExprWithID = AnnotatedLambdaExpr<SymbolID, ExprID>;

/*
impl fmt::Display for LambdaExprWithID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StringTerm(t, s) => {
                write!(f, "\"{s}\": {t}")
            },
            Self::IntTerm(t, n) => write!(f, "{n}: {t}"),
            Self::BoolTerm(t, b) => if *b {
                write!(f, "true: {t}")
            } else {
                write!(f, "false: {t}")
            },
            Self::VarTerm(t, s) => write!(f, "s{s}: {t}"),
            Self::OpTerm(t, op) => write!(f, "{op}: {t}"),
            Self::EmptyList(t) => write!(f, "[]: {t}"),
            Self::ListCon(t, car, cdr) => write!(f, "[{car} : {cdr}]: {t}"),
            Self::TermApplications(t, func, app) => write!(f, "({func} ({app})): {t}"),
            Self::Lambda(t, s, expr) => write!(f, "(λs{s}. {expr}): {t}"),
            Self::LetIn(t, vec, expr) => {
                let vec_s = vec.iter().map(|(s, e)| format!("s{s} := {e},")).collect::<String>();
                let vec_s = vec_s.trim_end_matches(",");
                write!(f, "(let {vec_s} in {expr}): {t}")
            },
            Self::CaseOf(t, s, hm) => {
                let vec_s = hm.iter().map(|(key, val)| format!("({key} => {val}),")).collect::<String>();
                let vec_s = vec_s.trim_end_matches(",");
                write!(f, "(case s{s}: {vec_s}): {t}")
            },
            Self::TryThen(t, first, second) => write!(f, "({first} █ {second}): {t}"),
            Self::FAIL => write!(f, "FAIL")
        }
    }
}
*/

#[derive(Debug)]
pub struct TypeTable {
    expr_table: ExprTypeTable,
    symbol_table: SymbolTypeMap,
    variable_set: DisjointSetVec<Option<Type>>,
    next_vartype: u32
}

impl TypeTable {
    pub fn new() -> TypeTable {
        TypeTable {
            expr_table: ExprTypeTable::new(),
            symbol_table: SymbolTypeMap::new(),
            variable_set: DisjointSetVec::new(),
            next_vartype: 0
        }
    }

    pub fn spawn_with_context(&self) -> TypeTable {
        TypeTable {
            expr_table: ExprTypeTable::new(),
            symbol_table: self.symbol_table.clone(),
            variable_set: self.variable_set.clone(),
            next_vartype: self.next_vartype
        }
    }

    pub fn grab_infer(&mut self) -> (u32, Type) {
        let temp = self.next_vartype;
        self.next_vartype += 1;
        self.variable_set.push(None);
        (temp, Type::Infer(temp))
    }

    fn insert_expr(&mut self, e: ExprID, t: Type) {
        self.expr_table.insert(e, t);
    }

    pub fn insert_symbol(&mut self, s: SymbolID, t: Type) {
        self.symbol_table.insert(s, t);
    }

    fn set_variable(&mut self, v: u32, t: Type) {
        let root = self.variable_set.root_of(v as usize);
        self.variable_set[root] = Some(t);
    }

    fn get_expr(&self, e: &ExprID) -> Option<&Type> {
        self.expr_table.get(e)
    }

    fn get_symbol(&self, s: &SymbolID) -> Option<&Type> {
        self.symbol_table.get(s)
    }

    fn get_variable(&self, v: &u32) -> &Option<Type> {
        let root = self.variable_set.root_of(*v as usize);
        match self.variable_set.get(root) {
            Some(t) => t,
            None => &None
        }
    }

    fn get_variable_or_infer(&self, v: &u32) -> Type {
        let root = self.variable_set.root_of(*v as usize);
        match self.variable_set.get(root) {
            Some(t) => match t {
                Some(t) => t.clone(),
                None => Type::Infer(root as u32)
            },
            None => Type::Infer(root as u32)
        }
    }

    fn get_root(&self, v: u32) -> u32 {
        self.variable_set.root_of(v as usize) as u32
    }

    fn merge_variables(&mut self, v1: u32, v2: u32) -> Result<Type, String> {
        let t1 = self.get_variable(&v1).clone();
        let t2 = self.get_variable(&v2).clone();
        self.variable_set.join(v1 as usize, v2 as usize);

        let root = Type::Infer(self.get_root(v1));
        let target_type: Option<Type> = match (t1, t2) {
            (Some(t1), Some(t2)) => {
                Some(unify(self, t1.clone(), t2.clone())?)
            },
            (Some(t), None) => Some(t.clone()),
            (None, Some(t)) => Some(t.clone()),
            (None, None) => None
        };
        let target_type = match target_type {
            Some(t) => {
                self.set_variable(v1, t.clone());
                t
            },
            None => root
        };
        Ok(target_type)
    }

    fn specify(&self, t: Type) -> Type {
        match t {
            Type::Infer(v) => self.get_variable_or_infer(&v),
            Type::Int => Type::Int,
            Type::String => Type::String,
            Type::Bool => Type::Bool,
            Type::List(t) => Type::List(Box::new(self.specify(*t))),
            Type::Func(t1, t2) => Type::Func(Box::new(self.specify(*t1)), Box::new(self.specify(*t2)))
        }
    }
}

pub fn identify(s: LambdaExpr) -> LambdaExprWithID {
    // Return AST with the same 
    let mut counter: u32 = 0;
    let mut register_node = |_| {
        let temp = counter;
        counter += 1;
        temp
    };
    s.map(&mut register_node)
}

fn unify(tt: &mut TypeTable, t1: Type, t2: Type) -> Result<Type, String> {
    match (t1.clone(), t2.clone()) {
        (Type::Infer(v1), Type::Infer(v2)) => {
            if v1 == v2 {
                Ok(tt.get_variable_or_infer(&v1))
            } else {
                tt.merge_variables(v1, v2)
            }
        },
        (Type::Infer(v), _) => {
            match tt.get_variable(&v) {
                Some(t) => {
                    unify(tt, t.clone(), t2)
                },
                None => {
                    tt.set_variable(v, t2.clone());
                    Ok(t2)
                }
            }
        },
        (_, Type::Infer(v)) => {
            match tt.get_variable(&v) {
                Some(t) => {
                    unify(tt, t.clone(), t1)
                },
                None => {
                    tt.set_variable(v, t1.clone());
                    Ok(t1)
                }
            }
        },
        (Type::List(t1), Type::List(t2)) => {
            let inner = unify(tt, *t1, *t2)?;
            Ok(Type::List(Box::new(inner)))
        },
        (Type::Func(t1a, t1b), Type::Func(t2a, t2b)) => {
            let func = unify(tt, *t1a, *t2a)?;
            let app = unify(tt, *t1b, *t2b)?;
            Ok(Type::Func(Box::new(func), Box::new(app)))
        },
        (Type::Bool, Type::Bool) => Ok(Type::Bool),
        (Type::Int, Type::Int) => Ok(Type::Int),
        (Type::String, Type::String) => Ok(Type::String),
        _ => {
            Err(format!("[unify] Failed to unify {:?} and {:?}", t1, t2))
        }
    }
}

pub fn infer(tt: &mut TypeTable, expr: &LambdaExprWithID) -> Result<Type, String> {
    match expr {
        AnnotatedLambdaExpr::StringTerm(id, _) => {
            tt.insert_expr(*id, Type::String);
            Ok(Type::String)
        },
        AnnotatedLambdaExpr::IntTerm(id, _) => {
            tt.insert_expr(*id, Type::Int);
            Ok(Type::Int)
        },
        AnnotatedLambdaExpr::BoolTerm(id, _) => {
            tt.insert_expr(*id, Type::Bool);
            Ok(Type::Bool)
        },
        AnnotatedLambdaExpr::OpTerm(id, op) => {
            let op_type = get_op_type(tt, *op);
            tt.insert_expr(*id, op_type.clone());
            Ok(op_type)
        },
        AnnotatedLambdaExpr::Lambda(id, s, expr) => {
            let (_, t) = tt.grab_infer();
            tt.insert_symbol(*s, t.clone());
            let t2 = infer(tt, expr)?;
            let t = tt.specify(t);
            let my_type = Type::Func(Box::new(t), Box::new(t2));
            tt.insert_expr(*id, my_type.clone());
            Ok(my_type)
        },
        AnnotatedLambdaExpr::VarTerm(id, s) => {
            let t = match tt.get_symbol(s) {
                Some(t) => t.clone(),
                None => { 
                    //return Err(format!("[infer] Expected symbol `s{}` to have type, but none found in table", s)); 
                    let (_, temp) = tt.grab_infer();
                    tt.insert_symbol(*s, temp.clone());
                    temp
                }
            };
            tt.insert_expr(*id, t.clone());
            Ok(t)
        },
        AnnotatedLambdaExpr::TermApplications(id, func, app) => {
            let func_type = infer(tt, func)?;
            let app_type = infer(tt, app)?;
            let (_, temp) = tt.grab_infer();
            unify(tt, func_type, Type::Func(Box::new(app_type), Box::new(temp.clone())))?; // MAYBE WRONG
            let temp = tt.specify(temp);
            tt.insert_expr(*id, temp.clone());
            Ok(temp)
        },
        AnnotatedLambdaExpr::EmptyList(id) => {
            let (_, temp) = tt.grab_infer();
            let my_type = Type::List(Box::new(temp));
            tt.insert_expr(*id, my_type.clone());
            Ok(my_type)
        },
        AnnotatedLambdaExpr::ListCon(id, car, cdr) => {
            let car_type = infer(tt, car)?;
            let cdr_type = infer(tt, cdr)?;
            unify(tt, cdr_type.clone(), Type::List(Box::new(car_type.clone())))?;
            let cdr_type = tt.specify(cdr_type);
            tt.insert_expr(*id, cdr_type.clone());
            Ok(cdr_type)
        },
        AnnotatedLambdaExpr::LetIn(id, vec, expr) => {
            for (s, e) in vec.iter() {
                let t = infer(tt, e)?;
                tt.insert_symbol(*s, t);
            }
            let expr_t = infer(tt, expr)?;
            tt.insert_expr(*id, expr_t.clone());
            Ok(expr_t)
        },
        AnnotatedLambdaExpr::CaseOf(id, s, exprs) => {
            // resolve it to Type(s) -> Type(exprs.body)
            let temp: Result<Vec<(Type, Type)>, String> = exprs.iter().map(|(arg, expr)| {
                let body_t = infer(tt, expr); // Parse the expression's type first, to populate 
                let arg_t = infer_arg(tt, arg);
                join(arg_t, body_t)
            }).collect();
            let mut iter = temp?.into_iter();
            let mut first = iter.next().ok_or_else(|| format!("[infer] Expected Case expression to have at least 1 case"))?;
            for (head, body) in iter {
                let (h, b) = first;
                first = (unify(tt, h, head)?, unify(tt, b, body)?);
            }
            let head_type = match tt.get_symbol(s) {
                Some(head) => {
                    unify(tt, head.clone(), first.0)?
                },
                None => first.0
            };
            tt.insert_symbol(*s, head_type.clone());
            let body_type = first.1.clone();
            tt.insert_expr(*id, first.1);
            Ok(body_type)
        },
        AnnotatedLambdaExpr::TryThen(id, expr1, expr2) => {
            match **expr2 {
                AnnotatedLambdaExpr::FAIL => {
                    let expr1_type = infer(tt, expr1)?;
                    tt.insert_expr(*id, expr1_type.clone());
                    Ok(expr1_type)
                },
                _ => {
                    let expr1_type = infer(tt, expr1)?;
                    let expr2_type = infer(tt, expr2)?;
                    let unified_type = unify(tt, expr1_type, expr2_type)?;
                    tt.insert_expr(*id, unified_type.clone());
                    Ok(unified_type)
                }
            }
        },
        AnnotatedLambdaExpr::FAIL => {
            Err(format!("[infer] Type of FAIL should never be evaluated!"))
        }
    }
}

fn get_op_type(tt: &mut TypeTable, op: OpTerm) -> Type {
    match op {
        OpTerm::Add | OpTerm::Sub | OpTerm::Div | OpTerm::Mul => Type::Func(
            Box::new(Type::Int),
            Box::new(Type::Func(
                Box::new(Type::Int),
                Box::new(Type::Int)
            ))
        ),
        OpTerm::Gt | OpTerm::Lt => Type::Func(
            Box::new(Type::Int),
            Box::new(Type::Func(
                Box::new(Type::Int),
                Box::new(Type::Bool)
            ))
        ),
        OpTerm::Eq => {
            let (_, temp) = tt.grab_infer();
            Type::Func(
                Box::new(temp.clone()),
                Box::new(Type::Func(
                    Box::new(temp),
                    Box::new(Type::Bool)
                ))
            )
        },
        OpTerm::IfElse => {
            let (_, temp) = tt.grab_infer();
            Type::Func(
                Box::new(Type::Bool),
                Box::new(Type::Func(
                    Box::new(temp.clone()),
                    Box::new(Type::Func(
                        Box::new(temp.clone()),
                        Box::new(temp.clone()))
                    )
                ))
            )
        }
    }
}

fn infer_arg(tt: &mut TypeTable, arg: &Arg) -> Result<Type, String> {
    match arg {
        Arg::EmptyList => {
            let (_, temp) = tt.grab_infer();
            Ok(Type::List(Box::new(temp)))
        },
        Arg::ListCon(car, cdr) => {
            let car_type = infer_arg(tt, car)?;
            let cdr_type = infer_arg(tt, cdr)?;
            unify(tt, cdr_type, Type::List(Box::new(car_type)))
        },
        Arg::Atom(a) => match a {
            Atom::BoolLit(_) => Ok(Type::Bool),
            Atom::StringLit(_) => Ok(Type::String),
            Atom::IntLit(_) => Ok(Type::Int),
            Atom::Term(s) => match tt.get_symbol(&s.0) {
                Some(t) => Ok(t.clone()),
                None => Ok(tt.grab_infer().1)
            }
        }
    }
}