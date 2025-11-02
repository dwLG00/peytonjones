use std::collections::HashMap;
use std::hash::Hash;
use std::fmt;
use disjoint::{DisjointSetVec, disjoint_set_vec};

use crate::aux::join;
use crate::expr::{Arg, Atom};
use crate::lambda::{AnnotatedLambdaExpr, LambdaExpr, OpTerm};
use crate::symbols::{Symbol, SymbolID, SymbolTable};


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

    fn get_infers(&self) -> Vec<u32> {
        match self {
            Self::Int | Self::String | Self::Bool => vec![],
            Self::List(t) => t.get_infers(),
            Self::Func(t1, t2) => {
                let mut v = t1.get_infers();
                v.extend_from_slice(&t2.get_infers());
                v
            },
            Self::Infer(i) => vec![*i]
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

impl LambdaExprWithID {
    pub fn get_type(&self, tt: &TypeTable) -> Type {
        let t = self.map_node(|id| {
            let t = tt.get_expr_specify(&id);
            //println!("{}, {:?}", id, t);
            t
        });
        let unwrapped = t.unwrap();
        unwrapped.unwrap()
    }
}

#[derive(Debug, Clone)]
pub struct TypeTable {
    expr_table: ExprTypeTable, // Maps expression type variable -> actual type value
    symbol_table: SymbolTypeMap, // Maps symbol -> actual type value
    global_symbol_table: SymbolTypeMap, // Maps global symbol -> actual type value
    variable_set: DisjointSetVec<Option<Type>>, // Used for type unification
    next_vartype: u32,
    next_expr: ExprID
}

impl TypeTable {
    pub fn new() -> TypeTable {
        TypeTable {
            expr_table: ExprTypeTable::new(),
            symbol_table: SymbolTypeMap::new(),
            global_symbol_table: SymbolTypeMap::new(),
            variable_set: DisjointSetVec::new(),
            next_vartype: 0,
            next_expr: 0
        }
    }

    pub fn grab_expr(&mut self) -> ExprID {
        let temp = self.next_expr;
        self.next_expr += 1;
        temp
    }

    pub fn clone_expr(&mut self, e: ExprID) -> Option<ExprID> {
        // Creates a new id with same type as given id, and returns it
        let e_new = self.grab_expr();
        let t = self.get_expr(&e)?.clone();
        self.insert_expr(e_new, t);
        Some(e_new)
    }

    pub fn grab_infer(&mut self) -> (u32, Type) {
        let temp = self.next_vartype;
        self.next_vartype += 1;
        self.variable_set.push(None);
        (temp, Type::Infer(temp))
    }

    pub fn insert_expr(&mut self, e: ExprID, t: Type) {
        self.expr_table.insert(e, t);
    }

    pub fn insert_symbol(&mut self, s: SymbolID, t: Type) {
        self.symbol_table.insert(s, t);
    }

    pub fn insert_global_symbol(&mut self, s: SymbolID, t: Type) {
        self.global_symbol_table.insert(s, t);
    }

    fn set_variable(&mut self, v: u32, t: Type) {
        let root = self.variable_set.root_of(v as usize);
        self.variable_set[root] = Some(t);
    }

    pub fn get_expr(&self, e: &ExprID) -> Option<&Type> {
        self.expr_table.get(e)
    }

    pub fn get_expr_specify(&self, e: &ExprID) -> Option<Type> {
        let t = self.get_expr(e)?;
        Some(self.specify(t.clone()))
    }

    pub fn get_symbol(&self, s: &SymbolID) -> Option<&Type> {
        self.symbol_table.get(s)
    }

    fn get_symbol_safe(&mut self, s: &SymbolID) -> Option<Type> {
        // Global type takes precedence over local type
        let res = self.global_symbol_table.get(s).cloned();
        match res {
            None => self.get_symbol(s).cloned(),
            Some(t) => Some(self.clone_with_new_vars(&t))
        }
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

    fn is_same_var(&self, v1: u32, v2: u32) -> bool {
        self.variable_set.is_joined(v1 as usize, v2 as usize)
    }

    fn clone_with_new_vars(&mut self, t: &Type) -> Type {
        let mut hm = HashMap::new();
        self.clone_with_new_vars_aux(&mut hm, t)
    }

    fn clone_with_new_vars_aux(&mut self, hm: &mut HashMap<u32, u32>, t: &Type) -> Type {
        match t {
            Type::String | Type::Int | Type::Bool => t.clone(),
            Type::List(t) => Type::List(Box::new(self.clone_with_new_vars_aux(hm, t))),
            Type::Func(t1, t2) => {
                let t1_ = self.clone_with_new_vars_aux(hm, t1);
                let t2_ = self.clone_with_new_vars_aux(hm, t2);
                Type::Func(Box::new(t1_), Box::new(t2_))
            },
            Type::Infer(v) => {
                match hm.get(v) {
                    Some(replacement) => Type::Infer(*replacement),
                    None => {
                        let (new_type_id, new_type) = self.grab_infer();
                        hm.insert(*v, new_type_id);
                        new_type
                    }
                }
            }
        }
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

pub fn identify(s: LambdaExpr, tt: &mut TypeTable) -> LambdaExprWithID {
    // Return AST with the same 
    let mut register_node = |_| {
        tt.grab_expr()
    };
    s.map(&mut register_node)
}

fn unify(tt: &mut TypeTable, t1: Type, t2: Type) -> Result<Type, String> {
    match (t1.clone(), t2.clone()) {
        (Type::Infer(v1), Type::Infer(v2)) => {
            if tt.is_same_var(v1, v2) {
                let t = tt.get_variable_or_infer(&v1);
                Ok(t)
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

pub fn infer_assignment(tt: &mut TypeTable, expr: &LambdaExprWithID, s: SymbolID) -> Result<Type, String> {
    let t = infer(tt, expr)?;
    match tt.get_symbol_safe(&s) {
        Some(t2) => {
            unify(tt, t, t2)
        },
        None => Ok(t)
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
            let t = match tt.get_symbol_safe(s) {
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
                let body_t = body_t.map(|t| tt.specify(t));
                join(arg_t, body_t)
            }).collect();
            let mut iter = temp?.into_iter();
            let mut first = iter.next().ok_or_else(|| format!("[infer] Expected Case expression to have at least 1 case"))?;
            for (head, body) in iter {
                let (h, b) = first;
                first = (unify(tt, h, head)?, unify(tt, b, body)?);
            }
            let head_type = match tt.get_symbol_safe(s) {
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

// ===================== DEBUGGING CODE ======================
pub fn infer_assignment_d(tt: &mut TypeTable, expr: &LambdaExprWithID, s: SymbolID) -> Result<Type, String> {
    let t = infer_d(tt, expr, 0)?;
    match tt.get_symbol_safe(&s) {
        Some(t2) => {
            unify_d(tt, t, t2, 0)
        },
        None => Ok(t)
    }
}

fn unify_d(tt: &mut TypeTable, t1: Type, t2: Type, n: usize) -> Result<Type, String> {
    let tabs = "  ".repeat(n);
    println!("{tabs}Unifying {t1} and {t2}...");
    match (t1.clone(), t2.clone()) {
        (Type::Infer(v1), Type::Infer(v2)) => {
            if tt.is_same_var(v1, v2) {
                let t = tt.get_variable_or_infer(&v1);
                println!("{tabs}[u] T{v1} and T{v2} both point to {t}");
                Ok(t)
            } else {
                println!("{tabs}[u] Found different variables T{v1} and T{v2}, hence merging");
                tt.merge_variables(v1, v2)
            }
        },
        (Type::Infer(v), _) => {
            match tt.get_variable(&v) {
                Some(t) => {
                    println!("{tabs}[u] Found that T{v} points to {t}...");
                    unify_d(tt, t.clone(), t2, n+1)
                },
                None => {
                    println!("{tabs}[u] T{v} doesn't point to anything, so T{v} := {t2}");
                    tt.set_variable(v, t2.clone());
                    Ok(t2)
                }
            }
        },
        (_, Type::Infer(v)) => {
            match tt.get_variable(&v) {
                Some(t) => {
                    println!("{tabs}[u] Found that T{v} points to {t}...");
                    unify_d(tt, t.clone(), t1, n+1)
                },
                None => {
                    println!("{tabs}[u] T{v} doesn't point to anything, so T{v} := {t1}");
                    tt.set_variable(v, t1.clone());
                    Ok(t1)
                }
            }
        },
        (Type::List(t1), Type::List(t2)) => {
            println!("{tabs}[u] Both lists, so unwrapping...");
            let inner = unify_d(tt, *t1, *t2, n+1)?;
            Ok(Type::List(Box::new(inner)))
        },
        (Type::Func(t1a, t1b), Type::Func(t2a, t2b)) => {
            println!("{tabs}[u] Both functions, so unwrapping...");
            let func = unify_d(tt, *t1a, *t2a, n+1)?;
            let app = unify_d(tt, *t1b, *t2b, n+1)?;
            Ok(Type::Func(Box::new(func), Box::new(app)))
        },
        (Type::Bool, Type::Bool) => {
            println!("{tabs}[u] Both bools!");
            Ok(Type::Bool)
        },
        (Type::Int, Type::Int) => {
            println!("{tabs}[u] Both ints!");
            Ok(Type::Int)
        },
        (Type::String, Type::String) => {
            println!("{tabs}[u] Both strings!");
            Ok(Type::String)
        },
        _ => {
            Err(format!("[unify] Failed to unify {:?} and {:?}", t1, t2))
        }
    }
}

pub fn infer_d(tt: &mut TypeTable, expr: &LambdaExprWithID, n: usize) -> Result<Type, String> {
    let tabs = "  ".repeat(n);
    println!("{tabs}Inferring {expr}...");
    let res = match expr {
        AnnotatedLambdaExpr::StringTerm(id, _) => {
            tt.insert_expr(*id, Type::String);
            println!("{tabs}[i] It's a string");
            Ok(Type::String)
        },
        AnnotatedLambdaExpr::IntTerm(id, _) => {
            tt.insert_expr(*id, Type::Int);
            println!("{tabs}[i] It's an int");
            Ok(Type::Int)
        },
        AnnotatedLambdaExpr::BoolTerm(id, _) => {
            tt.insert_expr(*id, Type::Bool);
            println!("{tabs}[i] It's a bool");
            Ok(Type::Bool)
        },
        AnnotatedLambdaExpr::OpTerm(id, op) => {
            let op_type = get_op_type(tt, *op);
            tt.insert_expr(*id, op_type.clone());
            println!("{tabs}[i] It's an op - specifically {}", op_type);
            Ok(op_type)
        },
        AnnotatedLambdaExpr::Lambda(id, s, expr) => {
            let (_, t) = tt.grab_infer();
            tt.insert_symbol(*s, t.clone());
            println!("{tabs}[i] It's a lambda s{s} - say {t}");
            let t2 = infer_d(tt, expr, n+1)?;
            let t = tt.specify(t);
            println!("{tabs}[i] Figured out that the body should be {t2}, and the head should be {t}");
            let my_type = Type::Func(Box::new(t), Box::new(t2));
            println!("{tabs}[i] so {my_type}");
            tt.insert_expr(*id, my_type.clone());
            Ok(my_type)
        },
        AnnotatedLambdaExpr::VarTerm(id, s) => {
            println!("{tabs}[i] Checking what it points to...");
            let t = match tt.get_symbol_safe(s) {
                Some(t) => {
                    println!("{tabs}[i] It's {t}");
                    t.clone()
                },
                None => {
                    //return Err(format!("[infer] Expected symbol `s{}` to have type, but none found in table", s)); 
                    let (_, temp) = tt.grab_infer();
                    println!("{tabs}[i] It's an unspecified variable - say {temp}");
                    tt.insert_symbol(*s, temp.clone());
                    temp
                }
            };
            tt.insert_expr(*id, t.clone());
            Ok(t)
        },
        AnnotatedLambdaExpr::TermApplications(id, func, app) => {
            println!("{tabs}[i] It's a term application...");
            println!("{tabs}[i] Inferring func...");
            let func_type = infer_d(tt, func, n+1)?;
            println!("{tabs}[i] Inferring app...");
            let app_type = infer_d(tt, app, n+1)?;
            let (_, temp) = tt.grab_infer();
            println!("{tabs}[i]Unifying...");
            unify_d(tt, func_type, Type::Func(Box::new(app_type), Box::new(temp.clone())), n+1)?; // MAYBE WRONG
            println!("{tabs}[i] Specifying {temp}...");
            let temp = tt.specify(temp);
            println!("{tabs}[i] Inferred that the application should be {temp}");
            tt.insert_expr(*id, temp.clone());
            Ok(temp)
        },
        AnnotatedLambdaExpr::EmptyList(id) => {
            let (_, temp) = tt.grab_infer();
            let my_type = Type::List(Box::new(temp));
            println!("{tabs}[i] It's an empty list - say {my_type}");
            tt.insert_expr(*id, my_type.clone());
            Ok(my_type)
        },
        AnnotatedLambdaExpr::ListCon(id, car, cdr) => {
            println!("{tabs}[i] It's a listcon...");
            println!("{tabs}[i] Inferring car...");
            let car_type = infer_d(tt, car, n+1)?;
            println!("{tabs}[i] Inferring cdr...");
            let cdr_type = infer_d(tt, cdr, n+1)?;
            println!("{tabs}[i] Unifying...");
            unify_d(tt, cdr_type.clone(), Type::List(Box::new(car_type.clone())), n+1)?;
            let cdr_type = tt.specify(cdr_type);
            println!("{tabs}[i] Inferred that the listcon should be {cdr_type}");
            tt.insert_expr(*id, cdr_type.clone());
            Ok(cdr_type)
        },
        AnnotatedLambdaExpr::LetIn(id, vec, expr) => {
            println!("{tabs}[i] It's a let-in");
            for (s, e) in vec.iter() {
                println!("{tabs}[i] Inferring item of let-in...");
                let t = infer_d(tt, e, n+1)?;
                tt.insert_symbol(*s, t);
            }
            println!("{tabs}[i] Inferring body...");
            let expr_t = infer_d(tt, expr, n+1)?;
            println!("{tabs}[i] Got that the body should have type {expr_t}");
            tt.insert_expr(*id, expr_t.clone());
            Ok(expr_t)
        },
        AnnotatedLambdaExpr::CaseOf(id, s, exprs) => {
            // resolve it to Type(s) -> Type(exprs.body)
            println!("{tabs}[i] It's a case-of");
            let temp: Result<Vec<(Type, Type)>, String> = exprs.iter().map(|(arg, expr)| {
                println!("{tabs}[i] Checking one case...");
                let body_t = infer_d(tt, expr, n+1); // Parse the expression's type first, to populate 
                println!("{tabs}[i] ...and its corresponding argument");
                let arg_t = infer_arg_d(tt, arg, n+1);
                let body_t = body_t.map(|t| tt.specify(t));
                join(arg_t, body_t)
            }).collect();
            let mut iter = temp?.into_iter();
            let mut first = iter.next().ok_or_else(|| format!("[infer] Expected Case expression to have at least 1 case"))?;
            for (head, body) in iter {
                let (h, b) = first;
                println!("{tabs}[i] Unifying...");
                first = (unify_d(tt, h, head, n+1)?, unify_d(tt, b, body, n+1)?);
            }
            println!("{tabs}[i] Unifying symbol s{s} with head...");
            let head_type = match tt.get_symbol_safe(s) {
                Some(head) => {
                    unify_d(tt, head.clone(), first.0, n+1)?
                },
                None => first.0
            };
            tt.insert_symbol(*s, head_type.clone());
            let body_type = first.1.clone();
            println!("{tabs}[i] Got that the head should have type {}, and the body should have type {}", head_type, body_type);
            tt.insert_expr(*id, first.1);
            Ok(body_type)
        },
        AnnotatedLambdaExpr::TryThen(id, expr1, expr2) => {
            match **expr2 {
                AnnotatedLambdaExpr::FAIL => {
                    let expr1_type = infer_d(tt, expr1, n+1)?;
                    println!("{tabs}[i] Tail type is FAIL so the expression type must be {}", expr1_type);
                    tt.insert_expr(*id, expr1_type.clone());
                    Ok(expr1_type)
                },
                _ => {
                    println!("{tabs}[i] first");
                    let expr1_type = infer_d(tt, expr1, n+1)?;
                    println!("{tabs}[i] second");
                    let expr2_type = infer_d(tt, expr2, n+1)?;
                    println!("{tabs}[i] Unifying..");
                    let unified_type = unify_d(tt, expr1_type, expr2_type, n+1)?;
                    println!("{tabs}[i] whole try expression has type {}", unified_type);
                    tt.insert_expr(*id, unified_type.clone());
                    Ok(unified_type)
                }
            }
        },
        AnnotatedLambdaExpr::FAIL => {
            Err(format!("[infer] Type of FAIL should never be evaluated!"))
        }
    };
    if let Ok(ref t) = res {
        println!("{tabs}Inferred type {t} for {expr}");
    }
    res
}

fn infer_arg_d(tt: &mut TypeTable, arg: &Arg, n: usize) -> Result<Type, String> {
    let tabs = "  ".repeat(n);
    println!("{tabs}[ia] Inferring arg {arg}...");
    match arg {
        Arg::EmptyList => {
            let (_, temp) = tt.grab_infer();
            println!("{tabs}[ia] Empty list, say {}...", Type::List(Box::new(temp.clone())));
            Ok(Type::List(Box::new(temp)))
        },
        Arg::ListCon(car, cdr) => {
            println!("{tabs}[ia] Inferring car...");
            let car_type = infer_arg_d(tt, car, n+1)?;
            println!("{tabs}[ia] Inferring cdr...");
            let cdr_type = infer_arg_d(tt, cdr, n+1)?;
            println!("{tabs}[ia] Unifying...");
            let res = unify_d(tt, cdr_type, Type::List(Box::new(car_type)), n+1);
            if let Ok(ref t) = res {
                println!("{tabs}[ia] Unified to {t}");
            }
            res
        },
        Arg::Atom(a) => match a {
            Atom::BoolLit(_) => {
                println!("{tabs}[ia] Found bool");
                Ok(Type::Bool)
            },
            Atom::StringLit(_) => {
                println!("{tabs}[ia] Found string");
                Ok(Type::String)
            },
            Atom::IntLit(_) => {
                println!("{tabs}[ia] Found int");
                Ok(Type::Int)
            },
            Atom::Term(s) => match tt.get_symbol_safe(&s.0) {
                Some(t) => {
                    println!("{tabs}[ia] It's a symbol that points to {t}");
                    Ok(t.clone())
                },
                None => {
                    let t = tt.grab_infer().1;
                    println!("{tabs}[ia] It's an unset arg, say {t}");
                    Ok(t)
                }
            }
        }
    }
}
// ===================== END DEBUGGING CODE ======================

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
            Atom::Term(s) => match tt.get_symbol_safe(&s.0) {
                Some(t) => Ok(t.clone()),
                None => Ok(tt.grab_infer().1)
            }
        }
    }
}

pub fn correct(tt: &mut TypeTable, expr: &LambdaExprWithID) -> Result<(), String> {
    expr.at_node(&mut |exprid| {
        let t = tt.get_expr(&exprid).ok_or(format!("[correct] Expression with id {} doesn't have corresponding type", exprid))?;
        let t = tt.specify(t.clone());
        tt.insert_expr(exprid, t);
        Ok::<(), String>(())
    })?;
    Ok(())
}

pub fn valid_type(t: &Type) -> bool {
    let mut context = Vec::new();
    valid_type_aux(t, &mut context)
}

fn valid_type_aux(t: &Type, context: &mut Vec<u32>) -> bool {
    match t {
        Type::Bool | Type::Int | Type::String => true,
        Type::List(t) => valid_type_aux(t, context),
        Type::Func(t1, t2) => {
            context.extend_from_slice(&t1.get_infers());
            valid_type_aux(t2, context)
        },
        Type::Infer(i) => context.contains(i)
    }
}