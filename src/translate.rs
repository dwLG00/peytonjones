use std::collections::BTreeMap;
use std::collections::HashMap;
use std::hash::Hash;
use std::os::macos::raw::stat;

use crate::aux::Recursible;
use crate::lambda::*;
use crate::expr::*;
use crate::symbols::*;
//use crate::treatment::{treat_function_definitions, PatternTree};


pub fn translate(statements: Vec<Statement>, ss: &mut SymbolStack) -> Result<Vec<(SymbolID, LambdaExpr)>, String> {
    translate_aux(statements, ss, false)
}

fn translate_aux(statements: Vec<Statement>, ss: &mut SymbolStack, in_let: bool) -> Result<Vec<(SymbolID, LambdaExpr)>, String> {
    let mut v: Vec<(SymbolID, LambdaExpr)> = Vec::new();

    let (function_map, main_statement) = match create_function_btree_map(statements) {
        Ok(hm) => hm,
        Err(s) => { return Err(s); }
    };
    if !validate_function_btree_map(&function_map) {
        return Err(format!("[translate] Code contains function definitions with contrasting arity"));
    }

    for (symbol, body) in function_map.iter() {
        v.push(
            (*symbol, build_function_def(body.iter().map(|t| &t.0), body[0].1, ss)?)
        );
    }

    if !in_let {
        match main_statement {
            Some(main) => {
                match main {
                    Statement::MainDef(e) => {
                        v.push((u32::MAX, expr_to_lambda(&e, ss)?))
                    },
                    _ => { return Err(format!("[translate] Expected main definition, got function definition"))}
                }
            },
            None => {
                // Don't throw an error - yet (helps with debugging)
                //return Err(format!("[translate] No main definition found"));
            }
        }
    }
    Ok(v)
}

fn create_function_map(statements: &Vec<Statement>) -> Result<(HashMap<SymbolID, Vec<(Statement, usize)>>, Option<Statement>), String> {
    let mut statement_buckets: HashMap<SymbolID, Vec<(Statement, usize)>> = HashMap::new();
    let mut main_statement = None;

    for statement in statements.iter() {
        match statement {
            Statement::MainDef(_) => { main_statement = Some(statement.clone()); },
            Statement::FuncDef(s, args, _) => match statement_buckets.get_mut(&s.0) {
                Some(v) => { v.push((statement.clone(), args.len())); },
                None => { statement_buckets.insert(s.0, vec![(statement.clone(), args.len())]); }
            }
        }
    }
    Ok((statement_buckets, main_statement))
}

fn create_function_btree_map(statements: Vec<Statement>) -> Result<(BTreeMap<SymbolID, Vec<(Statement, usize)>>, Option<Statement>), String> {
    let mut statement_buckets: BTreeMap<SymbolID, Vec<(Statement, usize)>> = BTreeMap::new();
    let mut main_statement = None;
    for statement in statements.into_iter() {
        match statement {
            Statement::MainDef(_) => { main_statement = Some(statement); },
            Statement::FuncDef(s, ref args, _) => {
                let arglen = args.len();
                match statement_buckets.get_mut(&s.0) {
                    Some(v) => { v.push((statement, arglen)) },
                    None => { statement_buckets.insert(s.0, vec![(statement, arglen)]); }
                }
            }
        }
    }
    Ok((statement_buckets, main_statement))
}

fn validate_function_map(hm: &HashMap<SymbolID, Vec<(Statement, usize)>>) -> bool {
    // Ensure that all function definitions for the same function have the same arity
    for (_, statement_vec) in hm.iter() {
        if statement_vec.len() > 1 { // If only 1 definition, then arity should already be correct
            let first_arity = statement_vec[0].1;
            let all_same_arity = statement_vec.iter().all(|(_, arity)| *arity == first_arity);
            if !all_same_arity {
                return false;
            }
        }
    }
    true
}

fn validate_function_btree_map(bm: &BTreeMap<SymbolID, Vec<(Statement, usize)>>) -> bool {
    for (_, statement_vec) in bm.iter() {
        if statement_vec.len() > 1 { // If only 1 definition, then arity should already be correct
            let first_arity = statement_vec[0].1;
            let all_same_arity = statement_vec.iter().all(|(_, arity)| *arity == first_arity);
            if !all_same_arity {
                return false;
            }
        }
    }
    true
}

#[derive(Clone)]
struct Match {
    args: Vec<SymbolID>,
    body: Vec<(Vec<Arg>, Expr)>,
    if_fail: Option<Expr>
}

impl Match {
    fn arity(&self) -> usize {
        self.args.len()
    }
}

fn build_function_def<'a>(fundefs: impl Iterator<Item=&'a Statement>, arity: usize, ss: &mut SymbolStack) -> Result<LambdaExpr, String> {
    let mut match_ = fundef_to_match(fundefs, arity, ss)?;
    let args = match_.args.clone();
    let target_expr = match_to_lambda_expr(&mut match_, ss)?;
    let lambda = args.iter().rev().fold(target_expr, |acc, x| LambdaExpr::Lambda((), *x, Box::new(acc)));
    let lambda = lambda.recurse(simp_case); // Simplify trivial cases
    Ok(lambda)
}

fn fundef_to_match<'a>(fundefs: impl Iterator<Item=&'a Statement>, arity: usize, ss: &mut SymbolStack) -> Result<Match, String> {
    let mut args: Vec<SymbolID> = Vec::with_capacity(arity);
    let mut body = Vec::new();

    // populate args
    for _ in 0..arity {
        args.push(ss.grab());
    }

    for fundef in fundefs {
        match fundef {
            Statement::FuncDef(_, _args, e) => { // Assume symbols are all the same
                body.push((_args.clone(), e.clone()));
            },
            Statement::MainDef(_) => { return Err(format!("[fundef_to_match] Expected FuncDef, got MainDef")); }
        }
    }

    Ok(Match {
        args: args,
        body: body,
        if_fail: None
    })
}

fn match_to_lambda_expr(m: &mut Match, ss: &mut SymbolStack) -> Result<LambdaExpr, String> {
    match match_reduce_vars(m) {
        Ok(_) => {
            match_reduce(m, ss)
        }
        Err(s) => Err(s)
    }
}

fn match_reduce_vars(m: &mut Match) -> Result<(), String> {
    // Variable rule
    let mut retain_idx = Vec::<bool>::with_capacity(m.arity());
    for i in 0..m.arity() {
        if m.body.iter().all(|(args, _)| args[i].is_var()) {
            for (arg, body) in m.body.iter_mut() {
                let old_symbol = match &arg[i] {
                    Arg::Atom(t) => match t {
                        Atom::Term(s) => s.0,
                        _ => { return Err(format!("[match_reduce] Expected Arg(Atom::Symbol)")); }
                    },
                    _ => { return Err(format!("[match_reduce] Expected Arg(Atom::Symbol)")); }
                };
                *body = body.alpha_subst(old_symbol, m.args[i]);
            }
            retain_idx.push(false);
        } else {
            retain_idx.push(true);
        }
    }
    retain(&mut m.args, &retain_idx);
    for (arg, _) in m.body.iter_mut() {
        retain(arg, &retain_idx);
    }
    Ok(())
}

fn match_reduce_empty(m: &Match, ss: &mut SymbolStack) -> Result<LambdaExpr, String> {
    if m.arity() > 0 {
        return Err(format!("[match_reduce_empty] Expected Match with arity 0, found arity {}", m.arity()));
    } else if m.body.len() == 0 { // Only 1 body expression
        Ok(expr_to_lambda(&m.body[0].1, ss)?)
    } else { 
        let failcase = match &m.if_fail {
            Some(e) => expr_to_lambda(&e, ss)?,
            None => LambdaExpr::FAIL
        };
        let lambda_expr: Result<LambdaExpr, String> = m.body.iter().rev().fold(Ok(failcase), |acc, (_, e)| Ok(LambdaExpr::TryThen((), Box::new(expr_to_lambda(e, ss)?), Box::new(acc?))));
        lambda_expr
    }
}

fn match_reduce(m: &Match, ss: &mut SymbolStack) -> Result<LambdaExpr, String> {
    if m.arity() == 0 {
        match_reduce_empty(m, ss)
    } else {
        let car = m.args[0];
        let cdr = m.args[1..].to_vec();
        // build temp hashmap; then we can use this to build the lambda expression hashmap
        let mut temp_hm: HashMap<Arg, Vec<(Vec<Arg>, Expr)>> = HashMap::new();
        // parts for resolving list constructor
        let car_symbol = ss.grab();
        let cdr_symbol = ss.grab();
        let mut list_vec: Vec<(Vec<Arg>, Expr)> = Vec::with_capacity(m.body.len());
        // parts for resolving variable
        let var_symbol = ss.grab();
        let mut var_vec: Vec<(Vec<Arg>, Expr)> = Vec::with_capacity(m.body.len());

        for (args, e) in m.body.iter() {
            match &args[0] {
                Arg::Atom(a) => match a {
                    Atom::Term(s) => { // It's a variable!
                        if s.1 { // Bounded variable (i.e. some other value)
                            match temp_hm.get_mut(&args[0]) {
                                Some(v) => v.push((args[1..].to_vec(), e.clone())),
                                None => {
                                    temp_hm.insert(
                                        args[0].clone(),
                                        vec![(args[1..].to_vec(), e.clone())]
                                    );
                                }
                            }
                        } else { // Unbound variable
                            var_vec.push((args[1..].to_vec(), e.alpha_subst(s.0, var_symbol)));
                        }
                    },
                    _ => { // Non-variable
                        match temp_hm.get_mut(&args[0]) {
                            Some(v) => v.push((args[1..].to_vec(), e.clone())),
                            None => {
                                temp_hm.insert(
                                    args[0].clone(),
                                    vec![(args[1..].to_vec(), e.clone())]
                                );
                            }
                        }
                    }
                },
                Arg::EmptyList => {
                    match temp_hm.get_mut(&args[0]) {
                        Some(v) => v.push((args[1..].to_vec(), e.clone())),
                        None => {
                            temp_hm.insert(
                                args[0].clone(),
                                vec![(args[1..].to_vec(), e.clone())]
                            );
                        }
                    }
                },
                Arg::ListCon(car_, cdr_) => {
                    if car_.like_var() { // Contains an unbounded variable
                        if let Arg::Atom(_) = **car_ {
                            // Ignore if car is a plain variable
                        } else {
                            return Err(format!("[match_reduce] Found list with unbound variable as car of list"))
                        }
                    }
                    let auged_args: Vec<Arg> = [*car_.clone(), *cdr_.clone()].iter().chain(args[1..].iter()).map(|arg| (*arg).clone()).collect();
                    let new_e = {
                        let mut e = e.clone();
                        if let Arg::Atom(Atom::Term(s)) = **car_ {
                            if !s.1 {
                                e = e.alpha_subst(s.0, car_symbol);
                            }
                        }
                        if let Arg::Atom(Atom::Term(s)) = **cdr_ {
                            if !s.1 {
                                e = e.alpha_subst(s.0, cdr_symbol);
                            }
                        }
                        e
                    };
                    list_vec.push((auged_args, new_e));
                }
            }
        }

        let mut hm: HashMap<Arg, LambdaExpr> = HashMap::new();
        for (arg, list) in temp_hm.into_iter() {
            let new_m = Match {
                args: cdr.clone(),
                body: list,
                if_fail: None
            };
            let lambda_expr = match_reduce(&new_m, ss)?;
            hm.insert(arg, lambda_expr);
        }
        if list_vec.len() > 0 { // We have list args
            let new_m = Match {
                args: [car_symbol, cdr_symbol].iter().chain(m.args[1..].iter()).map(|a| *a).collect(),
                body: list_vec,
                if_fail: None
            };
            let lambda_expr = match_reduce(&new_m, ss)?;
            hm.insert(
                Arg::ListCon(
                    Box::new(Arg::Atom(Atom::Term(Symbol(car_symbol, false)))),
                    Box::new(Arg::Atom(Atom::Term(Symbol(cdr_symbol, false))))
                ),
                lambda_expr
            );
        }
        if var_vec.len() > 0 {
            let new_m = Match {
                args: cdr.clone(),
                body: var_vec,
                if_fail: None
            };
            let lambda_expr = match_reduce(&new_m, ss)?;
            hm.insert(Arg::Atom(Atom::Term(Symbol(var_symbol, false))), lambda_expr);
        }
        Ok(LambdaExpr::CaseOf((), car, hm))
    }
}

fn expr_to_lambda(e: &Expr, ss: &mut SymbolStack) -> Result<LambdaExpr, String> {
    match e {
        Expr::App(e1, e2) => Ok(LambdaExpr::TermApplications((), Box::new(expr_to_lambda(e1, ss)?), Box::new(expr_to_lambda(e2, ss)?))),
        Expr::Binop(b, e1, e2) => Ok(LambdaExpr::TermApplications(
            (),
            Box::new(LambdaExpr::TermApplications((), Box::new(LambdaExpr::OpTerm((), OpTerm::from_binop(*b))), Box::new(expr_to_lambda(e1, ss)?))), 
            Box::new(expr_to_lambda(e2, ss)?)
        )),
        Expr::Atom(a) => match a {
            Atom::StringLit(s) => Ok(LambdaExpr::StringTerm((), s.clone())),
            Atom::IntLit(n) => Ok(LambdaExpr::IntTerm((), *n)),
            Atom::BoolLit(b) => Ok(LambdaExpr::BoolTerm((), *b)),
            Atom::Term(s) => Ok(LambdaExpr::VarTerm((), s.0))
        },
        Expr::IfElse(e1, e2, e3) => Ok(LambdaExpr::TermApplications((), Box::new(
            LambdaExpr::TermApplications((), 
                Box::new(LambdaExpr::TermApplications((), 
                    Box::new(LambdaExpr::OpTerm((), OpTerm::IfElse)),
                    Box::new(expr_to_lambda(e1, ss)?)
                )),
                Box::new(expr_to_lambda(e2, ss)?)
            )),
            Box::new(expr_to_lambda(e3, ss)?)
        )),
        Expr::List(v) => if v.len() == 0 {
            Ok(LambdaExpr::EmptyList(()))
        } else {
            let v: Result<Vec<LambdaExpr>, String> = v.iter().rev().map(|e| expr_to_lambda(e, ss)).collect();
            Ok(fold_lambda_list(v?.into_iter()))
        },
        Expr::ListCon(e1, e2) => Ok(LambdaExpr::ListCon((), Box::new(expr_to_lambda(e1, ss)?), Box::new(expr_to_lambda(e2, ss)?))),
        Expr::LetIn(s, e) => Ok(LambdaExpr::LetIn((), translate_aux(s.clone(), ss, true)?, Box::new(expr_to_lambda(e, ss)?)))
    }
}

fn fold_lambda_list(it: impl Iterator<Item=LambdaExpr>) -> LambdaExpr {
    it.fold(LambdaExpr::EmptyList(()), |acc, x| LambdaExpr::ListCon((), Box::new(x), Box::new(acc)))
}

fn retain<T>(v: &mut Vec<T>, retain_idx: &Vec<bool>) {
    let mut retain_iter = retain_idx.iter();
    v.retain(|_| *retain_iter.next().unwrap());
}