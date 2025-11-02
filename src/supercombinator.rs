use std::collections::HashMap;
use std::collections::HashSet;

use crate::supercombinator;
use crate::symbols::*;
use crate::lambda::*;
use crate::typing::*;
use crate::expr::*;

use std::collections::*;

#[derive(Debug)]
pub struct Supercombinator {
    variables: Vec<SymbolID>,
    body: SupercombinatorExpr<SymbolID, ExprID>
}

pub fn supercombinate(lambda_exprs: &mut Vec<(u32, AnnotatedLambdaExpr<SymbolID, ExprID>)>, symbol_stack: &mut SymbolStack, type_table: &mut TypeTable) -> Vec<Supercombinator> {
    let mut supercombinator_store = Vec::new();
    let sstack = &mut symbol_stack.to_sstack();
    for (symbol, expr) in lambda_exprs {
        let top_level_sc_body = reduce_lambda(expr, &mut supercombinator_store, sstack, type_table);
    }
    return supercombinator_store
}

pub fn supercombinate_debug(lambda_exprs: &BTreeMap<u32, AnnotatedLambdaExpr<u32, u32>>, symbol_stack: &mut SymbolStack, type_table: &mut TypeTable) {
    let mut supercombinator_store = Vec::new();
    let sstack = &mut symbol_stack.to_sstack();
    let mut function_definitions = Vec::new();
    for (symbol, expr) in lambda_exprs {
        let top_level_sc_body = reduce_lambda(expr, &mut supercombinator_store, sstack, type_table);
        function_definitions.push((*symbol, top_level_sc_body));
    }
    println!("Supercombinators:");
    for (i, supercombinator) in supercombinator_store.iter().enumerate() {
        println!("Y{}: {:?}", i, supercombinator);
    }
    println!();
    println!("Function definitions:");
    for (symbol, sc_body) in function_definitions.iter() {
        println!("s{}: {:?}", symbol, sc_body);
    }
}

pub fn reduce_lambda(lambda_expr: &AnnotatedLambdaExpr<SymbolID, ExprID>, supercombinator_store: &mut Vec<Supercombinator>, sstack: &mut SStack, type_table: &mut TypeTable) -> SupercombinatorExpr<SymbolID, ExprID> {
    match lambda_expr {
        AnnotatedLambdaExpr::BoolTerm(n, value) => SupercombinatorExpr::BoolTerm(*n, *value),
        AnnotatedLambdaExpr::StringTerm(n, value) => SupercombinatorExpr::StringTerm(*n, value.clone()),
        AnnotatedLambdaExpr::IntTerm(n, value) => SupercombinatorExpr::IntTerm(*n, *value),
        AnnotatedLambdaExpr::OpTerm(n, op) => SupercombinatorExpr::OpTerm(*n, *op),
        AnnotatedLambdaExpr::VarTerm(n, s) => SupercombinatorExpr::VarTerm(*n, *s),
        AnnotatedLambdaExpr::EmptyList(n) => SupercombinatorExpr::EmptyList(*n),
        AnnotatedLambdaExpr::ListCon(n, car, cdr) => SupercombinatorExpr::ListCon(
            *n, 
            Box::new(reduce_lambda(car, supercombinator_store, sstack, type_table)), 
            Box::new(reduce_lambda(cdr, supercombinator_store, sstack, type_table))
        ),
        AnnotatedLambdaExpr::TermApplications(n, func, arg) => SupercombinatorExpr::TermApplications(
            *n, 
            Box::new(reduce_lambda(func, supercombinator_store, sstack, type_table)),
            Box::new(reduce_lambda(arg, supercombinator_store, sstack, type_table))
        ),
        AnnotatedLambdaExpr::TryThen(n, expr1, expr2) => SupercombinatorExpr::TryThen(
            *n, 
            Box::new(reduce_lambda(expr1, supercombinator_store, sstack, type_table)),
            Box::new(reduce_lambda(expr2, supercombinator_store, sstack, type_table))
        ),
        AnnotatedLambdaExpr::LetIn(n, statements, body) => {
            let mut sc_statements = Vec::new();
            for (s, expr) in statements.iter() {
                let sc_expr = reduce_lambda(expr, supercombinator_store, sstack, type_table);
                sc_statements.push((*s, sc_expr));
            }
            let sc_body = reduce_lambda(body, supercombinator_store, sstack, type_table);
            SupercombinatorExpr::LetIn(*n, sc_statements, Box::new(sc_body))
        },

        AnnotatedLambdaExpr::CaseOf(n, s, cases) => {
            let mut hm = HashMap::new();
            for (arg, expr) in cases.iter() {
                let sc_expr = reduce_lambda(expr, supercombinator_store, sstack, type_table);
                hm.insert(arg.clone(), sc_expr);
            }
            SupercombinatorExpr::CaseOf(*n, *s, hm)
        },
        AnnotatedLambdaExpr::Lambda(_, s, body) => { // Assume (\lambda s. E)
            // Reduce the body
            let sc_expr = reduce_lambda(body, supercombinator_store, sstack, type_table); // Reduce E first
            // Extract free variables from the body, ignoring the current symbol (since the expression we want to emit is effectively ($Y a b c ...) := \lambda s. E)
            sstack.push_stack();
            sstack.add_symbol(*s);
            let free_vars = free_variables(&sc_expr, sstack);
            sstack.pop_stack();
            // So now free_vars contains all the free variables in E, minus s, which will be parameterized and provided
            // Then alpha-substitute the body (keeping the free variables for assignment)
            let free_vars_vec: Vec<(SymbolID, ExprID)> = free_vars.iter().cloned().collect(); // [(a, T_a), (b, T_b), (c, T_c), ...]
            let alpha_sub_map = free_vars_vec.iter().map(|(x, _)| (x.clone(), sstack.grab())).collect(); // [(a, a'), (b, b'), (c, c'), ...]
            let alphad_sc_expr = sc_expr.alpha_multisubst(&alpha_sub_map); // Alpha-substituted expression: E[a/a'][b/b'][c/c']...
            // build the supercombinator and add it to store
            let index = supercombinator_store.len();
            let mut alphad_free_vars_vec: Vec<SymbolID> = alpha_sub_map.iter().map(|x| x.1).collect(); // The ids of the new (alpha-subbed) variables
            alphad_free_vars_vec.push(*s); // [a', b', c', ..., s]
            let supercombinator = Supercombinator {
                variables: alphad_free_vars_vec, // order: [a, b, c, ..., s] implies $Y a b c ... = E
                body: alphad_sc_expr
            };
            supercombinator_store.push(supercombinator);
            // build supercombination application expression (i.e. $Y a b c ... to replace the lambda expression (\lambda x. \lambda y. ...) a b c) and return
            let supercombinator_expr = build_supercombinator_expr(index, &free_vars_vec, sc_expr.get_type(), type_table); // This is all type-assigned and everything
            supercombinator_expr
        },
        AnnotatedLambdaExpr::FAIL => SupercombinatorExpr::FAIL
    }
}

fn build_supercombinator_expr(index: usize, alphad_vars_vec: &Vec<(SymbolID, ExprID)>, t: &ExprID, type_table: &mut TypeTable) -> SupercombinatorExpr<SymbolID, ExprID> {
    // If we have [(a, T_a), (b, T_b), (c, T_c), ...] then we build
    // $Y a b c ...
    // Build the supercombinator expression, assigning expr per each
    let mut expr_id = type_table.grab_expr();
    let mut head: SupercombinatorExpr<SymbolID, ExprID> = SupercombinatorExpr::Supercombinator(expr_id, index as u32);
    for (symbol, tid) in alphad_vars_vec.iter() {
        expr_id = type_table.grab_expr();
        head = SupercombinatorExpr::TermApplications(expr_id, Box::new(head), Box::new(SupercombinatorExpr::VarTerm(*tid, *symbol)));
    }
    // Assign types in the type table
    let mut sc_type_head = type_table.get_expr(t).expect("A").clone();
    let mut cur = &mut head;
    loop {
        match cur {
            SupercombinatorExpr::TermApplications(e, func, arg) => {
                type_table.insert_expr(*e, sc_type_head.clone());
                let arg_type = type_table.get_expr(arg.get_type()).expect("B").clone();
                sc_type_head = Type::Func(Box::new(arg_type), Box::new(sc_type_head));
                cur = func.as_mut();
            },
            SupercombinatorExpr::Supercombinator(e, _) => {
                type_table.insert_expr(*e, sc_type_head);
                break;
            },
            v => {panic!("[build_supercombinator_expr] Didn't expect to find value `{:?}` in supercombinator application expression", v)}
        }
    }
    head
}

pub fn free_variables(lambda_expr: &SupercombinatorExpr<SymbolID, ExprID>, sstack: &mut SStack) -> HashSet<(SymbolID, ExprID)> {
    let mut variables = HashSet::new();
    free_variables_aux(lambda_expr, sstack, &mut variables);
    variables
}

fn free_variables_aux(lambda_expr: &SupercombinatorExpr<SymbolID, ExprID>, sstack: &mut SStack, out: &mut HashSet<(SymbolID, ExprID)>) {
    match lambda_expr {
        SupercombinatorExpr::LetIn(_, let_terms, body) => {
            sstack.push_stack();
            for (s, _) in let_terms.iter() {
                sstack.add_symbol(*s);
            }
            free_variables_aux(body, sstack, out);
            sstack.pop_stack();
        },
        SupercombinatorExpr::TermApplications(_, func, arg) => {
            free_variables_aux(func, sstack, out);
            free_variables_aux(arg, sstack, out);
        },
        SupercombinatorExpr::TryThen(_, expr1, expr2) => {
            free_variables_aux(expr1, sstack, out);
            free_variables_aux(expr2, sstack, out);
        },
        SupercombinatorExpr::CaseOf(_, _, bodies) => {
            for (arg, body) in bodies.iter() {
                sstack.push_stack();
                arg_symbols(arg, sstack);
                free_variables_aux(body, sstack, out);
                sstack.pop_stack();
            }
        },
        SupercombinatorExpr::ListCon(_, car, cdr) => {
            free_variables_aux(car, sstack, out);
            free_variables_aux(cdr, sstack, out);
        }
        SupercombinatorExpr::VarTerm(t, s) => {
            if !sstack.contains(*s) {
                // Abort if symbol is already added
                for (s_, _) in out.iter() {
                    if *s_ == *s {
                        return;
                    }
                }
                // Insert symbol + type into the hashset
                out.insert((*s, *t));
            }
        },
        _ => {}
    }
}

pub fn arg_symbols(arg: &Arg, sstack: &mut SStack) {
    // Add all unbound variables in the argument into the symbol stack
    match arg {
        Arg::Atom(a) => match a {
            Atom::Term(s) => {
                if !s.1 { // unbound
                    sstack.add_symbol(s.0);
                }
            },
            _ => {}
        },
        Arg::ListCon(car, cdr) => {
            arg_symbols(car, sstack);
            arg_symbols(cdr, sstack);
        },
        _ => {}
    }
}