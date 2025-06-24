use std::collections::HashMap;
use std::hash::Hash;
use std::os::macos::raw::stat;

use crate::lambda::*;
use crate::expr::*;
use crate::symbols::*;
use crate::treatment::{treat_function_definitions, PatternTree};

/*
pub fn translate(statements: Vec<Statement>, next_symbol: SymbolID) -> Result<Vec<(SymbolID, LambdaExpr)>, ()> {
    let mut v: Vec<(SymbolID, LambdaExpr)> = Vec::new();

    let function_map = match create_function_map(&statements) {
        Ok(hm) => hm,
        Err(_) => { return Err(()); }
    };

    let mut next_symbol = next_symbol;

    for symbol in function_map.keys().into_iter() {
        match function_map.get(symbol) {
            Some(body) => {
                let maybe_pattern_tree = treat_function_definitions(body, next_symbol);
                match maybe_pattern_tree {
                    Ok((pattern_tree, ns)) => {
                        let lambda_expr = build_lambda_expr(symbol.0, pattern_tree);
                        next_symbol = ns;
                        v.push((symbol.0, lambda_expr));
                    },
                    Err(_) => { return Err(()); }
                }
            },
            None => { return Err(()); }
        }
    }
    Ok(v)
}

pub fn create_function_map<'a>(statements: &'a Vec<Statement>) -> Result<HashMap<Symbol, Vec<(Vec<Arg>, &'a Expr)>>, ()> {
    // Create a hashmap of function name => vector of function definitions
    let mut hm = HashMap::<Symbol, Vec<(Vec<Arg>, &Expr)>>::new();
    for statement in statements.iter() {
        match statement {
            Statement::MainDef(expr) => {
                if let Some(_) = hm.get(&Symbol(0, false)) { return Err(()); } // There should only be 1 main function
                hm.insert(Symbol(0, false), vec![(Vec::new(), expr)]);
            },
            Statement::FuncDef(symbol, args, expr) => {
                match hm.get_mut(symbol) {
                    Some(v) => {
                        v.push((args.clone(), expr));
                    },
                    None => {
                        hm.insert(*symbol, vec![(args.clone(), expr)]);
                    }
                }
            }
        }
    }
    Ok(hm)
}

pub fn build_lambda_expr(symbol_id: SymbolID, pt: PatternTree) -> LambdaExpr {
    todo!();
}

pub fn translate_expr(expr: Expr) -> LambdaExpr {
    todo!();
}
*/