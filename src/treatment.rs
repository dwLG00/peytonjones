use crate::expr::*;
use crate::symbols::*;
use std::collections::HashMap;

#[derive(Debug)]
pub enum PatternTree {
    Node(HashMap<Atom, PatternTree>),
    Expr(Option<Expr>)
}


fn add_expr(pt: &mut PatternTree, args: &[Atom], expr: &Expr) -> Result<(), ()> {
    // Mutate pt to add expr in the right location in the tree according to args
    match pt {
        PatternTree::Node(hm) => {
            if args.len() == 0 {
                Err(())
            } else {
                let a = &args[0];
                match hm.get_mut(&a) {
                    Some(pt_) => add_expr(pt_, &args[1..], expr),
                    None => {
                        if args.len() == 1 {
                            hm.insert(a.clone(), PatternTree::Expr(Some(expr.clone())));
                            Ok(())
                        } else {
                            let mut pt_ = PatternTree::Node(HashMap::new());
                            let res = add_expr(&mut pt_, &args[1..], expr);
                            hm.insert(a.clone(), pt_);
                            res
                        }
                    }
                }
            }
        },
        PatternTree::Expr(_) => {
            Err(())
        }
    }
}

pub fn treat_function_definitions<'a>(statements: &Vec<(Vec<Arg>, &'a Expr)>, ss: &mut SymbolStack) -> Result<PatternTree, ()> {
    if statements.len() == 0 {
        return Ok(PatternTree::Expr(None));
    }

    let arity = statements[0].0.len();

    let mut arg_atoms: Vec<Vec<Arg>> = Vec::new();
    for _ in [0..statements.len()] {
        arg_atoms.push(Vec::new());
    }

    for (args, _) in statements.iter() {
        //if assert_dup_symbols(args) { return Err(()); }
        if args.len() != arity { return Err(()); }
        for (i, arg) in args.iter().enumerate() {
            if !arg_atoms[i].contains(arg) {
                arg_atoms[i].push(arg.clone());
            }
        }
    }

    let mut pt = PatternTree::Node(HashMap::new());
    for (args, expr) in statements.iter() {
        let mut e = (*expr).clone();
        let mut new_args = Vec::new();
        for (i, arg) in args.iter().skip(1).enumerate() {
            new_args.push(arg.clone());
            if let Atom::Term(s) = arg {
                for j in 0..i {
                    for arg_ in arg_atoms[j].iter() {
                        if arg_ == arg { // Conflict; alpha substitute expression
                            e = e.alpha_subst(s.0, next_symbol);
                            if let Some(last) = new_args.last_mut() {
                                *last = Atom::Term(Symbol(next_symbol, false));
                            }
                            next_symbol += 1;
                        }
                    }
                }
            }
        }
        if let Err(_) = add_expr(&mut pt, &new_args, expr) { return Err(()); }
    }
    Ok(pt)
}

/* For the time being, assume all argument terms are unique
fn assert_dup_symbols(args: &Vec<Arg>) -> bool {
    for (i, arg) in args.iter().enumerate() {
        match arg {
            Arg::Atom(a) => {
                match a {
                    Atom::Term(symbol) => {
                    for item in &args[0..i] {
                        if let Atom::Term(symbol2) = item {
                            if symbol == symbol2 && !symbol.1 { // Same unbounded variable being used
                                return true;
                            }
                        }
                    }
                },
                _ => {}
                }
            }
        }
    }
    false
}
*/