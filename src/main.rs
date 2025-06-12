mod expr;
mod lambda;
mod symbols;
mod tokens;
mod lex;
mod parse;
use crate::lambda::{LambdaExpr, display, reduce_all};
use crate::lex::{lex};
use crate::parse::{parse};

use std::fs::File;
use std::error::Error;
use std::io::Read;
use std::env;

fn main() -> Result<(), Box<dyn Error>> {
    // (lambda x. (lambda y. x y z)) (lambda k. k k) a
    /*
    let lambda_block = LambdaExpr::Lambda("x".to_string(), 
        Box::new(LambdaExpr::Lambda("y".to_string(), 
            Box::new(LambdaExpr::TermApplications(Box::new(LambdaExpr::TermApplications(
                Box::new(LambdaExpr::SimpleTerm("x".to_string())), 
                Box::new(LambdaExpr::SimpleTerm("y".to_string()))
            )), Box::new(LambdaExpr::SimpleTerm("z".to_string()))
            ))
        ))
    );
    let expr_ = LambdaExpr::TermApplications(Box::new(
        LambdaExpr::TermApplications(Box::new(lambda_block), Box::new(
            LambdaExpr::Lambda("k".to_string(), Box::new(LambdaExpr::TermApplications(
                Box::new(LambdaExpr::SimpleTerm("k".to_string())), Box::new(LambdaExpr::SimpleTerm("k".to_string()))
            )))
        ))
    ), Box::new(
        LambdaExpr::SimpleTerm("a".to_string())
    ));
    let expr = LambdaExpr::LetIn(vec![("z".to_string(), LambdaExpr::SimpleTerm("b".to_string()))], Box::new(expr_));
    println!("{}", display(&expr));
    let new_expr = reduce_all(expr);
    println!("{}", display(&new_expr));
    */

    let args: Vec<String> = env::args().collect();
    let filename = &args[1];

    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;

    /*
    let expr : String = format!("let x = 5 in (concat [0:[1:[]]] [x])");
    let lex_result = lex(expr);
    match lex_result {
        Ok(toks) => { println!("{:?}", toks); },
        Err(msg) => { println!("Error: {}", msg); }
    }
    */
    let lex_result = lex(contents);
    match lex_result {
        Ok(toks) => {
            println!("Lexed tokens: {:?}", toks);
            let parse_result = parse(toks);
            match parse_result {
                Ok(statements) => {
                    for (i, statement) in statements.iter().enumerate() {
                        println!("[{}] {:?}", i, statement);
                    }
                },
                Err(_) => {
                    println!("Parsing error...");
                }
            }
        },
        Err(msg) => { println!("Error: {}", msg); }
    }
    Ok(())

}
