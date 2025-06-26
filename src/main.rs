mod expr;
mod lambda;
mod symbols;
mod tokens;
mod lex;
mod parse;
mod translate;
mod treatment;
mod aux;
//use crate::lambda::{LambdaExpr, display, reduce_all};
use crate::lambda::{LambdaExpr};
use crate::lex::{lex};
use crate::parse::{parse};
use crate::translate::{translate};

use std::fs::File;
use std::error::Error;
use std::io::Read;
use std::env;

fn main() -> Result<(), Box<dyn Error>> {
    // (lambda x. (lambda y. x y z)) (lambda k. k k) a

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
                Ok((statements, mut ss)) => {
                    for (i, statement) in statements.iter().enumerate() {
                        println!("[{}] {:?}", i, statement);
                    }
                    let translate_result = translate(statements, &mut ss);
                    match translate_result {
                        Ok(translations) => {
                            for (symbol, lambda) in translations.iter() {
                                println!("{} => {}", symbol, lambda);
                            }
                        },
                        Err(msg) => {
                            println!("Translation error: {}", msg)
                        }
                    }
                },
                Err(msg) => {
                    println!("Parsing error: {}", msg);
                }
            }
        },
        Err(msg) => { println!("Lexing error: {}", msg); }
    }
    Ok(())

}
