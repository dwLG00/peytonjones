mod expr;
mod lambda;
mod symbols;
mod tokens;
mod lex;
mod parse;
use crate::lambda::{LambdaExpr, display, reduce_all};
use crate::lex::{lex};

fn main() {
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
    let expr : String = format!("let x = 5 in (concat [0:[1:[]]] [x])");
    let lex_result = lex(expr);
    match lex_result {
        Ok(toks) => { println!("{:?}", toks); },
        Err(msg) => { println!("Error: {}", msg); }
    }
}
