use crate::expr::{Statement, Expr, Atom};
use crate::tokens::{Token};


/*
Grammar:

STATEMENT :=    TERM = EXPR

EXPR :=         ATOM
|               LIST
|               ( EXPR )
|               EXPR EXPR
|               EXPR BINOP EXPR
|               let STATEMENT in EXPR
|               if EXPR then EXPR else EXPR

LIST :=         [ ]
|               [ EXPR : EXPR ]

ATOM :=         TERM
|               STR_LITERAL
|               NUM_LITERAL

BINOP :=        + | - | * | / | < | >
*/


pub fn parse(tokens : Vec<Token>) -> Vec<Statement> {
    let mut statements : Vec<Statement> = Vec::new();


    todo!()
}

pub fn parse_expr() -> Expr {
    todo!()
}