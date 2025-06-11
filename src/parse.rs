use std::iter::Peekable;

use crate::expr::{Statement, Expr, Atom};
use crate::symbols::{Symbol, SymbolStack};
use crate::tokens::{Token};


/*
Grammar:

STATEMENT :=    TERM {ATOM} = EXPR NEWLINE

EXPR :=         ATOM
|               LIST
|               ( {NEWLINE} EXPR {NEWLINE} )
|               EXPR EXPR
|               EXPR BINOP EXPR
|               let STATEMENT in EXPR
|               if {NEWLINE} EXPR {NEWLINE} then {NEWLINE} EXPR {NEWLINE} else {NEWLINE} EXPR

LIST :=         [ ]
|               [ {NEWLINE} EXPR {NEWLINE} : {NEWLINE} EXPR {NEWLINE} ]

ATOM :=         TERM
|               STR_LITERAL
|               NUM_LITERAL

BINOP :=        + | - | * | / | < | >
*/

pub fn parse(tokens : Vec<Token>) -> Result<Vec<Statement>, ()> {
    let mut statements : Vec<Statement> = Vec::new();
    let mut symbol_stack = SymbolStack::new();
    let mut it = tokens.iter().peekable();

    while it.peek().is_some() {
        let next_statement = parse_statement(&mut it, &mut symbol_stack);
        match next_statement {
            Ok(statement) => { statements.push(statement); },
            Err(_) => { return Err(()); }
        }
    }
    Ok(statements)
}

fn parse_statement<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Statement, ()> 
    where I: Iterator<Item=&'a Token>
{
    // match Term
    let expect_symbol = parse_symbol(it, ss);
    match expect_symbol {
        Err(_) => Err(()),
        Ok(symbol) => {
            // match 0 or more Atoms
            ss.push_stack();
            let mut atoms = Vec::new();
            loop {
                let expect_atom = parse_atom_weak(it, ss);
                match expect_atom {
                    Ok(atom) => atoms.push(atom),
                    Err(maybe_tok) => {
                        match maybe_tok {
                            Some(tok) => match tok {
                                Token::Newline => { it.next(); }, // skip newlines atp
                                _ => { break; }
                            },
                            None => { // Reached end of iterator
                                return Err(());
                            }
                        }
                    }
                }
            }
            // match eq
            if !parse_eq(it) {
                return Err(());
            }
            let expect_expr = parse_expr_greedy(it, ss);
            ss.pop_stack();
            match expect_expr {
                Ok(expr) => Ok(Statement::FuncDef(symbol, atoms, expr)),
                Err(_) => Err(())
            }
        }
    }
}

/*
Grammar:

STATEMENT :=    TERM {ATOM} = EXPR NEWLINE

EXPR :=         ATOM
|               LIST
|               ( {NEWLINE} EXPR {NEWLINE} )
|               EXPR EXPR
|               EXPR BINOP EXPR
|               let STATEMENT in EXPR
|               if {NEWLINE} EXPR {NEWLINE} then {NEWLINE} EXPR {NEWLINE} else {NEWLINE} EXPR

LIST :=         [ ]
|               [ {NEWLINE} EXPR {NEWLINE} : {NEWLINE} EXPR {NEWLINE} ]

ATOM :=         TERM
|               STR_LITERAL
|               NUM_LITERAL
|               BOOL_LITERAL

BINOP :=        + | - | * | / | < | >
*/

fn parse_expr<'a>(it: &mut impl Iterator<Item=&'a Token>, ss: &mut SymbolStack) -> Result<Expr, ()> {

    todo!()
}

fn parse_expr_greedy<'a>(it: &mut impl Iterator<Item=&'a Token>, ss: &mut SymbolStack) -> Result<Expr, ()> {
    todo!()
}

fn parse_symbol<'a>(it: &mut impl Iterator<Item=&'a Token>, ss: &mut SymbolStack) -> Result<Symbol, ()> {
    let expect_term = it.next();
    match expect_term {
        Some(eterm) => match eterm {
            Token::Term(t) => {
                let symbol = ss.get_symbol(t);
                Ok(symbol)
            },
            _ => Err(())
        },
        None => Err(())
    }
}

pub fn parse_eq<'a>(it: &mut impl Iterator<Item=&'a Token>) -> bool {
    let expect_eq = it.next();
    match expect_eq {
        Some(eeq) => match eeq {
            Token::Eq => true,
            _ => false
        },
        None => false
    }
}

fn parse_atom_weak<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Atom, Option<Token>>
    where I: Iterator<Item=&'a Token>
{
    // Match atom from it.peek(); advance if it succeeds, and don't if it doesn't
    let peek = it.peek();
    match peek {
        Some(token) => match token {
            Token::Term(s) => {
                it.next();
                // Check if s is secretly a boolean first
                if s == "true" {
                    Ok(Atom::BoolLit(true))
                } else if s == "false" {
                    Ok(Atom::BoolLit(false))
                } else {
                    let symbol = ss.get_symbol(s);
                    Ok(Atom::Term(symbol))
                }
            },
            Token::StrLiteral(s) => {
                it.next();
                Ok(Atom::StringLit(s.to_string()))
            },
            Token::NumLiteral(n) => {
                it.next();
                Ok(Atom::IntLit(*n))
            },
            _ => {
                Err(Some((**token).clone()))
            }
        },
        None => Err(None)
    }
}

fn parse_term_weak<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> bool 
    where I: Iterator<Item=&'a Token>
{
    todo!()
}

fn skip_newlines<'a, I>(it: &mut Peekable<I>) -> Result<&'a Token, ()> 
    where I: Iterator<Item=&'a Token>, 
{
    // Skips all the newlines so that calling `it.next()` will give you a non-newline item.
    // Returns a reference to the next token as well, or Err(()) if the iterator is now empty.
    loop {
        let peek = it.peek();
        match peek {
            None => { return Err(()); }
            Some(tok) => match tok {
                Token::Newline => { it.next(); },
                t => { return Ok(t); }
            }
        }
    }
}