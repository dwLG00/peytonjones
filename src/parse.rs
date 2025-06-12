use std::iter::Peekable;

use crate::expr::{Statement, Expr, Atom, Binop};
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
|               [ {NEWLINE} EXPR {NEWLINE} , ... , {NEWLINE} EXPR {NEWLINE} ]

ATOM :=         TERM
|               STR_LITERAL
|               NUM_LITERAL
|               BOOL_LITERAL

BINOP :=        + | - | * | / | < | >
*/

#[derive(PartialEq, Clone)]
enum ExprContext {
    // Stores context about the expression (e.g. am I in a 
    // parenthesis block? an if block?)
    InParen,
    InIf1, // if [here] then xyz else abc
    InIf2, // if xyz then [here] else abc
    InList,
    None
}

pub fn parse(tokens : Vec<Token>) -> Result<Vec<Statement>, String> {
    let mut statements : Vec<Statement> = Vec::new();
    let mut symbol_stack = SymbolStack::new();
    let mut it = tokens.iter().peekable();

    while it.peek().is_some() {
        let next_statement = parse_statement(&mut it, &mut symbol_stack);
        match next_statement {
            Ok(statement) => { statements.push(statement); },
            Err(e) => { return Err(e); }
        }
    }
    Ok(statements)
}

fn parse_statement<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Statement, String> 
    where I: Iterator<Item=&'a Token>
{
    // match Term
    let expect_symbol = parse_symbol(it, ss);
    match expect_symbol {
        Err(e) => Err(e),
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
                                return Err(format!("[parse_statement] Reached end of iterator"));
                            }
                        }
                    }
                }
            }
            // match eq
            match parse_eq_weak(it) {
                Ok(()) => {},
                Err(maybe_token) => match maybe_token {
                    Some(token) => { return Err(format!("[parse_statement] Expected `=` after statement beginning, found {:?}", token)); },
                    None => { return Err(format!("[parse_statement] Expected `=` after statement beginning, found EOF")); }
                }
            }
            let expect_expr = parse_expr_greedy(it, ss, ExprContext::None);
            ss.pop_stack();
            match expect_expr {
                Ok(expr) => Ok(Statement::FuncDef(symbol, atoms, expr)),
                Err(e) => Err(e)
            }
        }
    }
}

fn parse_expr<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack, context: ExprContext) -> Result<Expr, String>
    where I: Iterator<Item=&'a Token>
{
    // Try to match `let`, then try to match `if`, then try to match ``
    if parse_exact_term_weak(it, &"let".to_string()) { // let statement
        ss.push_stack();
        skip_newlines(it)?;
        let statement = parse_statement(it, ss)?;
        skip_newlines(it)?;
        parse_exact_term(it, &"in".to_string());
        skip_newlines(it)?;
        let expr = parse_expr_greedy(it, ss, context)?;
        ss.pop_stack();
        return Ok(Expr::LetIn(Box::new(statement), Box::new(expr)))

    } else if parse_exact_term_weak(it, &"if".to_string()) { // if statement
        skip_newlines(it)?;
        let split = parse_expr_greedy(it, ss, ExprContext::InIf1)?;
        skip_newlines(it)?;
        parse_exact_term(it, &"then".to_string());
        skip_newlines(it)?;
        let expr1 = parse_expr_greedy(it, ss, ExprContext::InIf2)?;
        skip_newlines(it)?;
        parse_exact_term(it, &"else".to_string());
        skip_newlines(it)?;
        let expr2 = parse_expr_greedy(it, ss, context)?;
        Ok(Expr::IfElse(Box::new(split), Box::new(expr1), Box::new(expr2)))

    } else if parse_exact_token_weak(it, Token::LParen) { // (expr)
        skip_newlines(it)?;
        let expr = parse_expr_greedy(it, ss, ExprContext::InParen)?;
        skip_newlines(it)?;
        parse_exact_token(it, Token::RParen);
        Ok(expr)

    } else if parse_exact_token_weak(it, Token::LBracket) {
        skip_newlines(it)?;
        let list = parse_list(it, ss)?;
        Ok(list)

    } else {
        // match atom, then try to match additional expressions
        let atom = parse_atom(it, ss)?;
        Ok(Expr::Atom(atom))
    }
}

fn parse_expr_greedy<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack, context: ExprContext) -> Result<Expr, String>
    where I: Iterator<Item=&'a Token>
{
    let expr = parse_expr(it, ss, context.clone())?;
    parse_expr_greedy_aux(it, ss, context, expr)
}

fn parse_expr_greedy_aux<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack, context: ExprContext, prev_expr: Expr) -> Result<Expr, String>
    where I: Iterator<Item=&'a Token>
{
    match it.peek() {
        None => Err(format!("[parse_expr_greedy_aux] Hit EOF")),
        Some(token) => match token {
            Token::Newline => {
                it.next();
                Ok(prev_expr)
            },
            // Match binary ops
            Token::Plus => {
                it.next();
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::Binop(Binop::Add, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            },
            Token::Minus => {
                it.next();
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::Binop(Binop::Sub, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            },
            Token::Ast => {
                it.next();
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::Binop(Binop::Mul, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            },
            Token::Div => {
                it.next();
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::Binop(Binop::Div, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            },
            Token::LT => {
                it.next();
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::Binop(Binop::Lt, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            },
            Token::GT => {
                it.next();
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::Binop(Binop::Gt, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            },
            Token::Eq => {
                it.next();
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::Binop(Binop::Gt, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            }
            // Try to apply
            _ => {
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::App(Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            }
        }
    }
}

fn parse_list<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Expr, String>
    where I: Iterator<Item=&'a Token>
{
    // match either ] or expr:expr] or expr{, expr}]

    match it.peek() {
        None => Err(format!("[parse_list] Hit EOF")),
        Some(token) => match token {
            Token::RBracket => {
                it.next();
                Ok(Expr::List(Vec::new()))
            },
            _ => { // Parse as an expression
                let expr1 = parse_expr_greedy(it, ss, ExprContext::InList)?;
                skip_newlines(it)?;
                match it.next() {
                    None => Err(format!("[parse_list] Hit EOF")), // EOF
                    Some(token) => match token {
                        Token::Colon => { // car:cdr]
                            skip_newlines(it)?;
                            let expr2 = parse_expr_greedy(it, ss, ExprContext::InList)?;
                            let expect_rbracket = skip_newlines(it)?;
                            match expect_rbracket {
                                Token::RBracket => {
                                    Ok(Expr::ListCon(Box::new(expr1), Box::new(expr2)))
                                },
                                t => Err(format!("[parse_list] Expected `]`, found `{:?}` instead", t))
                            }
                        },
                        Token::Comma => {
                            let mut v: Vec<Expr> = vec![expr1];
                            skip_newlines(it)?;
                            let next_expr = parse_expr_greedy(it, ss, ExprContext::InList)?;
                            v.push(next_expr);
                            let token = skip_newlines(it)?;
                            match token {
                                Token::RBracket => {
                                    it.next();
                                    Ok(Expr::List(v))
                                },
                                Token::Comma => {
                                    loop { // keep matching , {RETURN} expr {RETURN} until we get a newline
                                        match parse_exact_token(it, Token::Comma) {
                                            Ok(()) => {},
                                            Err(e) => match e {
                                                None => { return Err(format!("[parse_list] Expected ','; found EOF instead")); },
                                                Some(t) => { return Err(format!("[parse_list] Expected `,`; found `{:?}` instead", t)); }
                                            }
                                        }
                                        skip_newlines(it)?;
                                        v.push(parse_expr_greedy(it, ss, ExprContext::InList)?);
                                        let maybe_rb = skip_newlines(it)?;
                                        match maybe_rb {
                                            Token::RBracket => { break; },
                                            Token::Comma => {}, // do nothing; onto the next loop
                                            t => { return Err(format!("[parse_list] Expected `]` or `,`; found `{:?}` instead", t)); } // Unexpected...
                                        }
                                    }
                                    it.next(); // we break when the peek is RBracket
                                    Ok(Expr::List(v))
                                },
                                t => Err(format!("[parse_list] Expected `]` or `,`; found `{:?}` instead", t)) // Something weird not captured by the greedy expr parser...
                            }
                            
                        },
                        Token::RBracket => { // end list here
                            Ok(Expr::List(vec![expr1]))
                        },
                        t => Err(format!("[parse_list] Expected `]` or `,` or `:`; found {:?} instead", t))
                    }
                }
            }
        }
    }
}

fn parse_symbol<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Symbol, String> 
    where I: Iterator<Item=&'a Token>
{
    let expect_term = it.next();
    match expect_term {
        Some(eterm) => match eterm {
            Token::Term(t) => {
                let symbol = ss.get_symbol(t);
                Ok(symbol)
            },
            t => Err(format!("[parse_symbol] Expected symbol, found `{:?}` instead", t))
        },
        None => Err(format!("[parse_symbol] Expected symbol, found EOF"))
    }
}

fn parse_eq<'a>(it: &mut impl Iterator<Item=&'a Token>) -> bool {
    let expect_eq = it.next();
    match expect_eq {
        Some(eeq) => match eeq {
            Token::Eq => true,
            _ => false
        },
        None => false
    }
}

fn parse_eq_weak<'a, I>(it: &mut Peekable<I>) -> Result<(), Option<Token>>
    where I: Iterator<Item=&'a Token>
{
    match it.peek() {
        None => Err(None),
        Some(token) => match token {
            Token::Eq => Ok(()),
            t => Err(Some((**t).clone()))
        }
    }
}

fn parse_atom<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Atom, String>
    where I: Iterator<Item=&'a Token>
{
    // Match atom from it.peek(); advance if it succeeds, and don't if it doesn't
    match it.next() {
        Some(token) => match token {
            Token::Term(s) => if s == "true" {
                Ok(Atom::BoolLit(true))
            } else if s == "false" {
                Ok(Atom::BoolLit(false))
            } else {
                let symbol = ss.get_symbol(s);
                Ok(Atom::Term(symbol))
            },
            Token::StrLiteral(s) => Ok(Atom::StringLit(s.to_string())),
            Token::NumLiteral(n) => Ok(Atom::IntLit(*n)),
            t => Err(format!("[parse_atom] Expected atom, found `{:?}` instead", t))
        },
        None => Err(format!("[parse_atom] Expected atom, found EOF"))
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

fn parse_exact_term<'a, I>(it: &mut Peekable<I>, s: &String) -> bool
    where I: Iterator<Item=&'a Token>
{
    // Matches the exact term strongly, and returns whether match succeeded or not
    match it.next() {
        Some(tok) => match tok {
            Token::Term(s_) => s == s_,
            _ => false
        },
        None => false
    }
}

fn parse_exact_term_weak<'a, I>(it: &mut Peekable<I>, s: &String) -> bool 
    where I: Iterator<Item=&'a Token>
{
    // Matches the exact term weakly, and returns whether match succeeded or not
    match it.peek() {
        Some(tok) => match tok {
            Token::Term(s_) => {
                if s == s_ {
                    it.next();
                    true
                } else {
                    false
                }
            },
            _ => false
        },
        None => false
    }
}

fn parse_exact_token<'a, I>(it: &mut Peekable<I>, t: Token) -> Result<(), Option<Token>> 
    where I: Iterator<Item=&'a Token>
{
    match it.next() {
        Some(tok) => if (*tok).clone() == t {
            Ok(())
        } else {
            Err(Some((*tok).clone()))
        },
        None => Err(None)
    }
}

fn parse_exact_token_weak<'a, I>(it: &mut Peekable<I>, t: Token) -> bool 
    where I: Iterator<Item=&'a Token>
{
    match it.peek() {
        Some(tok) => if **tok == t {
            it.next();
            true
        } else {
            false
        },
        None => false
    }
}

fn skip_newlines<'a, I>(it: &mut Peekable<I>) -> Result<&'a Token, String> 
    where I: Iterator<Item=&'a Token>, 
{
    // Skips all the newlines so that calling `it.next()` will give you a non-newline item.
    // Returns a reference to the next token as well, or Err(()) if the iterator is now empty.
    loop {
        let peek = it.peek();
        match peek {
            None => { return Err(format!("[skip_newlines] Reached EOF")); }
            Some(tok) => match tok {
                Token::Newline => { it.next(); },
                t => { return Ok(t); }
            }
        }
    }
}