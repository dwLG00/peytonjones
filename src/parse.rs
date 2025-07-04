use std::iter::Peekable;

use crate::expr::{Statement, Expr, Atom, Arg, Binop};
use crate::symbols::{Symbol, SymbolStack};
use crate::tokens::{Token};

/*
Grammar:

STATEMENT :=    TERM {ARG} = EXPR NEWLINE

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

ARG :=          ATOM
|               [ ]
|               [ ARG : ARG ]
|               [ ARG {, ARG}* ]


BINOP :=        + | - | * | / | < | >
*/

#[derive(PartialEq, Clone, Debug)]
enum ExprContext {
    // Stores context about the expression (e.g. am I in a 
    // parenthesis block? an if block?)
    InParen,
    InIf1, // if [here] then xyz else abc
    InIf2, // if xyz then [here] else abc
    InList,
    InLet,
    None
}

const RESERVED_TERMS: [&'static str; 6] = [
    "if",
    "then",
    "else",
    "let",
    "in",
    "main"
];

pub fn parse(tokens : Vec<Token>) -> Result<(Vec<Statement>, SymbolStack), String> {
    let mut statements : Vec<Statement> = Vec::new();
    let mut symbol_stack = SymbolStack::new();
    let mut it = tokens.iter().enumerate().peekable();

    while it.peek().is_some() {
        let next_statement = parse_statement(&mut it, &mut symbol_stack, false);
        match next_statement {
            Ok(statement) => {
                statements.push(statement);
                skip_newlines_to_end(&mut it); // Skip newlines until we hit another token or EOF
            },
            Err(e) => { return Err(e); }
        }
    }
    Ok((statements, symbol_stack))
}

fn parse_statement<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack, in_let: bool) -> Result<Statement, String> 
    where I: Iterator<Item=(usize, &'a Token)>
{
    // Peek to clear the "main" case (no arguments)
    match it.peek() {
        None => { return Err(format!("[parse_statemet] @End, Hit EOF")); },
        Some((idx, token)) => match token {
            Token::Term(t) => if t == "main" {
                it.next();
                let idx = grab_index(it);
                match parse_eq_weak(it) {
                    Err(maybe_tok) => match maybe_tok {
                        None => { return Err(format!("[parse_statemet] @End, Hit EOF")); },
                        Some(tok) => { return Err(format!("[parse_statement] @{}, Expected `=`, found `{:?}`", idx, tok)); }
                    },
                    Ok(()) => {
                        let expect_expr = parse_expr_greedy(it, ss, ExprContext::None);
                        match expect_expr {
                            Ok(expr) => { return Ok(Statement::MainDef(expr)); },
                            Err(e) => { return Err(e); }
                        }
                    }
                }
            },
            token => { return Err(format!("[parse_statement] @{}, Expected term, found `{:?}`", idx, token))}
        }
    }
    let expect_symbol = parse_symbol(it, ss);
    ss.push_stack();
    match expect_symbol {
        Err(e) => Err(e),
        Ok(symbol) => {
            // match 0 or more Atoms
            let args = parse_args(it, ss)?;
            let idx = grab_index(it); // For debugging
            // match eq
            match parse_eq_weak(it) {
                Ok(()) => { skip_newlines(it)?; }, // skips for you
                Err(maybe_token) => match maybe_token {
                    Some(token) => { return Err(format!("[parse_statement] @{}, Expected `=` after statement beginning, found {:?}", idx, token)); },
                    None => { return Err(format!("[parse_statement] @End, Expected `=` after statement beginning, found EOF")); }
                }
            }
            let expect_expr = parse_expr_greedy(
                it,
                ss, 
                if in_let {
                    ExprContext::InLet
                } else {
                    ExprContext::None
                }
            );
            ss.pop_stack();
            match expect_expr {
                Ok(expr) => Ok(Statement::FuncDef(symbol, args, expr)),
                Err(e) => Err(e)
            }
        }
    }
}

fn parse_expr<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack, context: ExprContext) -> Result<Expr, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    // Try to match `let`, then try to match `if`, then try to match ``
    if parse_exact_term_weak(it, &"let".to_string()) { // let statement
        ss.push_stack();
        skip_newlines(it)?;
        let statement = parse_statement(it, ss, true)?;
        skip_newlines(it)?;
        parse_exact_term(it, &"in".to_string());
        skip_newlines(it)?;
        let expr = parse_expr_greedy(it, ss, context)?;
        ss.pop_stack();
        return Ok(Expr::LetIn(vec![statement], Box::new(expr)))

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
        let idx = grab_index(it);
        match parse_exact_token(it, Token::RParen) {
            Ok(_) => Ok(expr),
            Err(maybe_tok) => match maybe_tok {
                Some(tok) => Err(format!("[parse_expr] @{}, Expected `)`, found `{:?}`", idx, tok)),
                None => Err(format!("[parse_expr] @End, Hit EOF"))
            }
        }

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
    where I: Iterator<Item=(usize, &'a Token)>
{
    let expr = parse_expr(it, ss, context.clone())?;
    parse_expr_greedy_aux(it, ss, context, expr)
}

fn parse_expr_greedy_aux<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack, context: ExprContext, prev_expr: Expr) -> Result<Expr, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    match it.peek() {
        None => Err(format!("[parse_expr_greedy_aux] @End, Hit EOF")),
        Some((idx, token)) => match token {
            Token::Newline => {
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
                let expr = Expr::Binop(Binop::Eq, Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            },
            // Conditional terminals
            Token::Colon => {
                match context {
                    ExprContext::InList => Ok(prev_expr),
                    _ => Err(format!("[parse_expr_greedy_aux] @{}, unexpected `:` outside of list", idx))
                }
            },
            Token::Comma => {
                match context {
                    ExprContext::InList => Ok(prev_expr),
                    _ => Err(format!("[parse_expr_greedy_aux] @{}, unexpected `,` outside of list", idx))
                }
            },
            Token::RBracket => {
                match context {
                    ExprContext::InList => Ok(prev_expr),
                    _ => Err(format!("[parse_expr_greedy_aux] @{}, unexpected `]` (context: {:?})", idx, context)) //TODO Revert
                }
            },
            Token::RParen => {
                match context {
                    ExprContext::InParen => { return Ok(prev_expr); },
                    _ => { return Err(format!("[parse_expr_greedy_aux] @{}, unexpected `)`", idx)); }
                }
            }
            // Try to apply
            _ => {
                match token {
                    // Prevent reserved terms from being used
                    Token::Term(t) => if t == "then" {
                        match context {
                            ExprContext::InIf1 => { return Ok(prev_expr); },
                            _ => { return Err(format!("[parse_expr_greedy_aux] @{}, unexpected `then`", idx)); }
                        }
                    } else if t == "else" {
                        match context {
                            ExprContext::InIf2 => { return Ok(prev_expr); },
                            _ => { return Err(format!("[parse_expr_greedy_aux] @{}, unexpected `else`", idx)); }
                        }
                    } else if t == "let" {
                        // Let block
                        let mut statements = Vec::<Statement>::new();
                        loop {
                            let next = parse_statement(it, ss, true)?;
                            statements.push(next);
                            match it.next() {
                                None => { return Err(format!("[parse_expr_greedy_aux] @End, expected comma or `in`, found EOF")); },
                                Some((idx, t)) => match t {
                                    Token::Term(s) => if s == "in" {
                                        skip_newlines(it)?;
                                        break;
                                    } else {
                                        return Err(format!("[parse_expr_greedy_aux] @{}, expected comma or `in`, found {:?} instead", idx, t));
                                    },
                                    Token::Comma => {
                                        skip_newlines(it)?;
                                        // Let loop
                                    },
                                    t => { return Err(format!("[parse_expr_greedy_aux] @{}, expected comma or `in`, found {:?} instead", idx, t))}
                                }
                            }
                        }
                        let next_expr = parse_expr_greedy(it, ss, context.clone())?;
                        let expr = Expr::LetIn(statements, Box::new(next_expr));
                        return parse_expr_greedy_aux(it, ss, context, expr);
                    } else if t == "in" {
                        match context {
                            ExprContext::InLet => { return Ok(prev_expr); },
                            _ => { return Err(format!("[parse_expr_greedy_aux] @{}, unexpected `in`", idx)); }
                        }
                    },
                    _ => {}
                }
                let next_expr = parse_expr(it, ss, context.clone())?;
                let expr = Expr::App(Box::new(prev_expr), Box::new(next_expr));
                parse_expr_greedy_aux(it, ss, context, expr)
            }
        }
    }
}

fn parse_list<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Expr, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    // match either ] or expr:expr] or expr{, expr}]
    match it.peek() {
        None => Err(format!("[parse_list] @End, Hit EOF")),
        Some((_, token)) => match token {
            Token::RBracket => {
                it.next();
                Ok(Expr::List(Vec::new()))
            },
            _ => { // Parse as an expression
                let expr1 = parse_expr_greedy(it, ss, ExprContext::InList)?;
                skip_newlines(it)?;
                match it.next() {
                    None => Err(format!("[parse_list] @End, Hit EOF")), // EOF
                    Some((idx, token)) => match token {
                        Token::Colon => { // car:cdr]
                            skip_newlines(it)?;
                            let expr2 = parse_expr_greedy(it, ss, ExprContext::InList)?;
                            let expect_rbracket = skip_newlines(it)?;
                            match expect_rbracket {
                                Token::RBracket => {
                                    it.next();
                                    Ok(Expr::ListCon(Box::new(expr1), Box::new(expr2)))
                                },
                                t => Err(format!("[parse_list] @{}, Expected `]`, found `{:?}` instead", idx, t))
                            }
                        },
                        Token::Comma => {
                            let mut v: Vec<Expr> = vec![expr1];
                            skip_newlines(it)?;
                            let next_expr = parse_expr_greedy(it, ss, ExprContext::InList)?;
                            v.push(next_expr);
                            let token = skip_newlines(it)?;
                            let idx2 = grab_index(it);
                            match token {
                                Token::RBracket => {
                                    it.next();
                                    Ok(Expr::List(v))
                                },
                                Token::Comma => {
                                    loop { // keep matching , {RETURN} expr {RETURN} until we get a newline
                                        let idx3 = grab_index(it);
                                        match parse_exact_token(it, Token::Comma) {
                                            Ok(()) => {},
                                            Err(e) => match e {
                                                None => { return Err(format!("[parse_list] @End, Expected ','; found EOF instead")); },
                                                Some(t) => { return Err(format!("[parse_list] @{}, Expected `,`; found `{:?}` instead", idx3, t)); }
                                            }
                                        }
                                        skip_newlines(it)?;
                                        v.push(parse_expr_greedy(it, ss, ExprContext::InList)?);
                                        let maybe_rb = skip_newlines(it)?;
                                        let idx3 = grab_index(it);
                                        match maybe_rb {
                                            Token::RBracket => { break; },
                                            Token::Comma => {}, // do nothing; onto the next loop
                                            t => { return Err(format!("[parse_list] @{}, Expected `]` or `,`; found `{:?}` instead", idx3, t)); } // Unexpected...
                                        }
                                    }
                                    it.next(); // we break when the peek is RBracket
                                    Ok(Expr::List(v))
                                },
                                t => Err(format!("[parse_list] @{}, Expected `]` or `,`; found `{:?}` instead", idx2, t)) // Something weird not captured by the greedy expr parser...
                            }
                            
                        },
                        Token::RBracket => { // end list here
                            Ok(Expr::List(vec![expr1]))
                        },
                        t => Err(format!("[parse_list] @{}, Expected `]` or `,` or `:`; found {:?} instead", idx, t))
                    }
                }
            }
        }
    }
}

fn parse_symbol<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Symbol, String> 
    where I: Iterator<Item=(usize, &'a Token)>
{
    let expect_term = it.next();
    match expect_term {
        Some((idx, eterm)) => match eterm {
            Token::Term(t) => {
                let symbol = ss.get_symbol(t);
                Ok(symbol)
            },
            t => Err(format!("[parse_symbol] @{}, Expected symbol, found `{:?}` instead", idx, t))
        },
        None => Err(format!("[parse_symbol] @End, Expected symbol, found EOF"))
    }
}

fn parse_eq<'a>(it: &mut impl Iterator<Item=(usize, &'a Token)>) -> bool {
    let expect_eq = it.next();
    match expect_eq {
        Some((_, eeq)) => match eeq {
            Token::Eq => true,
            _ => false
        },
        None => false
    }
}

fn parse_eq_weak<'a, I>(it: &mut Peekable<I>) -> Result<(), Option<Token>>
    where I: Iterator<Item=(usize, &'a Token)>
{
    match it.peek() {
        None => Err(None),
        Some((_, token)) => match token {
            Token::Eq => {
                it.next();
                Ok(())
            },
            t => Err(Some((**t).clone()))
        }
    }
}

fn parse_arg_weakish<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Result<Arg, Option<Token>>, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    match parse_atom_weak(it, ss) {
        Ok(a) => Ok(Ok(Arg::Atom(a))),
        Err(maybe_token) => {
            match maybe_token {
                Some(token) => {
                    match token {
                        Token::LBracket => {
                            it.next();
                            match parse_arg_list(it, ss) {
                                Ok(arg) => Ok(Ok(arg)),
                                Err(s) => { return Err(s); }
                            }
                        },
                        _ => { return Ok(Err(Some(token))); }
                    }
                },
                None => { return Ok(Err(None)); }
            }
        }
    }
}

fn parse_arg<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Arg, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    let idx = grab_index(it);
    match parse_arg_weakish(it, ss) {
        Ok(maybe_success) => match maybe_success {
            Ok(arg) => Ok(arg),
            Err(err) => match err {
                Some(t) => Err(format!("[parse_arg] @{}, Expected argument, found `{:?}` instead", idx, t)),
                None => Err(format!("[parse_arg] @End, Hit EOF"))
            }
        },
        Err(s) => Err(s)
    }
}

fn parse_args<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Vec<Arg>, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    let mut args: Vec<Arg> = Vec::new();
    // Try to parse atom (weak)
    loop {
        match parse_arg_weakish(it, ss) {
            Ok(no_list_fail) => match no_list_fail {
                Ok(arg) => { args.push(arg); },
                Err(maybe_token) => match maybe_token {
                    Some(t) => {
                        if let Token::Newline = t { // Skip newlines between arguments and eq
                            skip_newlines(it)?;
                        }
                        return Ok(args);
                    },
                    None => { return Err(format!("[parse_args] @End, Hit EOF")); }
                }
            },
            Err(s) => { return Err(s); }
        }
    }
}

fn parse_arg_list<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Arg, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    match it.peek() {
        None => Err(format!("[parse_arg_list] @End, Hit EOF")),
        Some((_, token)) => match token {
            Token::RBracket => { // Empty list
                it.next(); // Skip next
                Ok(Arg::EmptyList)
            },
            _ => { // Parse as an arg
                let arg1 = parse_arg(it, ss)?;
                skip_newlines(it)?;
                match it.next() {
                    None => Err(format!("[parse_arg_list] @End, Hit EOF")),
                    Some((idx, token)) => match token {
                        Token::Colon => { // car : cdr ]
                            skip_newlines(it)?;
                            let arg2 = parse_arg(it, ss)?;
                            let expect_rbracket = skip_newlines(it)?;
                            let idx = grab_index(it);
                            match expect_rbracket {
                                Token::RBracket => {
                                    it.next();
                                    Ok(Arg::ListCon(Box::new(arg1), Box::new(arg2)))
                                },
                                t => Err(format!("[parse_arg_list] @{}, Expected `]`, found `{:?}` instead", idx, t))
                            }
                        },
                        Token::Comma => {
                            let mut v: Vec<Arg> = vec![arg1];
                            skip_newlines(it)?;
                            let next_arg = parse_arg(it, ss)?;
                            v.push(next_arg);
                            let token = skip_newlines(it)?;
                            let idx2 = grab_index(it);
                            match token {
                                Token::RBracket => {
                                    it.next();
                                    let list = v.iter().rev().fold(Arg::EmptyList, |acc, new| Arg::ListCon(Box::new(new.clone()), Box::new(acc)));
                                    Ok(list)
                                },
                                Token::Comma => {
                                    loop {
                                        let idx3 = grab_index(it);
                                        match parse_exact_token(it, Token::Comma) {
                                            Ok(()) => {},
                                            Err(e) => match e {
                                                None => { return Err(format!("[parse_arg_list] @End, Expected ','; found EOF instead")); },
                                                Some(t) => { return Err(format!("[parse_arg_list] @{}, Expected `,`; found `{:?}` instead", idx3, t)); }
                                            }
                                        }
                                        skip_newlines(it)?;
                                        v.push(parse_arg(it, ss)?);
                                        let maybe_rb = skip_newlines(it)?;
                                        let idx3 = grab_index(it);
                                        match maybe_rb {
                                            Token::RBracket => { break; },
                                            Token::Comma => {}, // do nothing; onto the next loop
                                            t => { return Err(format!("[parse_arg_list] @{}, Expected `]` or `,`; found `{:?}` instead", idx3, t)); } // Unexpected...
                                        }
                                    }
                                    it.next();
                                    let list = v.iter().rev().fold(Arg::EmptyList, |acc, new| Arg::ListCon(Box::new(new.clone()), Box::new(acc)));
                                    Ok(list)
                                },
                                t => Err(format!("[parse_arg_list] @{}, Expected `]` or `,`; found `{:?}` instead", idx2, t))
                            }
                        },
                        Token::RBracket => {
                            Ok(Arg::ListCon(Box::new(arg1), Box::new(Arg::EmptyList)))
                        },
                        t => Err(format!("[parse_arg_list] @{}, Expected `]` or `,` or `:`; found {:?} instead", idx, t))
                    }
                }
            }
        }
    }
}

fn parse_atom<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Atom, String>
    where I: Iterator<Item=(usize, &'a Token)>
{
    // Match atom from it.peek(); advance if it succeeds, and don't if it doesn't
    match it.next() {
        Some((idx, token)) => match token {
            Token::Term(s) => 
                if s == "true" {
                    Ok(Atom::BoolLit(true))
                } else if s == "false" {
                    Ok(Atom::BoolLit(false))
                } else if reserved(s) {
                    Err(format!("[parse_atom] @{}, Found reserved term `{}`", idx, s))
                } else {
                    let symbol = ss.get_symbol(s);
                    Ok(Atom::Term(symbol))
                },
            Token::StrLiteral(s) => Ok(Atom::StringLit(s.to_string())),
            Token::NumLiteral(n) => Ok(Atom::IntLit(*n)),
            t => Err(format!("[parse_atom] @{}, Expected atom, found `{:?}` instead", idx, t))
        },
        None => Err(format!("[parse_atom] @End, Expected atom, found EOF"))
    }
}

fn parse_atom_weak<'a, I>(it: &mut Peekable<I>, ss: &mut SymbolStack) -> Result<Atom, Option<Token>>
    where I: Iterator<Item=(usize, &'a Token)>
{
    // Match atom from it.peek(); advance if it succeeds, and don't if it doesn't
    let peek = it.peek();
    match peek {
        Some((_, token)) => match token {
            Token::Term(s) => {
                let tok = (**token).clone();
                it.next();
                // Check if s is secretly a boolean first
                if s == "true" {
                    Ok(Atom::BoolLit(true))
                } else if s == "false" {
                    Ok(Atom::BoolLit(false))
                } else if reserved(s) {
                    Err(Some(tok))
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
    where I: Iterator<Item=(usize, &'a Token)>
{
    // Matches the exact term strongly, and returns whether match succeeded or not
    match it.next() {
        Some((_, tok)) => match tok {
            Token::Term(s_) => s == s_,
            _ => false
        },
        None => false
    }
}

fn parse_exact_term_weak<'a, I>(it: &mut Peekable<I>, s: &String) -> bool 
    where I: Iterator<Item=(usize, &'a Token)>
{
    // Matches the exact term weakly, and returns whether match succeeded or not
    match it.peek() {
        Some((_, tok)) => match tok {
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
    where I: Iterator<Item=(usize, &'a Token)>
{
    match it.next() {
        Some((_, tok)) => if (*tok).clone() == t {
            Ok(())
        } else {
            Err(Some((*tok).clone()))
        },
        None => Err(None)
    }
}

fn parse_exact_token_weak<'a, I>(it: &mut Peekable<I>, t: Token) -> bool 
    where I: Iterator<Item=(usize, &'a Token)>
{
    match it.peek() {
        Some((_, tok)) => if **tok == t {
            it.next();
            true
        } else {
            false
        },
        None => false
    }
}

fn skip_newlines<'a, I>(it: &mut Peekable<I>) -> Result<&'a Token, String> 
    where I: Iterator<Item=(usize, &'a Token)>, 
{
    // Skips all the newlines so that calling `it.next()` will give you a non-newline item.
    // Returns a reference to the next token as well, or Err(()) if the iterator is now empty.

    // Run this once, error if there are _no_ newlines and we reach EOF
    loop {
        let peek = it.peek();
        match peek {
            None => { return Err(format!("[skip_newlines] @End, Reached EOF")); }
            Some((_, tok)) => match tok {
                Token::Newline => { it.next(); },
                t => { return Ok(t); }
            }
        }
    }
}

fn skip_newlines_to_end<'a, I>(it: &mut Peekable<I>)
    where I: Iterator<Item=(usize, &'a Token)>, 
{
    // Same as skip_newlines, except EOFs after a newline are OK
    loop {
        let peek = it.peek();
        match peek {
            None => { break;}
            Some((_, tok)) => match tok {
                Token::Newline => { it.next(); },
                _ => { break; }
            }
        }
    }
}

fn grab_index<'a, I>(it: &mut Peekable<I>) -> usize
    where I: Iterator<Item=(usize, &'a Token)>
{
    match it.peek() {
        None => 0, // This case should be handled by EOF anyways
        Some((idx, _)) => *idx
    }
}

fn reserved(s: &String) -> bool {
    for i in 0..5 {
        if RESERVED_TERMS[i] == s {
            return true;
        }
    }
    false
}