use std::fmt::Write;
use std::fs::File;
use std::io::BufRead;
use std::io::Read;
use std::fmt;

use crate::lex;
use crate::tokens;
use crate::parse;
use crate::expr;
use crate::symbols;
use crate::translate;
use crate::lambda;
use crate::typing;

// "Structures" of context surrounding file at each stage of compilation

#[derive(Debug, Clone)]
pub struct Lexed {
    tokens: Vec<tokens::Token>
}

#[derive(Debug, Clone)]
pub struct Parsed {
    statements: Vec<expr::Statement>,
    symbol_stack: symbols::SymbolStack
}

#[derive(Debug, Clone)]
pub struct Translated {
    function_defs: Vec<(u32, lambda::LambdaExpr)>,
    symbol_stack: symbols::SymbolStack
}

#[derive(Debug, Clone)]
pub struct TypeChecked {
    function_defs: Vec<(u32, lambda::AnnotatedLambdaExpr<symbols::SymbolID, typing::ExprID>)>,
    symbol_stack: symbols::SymbolStack,
    type_table: typing::TypeTable
}

impl Lexed {
    pub fn from_file(file: &mut File) -> Result<Lexed, String> {
        let mut contents = String::new();
        file.read_to_string(&mut contents).expect("[Lexed::from_file] Failed to read file to string");
        let lexed_result = lex::lex(contents)?;
        Ok(Lexed { tokens: lexed_result })
    }

    pub fn parse(self) -> Result<Parsed, String> {
        let (statements, ss) = parse::parse(self.tokens)?;
        Ok(Parsed { statements: statements, symbol_stack: ss })
    }
}

impl Parsed {
    pub fn translate(self) -> Result<Translated, String> {
        let mut ss = self.symbol_stack;
        let function_defs = translate::translate(self.statements, &mut ss)?;
        Ok(Translated { function_defs: function_defs, symbol_stack: ss })
    }
}

impl Translated {
    pub fn type_check(self) -> Result<TypeChecked, String> {
        let mut type_table = typing::TypeTable::new();
        let mut typechecked_function_defs = Vec::new();
        for (symbol, lambda) in self.function_defs.into_iter() {
            let identified = typing::identify(lambda, &mut type_table);
            let t = typing::infer(&mut type_table, &identified)?;
            type_table.insert_symbol(symbol, t);
            // Handle recursive case
            typing::infer(&mut type_table, &identified)?;
            typechecked_function_defs.push((symbol, identified));
        }
        Ok(TypeChecked{
            function_defs: typechecked_function_defs,
            symbol_stack: self.symbol_stack,
            type_table: type_table
        })
    }
}

impl fmt::Display for TypeChecked {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = String::new();
        for (symbol, lambda) in self.function_defs.iter() {
            let t = lambda.get_type(&self.type_table);
            let validity = if typing::valid_type(&t) { "is valid" } else { "invalid" };
            buf.write_fmt(format_args!("s{} :: {} ({})\n", symbol, t, validity))?;
            buf.write_fmt(format_args!("s{} => {}\n\n", symbol, lambda))?;
        }
        write!(f, "{}", buf)
    }
}