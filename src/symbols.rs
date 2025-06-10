

pub struct Symbol(u32, u32); // ident, scope

pub type SymbolTable = std::collections::HashMap<String, Symbol>;