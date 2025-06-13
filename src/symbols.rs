
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Symbol(pub u32); // ident, scope

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "s{}", self.0)
    }
}

pub type SymbolTable = std::collections::HashMap<String, Symbol>;

pub struct SymbolStack {
    stack : Vec<SymbolTable>,
    next_u32 : u32
}

impl SymbolStack {
    pub fn new() -> SymbolStack {
        SymbolStack { stack:  vec![SymbolTable::new()], next_u32: 0 }
    }

    pub fn contains(&self, s: &String) -> bool {
        // Check if `s` has already been registered in this scope
        for table in self.stack.iter() {
            if table.contains_key(s) {
                return true;
            }
        }
        false
    }

    pub fn get_symbol(&mut self, s: &String) -> Symbol {
        for table in self.stack.iter().rev() {
            match table.get(s) {
                Some(symbol) => { return symbol.clone(); },
                None => {}
            }
        }
        self.register(s)
    }

    fn register(&mut self, s: &String) -> Symbol {
        // Register s in the newest symbol table entry
        let symbol = Symbol{0: self.next_u32 };
        let last_idx = self.stack.len() - 1;
        self.stack[last_idx].insert(s.clone(), symbol.clone());
        self.next_u32 += 1;
        symbol
    }

    pub fn push_stack(&mut self) {
        self.stack.push(SymbolTable::new());
    }

    pub fn pop_stack(&mut self) -> Option<SymbolTable> {
        if self.stack.len() == 1 { // Don't pop if there's only the global table...
            return None;
        }
        self.stack.pop()
    }
}