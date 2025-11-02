use std::fmt;
use std::cmp::Ordering;


pub type SymbolID = u32;
pub type SymbolTable = std::collections::HashMap<String, SymbolID>;
pub type SymbolSet = std::collections::HashSet<SymbolID>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(pub SymbolID, pub bool); // ident, scope

pub trait AlphaSubbable {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self;
    fn alpha_multisubst(&self, map: &Vec<(SymbolID, SymbolID)>) -> Self;
}

impl AlphaSubbable for SymbolID {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Self {
        if *self == old {
            new
        } else {
            *self
        }
    }
    fn alpha_multisubst(&self, map: &Vec<(SymbolID, SymbolID)>) -> Self {
        for (old, new) in map.iter() {
            if self == old {
                return *new;
            }
        }
        return *self;
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "s{}", self.0)
    }
}

impl Symbol {
    pub fn is_symbol(&self, s: SymbolID) -> bool {
        self.0 == s
    }
}

impl AlphaSubbable for Symbol {
    fn alpha_subst(&self, old: SymbolID, new: SymbolID) -> Symbol {
        if self.0 == old {
            Symbol(new, self.1)
        } else {
            self.clone()
        }
    }
    fn alpha_multisubst(&self, map: &Vec<(SymbolID, SymbolID)>) -> Self {
        for (old, new) in map.iter() {
            if self.0 == *old {
                return Symbol(*new, self.1)
            }
        }
        return self.clone();
    }
}

#[derive(Debug, Clone)]
pub struct SymbolStack {
    stack : Vec<SymbolTable>,
    next_u32 : u32
}

impl SymbolStack {
    pub fn new() -> SymbolStack {
        SymbolStack { stack:  vec![SymbolTable::new()], next_u32: 1 } // main := u32::MAX fyi. 
    }

    pub fn set_next_u32(&mut self, next: u32) {
        self.next_u32 = next
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
        // Grab corresponding symbol for term, registering it if not already exists
        for table in self.stack.iter().rev() {
            match table.get(s) {
                Some(i) => { return Symbol{0: *i, 1: true}; },
                None => {}
            }
        }
        self.register(s)
    }

    pub fn grab(&mut self) -> SymbolID {
        // Just grabs the next symbol ID available, for use outside of parsing
        let next = self.next_u32;
        self.next_u32 += 1;
        next
    }

    fn register(&mut self, s: &String) -> Symbol {
        // Register s in the newest symbol table entry
        let last_idx = self.stack.len() - 1;
        self.stack[last_idx].insert(s.clone(), self.next_u32);
        let symbol = Symbol{0: self.next_u32, 1: false};
        self.next_u32 += 1;
        symbol
    }

    pub fn push_stack(&mut self) {
        // Add a new table for sub-scope
        self.stack.push(SymbolTable::new());
    }

    pub fn pop_stack(&mut self) -> Option<SymbolTable> {
        // Remove the localest table
        if self.stack.len() == 1 { // Don't pop if there's only the global table...
            return None;
        }
        self.stack.pop()
    }

    pub fn to_sstack(&self) -> SStack {
        let mut stack = Vec::new();
        for table in self.stack.iter() {
            stack.push(table.values().copied().collect());
        }
        let next_u32 = self.next_u32;
        SStack { stack, next_u32 }
    }
}

#[derive(Debug, Clone)]
pub struct SStack {
    stack: Vec<SymbolSet>,
    next_u32 : u32
}

impl SStack {
    pub fn new() -> SStack {
        SStack { stack: vec![SymbolSet::new()], next_u32: 1 }
    }

    pub fn contains(&self, id: SymbolID) -> bool {
        for set in self.stack.iter() {
            if set.contains(&id) { return true }
        }
        return false
    }

    pub fn push_stack(&mut self) {
        self.stack.push(SymbolSet::new());
    }

    pub fn pop_stack(&mut self) -> Option<SymbolSet> {
        self.stack.pop()
    }

    pub fn add_symbol(&mut self, symbol: SymbolID) {
        let last_idx = self.stack.len() - 1;
        self.stack[last_idx].insert(symbol);
    }

    pub fn grab(&mut self) -> SymbolID {
        // Just grabs the next symbol ID available, for use outside of parsing
        let next = self.next_u32;
        self.next_u32 += 1;
        next
    }
}