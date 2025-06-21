use std::collections::HashMap;

use crate::lambda::*;
use crate::expr::*;
use crate::symbols::*;

pub fn translate(statements: Vec<Statement>) -> Vec<LambdaExpr> {
    let mut v: Vec<LambdaExpr> = Vec::new();
    for statement in statements.iter() {
    }
    v
}

pub fn reorder_statements(statements: &mut Vec<Statement>) {
    // Reorder the statements so that the same definitions are in the same order
    statements.sort_by(|a, b| a.cmp(b));
}

