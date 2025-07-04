mod expr;
mod lambda;
mod symbols;
mod tokens;
mod lex;
mod parse;
mod translate;
mod aux;
mod typing;
mod structures;
use crate::structures::*;

use std::fs::File;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    //let args: Vec<String> = env::args().collect();
    //let filename = &args[1];
    let filename = &"/Users/dwall/peytonjones/test.txt".to_string();

    let mut file = File::open(filename)?;
    let lexed = Lexed::from_file(&mut file)?;
    //println!("{}", lexed);
    let parsed = lexed.parse()?;
    let translated = parsed.translate()?;
    let type_checked = translated.type_check()?;
    println!("{}", type_checked);
    //println!("{:?}", type_checked);
    Ok(())
}