

#[derive(Debug)]
pub enum Token {
    // Literals
    NumLiteral(u32),
    StrLiteral(String),
    // Symbols
    Eq, // =
    Plus, // +
    Minus, // -
    Ast, // *
    Div, // /
    Colon, // :
    DColon, // ::
    Walrus, // :=
    Pipe, // |
    Comma, // ,
    LParen, // (
    RParen, // )
    LBracket, // [
    RBracket, // ]
    LArrow, // <-
    RArrow, // ->
    LBArrow, // <=
    RBArrow, // =>
    LT, // <
    GT, // >
    // Atoms - e.g. variables, builtins, etc
    Term(String),
    Newline
}