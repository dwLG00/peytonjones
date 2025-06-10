

pub enum Token {
    // Literals
    NumLiteral(i32),
    StrLiteral(String),
    // Symbols
    Eq,
    Plus,
    Minus,
    Ast, // asterisk
    Div,
    Colon,
    DColon, // ::
    Walrus, // :=
    Pipe, // |
    Comma,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LArrow, // <-
    RArrow, // ->
    // Atoms - e.g. variables, builtins, etc
    Term(String),
}
