use crate::tokens::Token;

pub fn lex(s: String) -> Result<Vec<Token>, String> { // Lexer
    let mut prev_was_whitespace = true;
    let mut in_string = false;
    let mut in_num = false;
    let mut in_term = false;
    let mut buffer : Vec<char> = Vec::new();

    let mut tokens : Vec<Token> = Vec::new();

    for (i, c) in s.chars().enumerate() {
        let toklen = tokens.len();
        if in_string { 
            match c {
                '\'' => {
                    let s : String = buffer.iter().collect();
                    tokens.push(Token::StrLiteral(s));
                    buffer.clear();
                    in_string = false;
                },
                '\n' => {
                    return Result::Err(format!("[{}] Found newline in string literal", i));
                }
                c => {
                    buffer.push(c);
                }
            }
        } else if in_num {
            match c {
                c if c.is_whitespace() => {
                    let s : String = buffer.iter().collect();
                    let i : u32 = s.parse().unwrap();
                    tokens.push(Token::NumLiteral(i));
                    buffer.clear();
                    in_num = false;
                    prev_was_whitespace = true;
                    if c == '\n' { // also push a newline
                        tokens.push(Token::Newline);
                    }
                },
                c if c.is_ascii_digit() => {
                    buffer.push(c);
                },
                c if c.is_alphabetic() => { // parse it as a term, not a digit
                    in_num = false;
                    in_term = true;
                    buffer.push(c);
                },
                ')' | ']' | ':' | ',' => { // Close num, and push these 
                    let s : String = buffer.iter().collect();
                    let i : u32 = s.parse().unwrap();
                    tokens.push(Token::NumLiteral(i));
                    buffer.clear();
                    in_num = false;
                    match c {
                        ')' => { tokens.push(Token::RParen); },
                        ']' => { tokens.push(Token::RBracket); },
                        ':' => { tokens.push(Token::Colon); },
                        ',' => { tokens.push(Token::Comma); },
                        _ => { return Result::Err(format!("[{}] Reached unreachable code while lexing number!", i)) }
                    }
                },
                c => { // error
                    return Result::Err(format!("[{}] Expected digit or alphabetic character; found '{}'", i, c));
                }
            }
        } else if in_term {
            match c {
                c if c.is_whitespace() => {
                    let s : String = buffer.iter().collect();
                    tokens.push(Token::Term(s));
                    buffer.clear();
                    in_term = false;
                    prev_was_whitespace = true;
                    if c == '\n' { // Also push newline
                        tokens.push(Token::Newline);
                    }
                },
                c if c.is_alphanumeric() => {
                    buffer.push(c);
                },
                ')' | ']' | ':' | ',' => { // Close num, and push these 
                    let s : String = buffer.iter().collect();
                    tokens.push(Token::Term(s));
                    buffer.clear();
                    in_term = false;
                    match c {
                        ')' => { tokens.push(Token::RParen); },
                        ']' => { tokens.push(Token::RBracket); },
                        ':' => { tokens.push(Token::Colon); },
                        ',' => { tokens.push(Token::Comma); },
                        _ => { return Result::Err(format!("[{}] Reached unreachable code while lexing term!", i)) }
                    }
                },
                c => {
                    return Result::Err(format!("[{}] Expected digit or alphabetic character; found '{}'", i, c));
                }
            }
        } else {
            match c {
                '\n' => {
                    prev_was_whitespace = true;
                    if tokens.len() != 0 && tokens[tokens.len() - 1] != Token::Newline {
                        // 1) prevent leading newlines, and 2) prevent multiple newlines in a row
                        tokens.push(Token::Newline);
                    }
                },
                c if c.is_whitespace() => {
                    prev_was_whitespace = true;
                }, // just ignore
                '\'' => {
                    in_string = true;
                    prev_was_whitespace = false;
                },
                c if c.is_numeric() => {
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::LParen | Token::LBracket | Token::Comma => {
                                in_num = true;
                                buffer.push(c);
                            },
                            _ => {
                                return Result::Err(format!("[{}] Didn't expect alphanumeric character '{}' after symbol", i, c));
                            }
                        }
                    } else {
                        in_num = true;
                        buffer.push(c);
                        prev_was_whitespace = false;
                    }
                },
                c if c.is_alphanumeric() => {
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::LParen | Token::LBracket | Token::Colon | Token::Comma => {
                                in_term = true;
                                buffer.push(c);
                            },
                            _ => {
                                return Result::Err(format!("[{}] Didn't expect alphanumeric character '{}' after symbol", i, c));
                            }
                        }
                    } else {
                        in_term = true;
                        buffer.push(c);
                        prev_was_whitespace = false;
                    }
                },
                '=' => {
                    // Check previous token in case it is ':' (-> Walrus) or '<' (-> LBArrow)
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::Colon => { tokens[toklen - 1] = Token::Walrus; },
                            Token::LT => { tokens[toklen - 1] = Token::LBArrow; },
                            Token::LParen => { tokens.push(Token::Eq); },
                            _ => { return Result::Err(format!("[{}] Didn't expect '='", i)); }
                        }
                    } else {
                        tokens.push(Token::Eq);
                        prev_was_whitespace = false;
                    } 
                },
                '+' => {
                    if !prev_was_whitespace { 
                        match tokens[toklen - 1] {
                            Token::LParen => { tokens.push(Token::Plus); },
                            _ => { return Result::Err(format!("[{}] Didn't expect '+'", i)); }
                        }
                    } else {
                        tokens.push(Token::Plus);
                        prev_was_whitespace = true;
                    }
                },
                '-' => {
                    // Check previous token in case it is '<' (-> LArrow)
                    if prev_was_whitespace {
                        tokens.push(Token::Minus);
                        prev_was_whitespace = false;
                    } else {
                        match tokens[toklen - 1] {
                            Token::LT => { tokens[toklen - 1] = Token::LArrow; },
                            Token::LParen => { tokens.push(Token::Minus); },
                            _ => { return Result::Err(format!("[{}] Didn't expect '-'", i)) }
                        }
                    }
                },
                '*' => {
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::LParen => { tokens.push(Token::Ast); },
                            _ => { return Result::Err(format!("[{}] Didn't expect '*'", i)); }
                        }
                    } else {
                        tokens.push(Token::Ast);
                        prev_was_whitespace = false;
                    }
                },
                '/' => {
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::LParen => { tokens.push(Token::Div); },
                            _ => { return Result::Err(format!("[{}] Didn't expect '/'", i)); }
                        }
                    } else {
                        tokens.push(Token::Div);
                        prev_was_whitespace = false;
                    }
                },
                ':' => {
                    // Check previous token in case it is ':' (-> DColon)
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::Colon => { tokens[toklen - 1] = Token::DColon },
                            Token::StrLiteral(_) => { // colons after non-whitespace are allowed, e.g. [x:xs]
                                tokens.push(Token::Colon); 
                            },
                            _ => { return Result::Err(format!("[{}] Didn't expect ':'", i)); }
                        }
                    } else {
                        tokens.push(Token::Colon);
                        prev_was_whitespace = false;
                    }
                },
                '|' => {
                    if prev_was_whitespace {
                        tokens.push(Token::Pipe);
                        prev_was_whitespace = false;
                    } else {
                        return Result::Err(format!("[{}] Didn't expect '|'", i));
                    }
                },
                ',' => {
                    if prev_was_whitespace {
                        tokens.push(Token::Comma);
                        prev_was_whitespace = false;
                    } else {
                        match tokens[toklen - 1] {
                            Token::Eq | Token::Plus | Token::Minus | Token::Ast | Token::Div
                            | Token::LT | Token::GT | Token::RBracket | Token::RParen
                            | Token::StrLiteral(_) | Token::NumLiteral(_) | Token::Term(_) => {
                                tokens.push(Token::Comma);
                            },
                            _ => { return Result::Err(format!("[{}] Didn't expect ','", i)); }
                        }
                    }
                },
                '(' => {
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::LParen => { tokens.push(Token::LParen); },
                            _ => { return Result::Err(format!("[{}] Didn't expect '('", i))}
                        }
                    } else {
                        tokens.push(Token::LParen);
                        prev_was_whitespace = false;
                    }
                },
                ')' => {
                    match tokens[toklen - 1] {
                        Token::Eq | Token::Plus | Token::Minus | Token::Ast | Token::Div
                        | Token::LT | Token::GT | Token::RBracket | Token::RParen
                        | Token::StrLiteral(_) | Token::NumLiteral(_) | Token::Term(_)
                        | Token::Newline => {
                            tokens.push(Token::RParen);
                            prev_was_whitespace = false;
                        },
                        _ => {
                            return Result::Err(format!("[{}] Didn't expect ')'", i));
                        }
                    }
                },
                '[' => {
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::LBracket | Token::Colon | Token::LParen | Token::Comma => {
                                tokens.push(Token::LBracket);
                            },
                            _ => {
                                return Result::Err(format!("[{}] Didn't expect '['", i));
                            }
                        }
                    } else {
                        tokens.push(Token::LBracket);
                        prev_was_whitespace = false;
                    }
                },
                ']' => {
                    if toklen == 0 { // Invalid
                        return Result::Err(format!("[{}] Didn't expect ']'", i));
                    }
                    match tokens[toklen - 1] {
                        Token::Eq | Token::Plus | Token::Minus | Token::Ast | Token::Div
                        | Token::LT | Token::GT | Token::LBracket | Token::RBracket | Token::RParen
                        | Token::StrLiteral(_) | Token::NumLiteral(_) | Token::Term(_)
                        | Token::Newline => {
                            tokens.push(Token::RBracket);
                            prev_was_whitespace = false;
                        },
                        _ => {
                            return Result::Err(format!("[{}] Didn't expect ']'", i))
                        }
                    }
                },
                '<' => {
                    if !prev_was_whitespace {
                        return Result::Err(format!("[{}] Didn't expect '<'", i));
                    } else {
                        tokens.push(Token::LT);
                        prev_was_whitespace = false;
                    }
                },
                '>' => {
                    if !prev_was_whitespace {
                        match tokens[toklen - 1] {
                            Token::Minus => { tokens[toklen - 1] = Token::RArrow; },
                            Token::Eq => { tokens[toklen - 1] = Token::RBArrow },
                            _ => {
                                return Result::Err(format!("[{}] Didn't expect '>'", i));
                            }
                        }
                    } else {
                        tokens.push(Token::GT);
                        prev_was_whitespace = false;
                    }
                },
                c => {
                    return Result::Err(format!("[{}] Didn't expect '{}'", i, c));
                }
            }
        }
    }
    if in_string {
        return Result::Err(format!("[EOF] File ended with open quote!"));
    } else if in_num {
        let s : String = buffer.iter().collect();
        let i : u32 = s.parse().unwrap();
        tokens.push(Token::NumLiteral(i));
    } else if in_term {
        let s : String = buffer.iter().collect();
        tokens.push(Token::Term(s));
    }
    if tokens.len() > 0 && tokens[tokens.len() - 1] != Token::Newline {
        // Manually add in a trailing newline to make things easier
        tokens.push(Token::Newline);
    }
    Result::Ok(tokens)
}