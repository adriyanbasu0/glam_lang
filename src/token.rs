#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum TokenKind {
    // Keywords
    Fn,     // fn
    Let,    // let
    Mut,    // mut
    If,     // if
    Else,   // else
    Return, // return
    True,   // true
    False,  // false
    Null,   // null
    Print,  // print (for a simple print function)
    Struct, // struct

    // Operators
    Assign,   // =
    Plus,     // +
    Minus,    // -
    Asterisk, // *
    Slash,    // /
    Bang,     // !
    Eq,       // ==
    NotEq,    // !=
    Lt,       // <
    Gt,       // >
    LtEq,     // <=
    GtEq,     // >=

    // Delimiters
    Comma,     // ,
    Semicolon, // ;
    Colon,     // :
    Dot,       // .
    LParen,    // (
    RParen,    // )
    LBrace,    // {
    RBrace,    // }

    // Literals
    Identifier,
    Int,
    String,

    // Special
    Eof,
    Illegal,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Token {
    pub kind: TokenKind,
    pub literal: String,
    pub start: usize,
    pub len: usize,
}

impl Token {
    pub fn new(kind: TokenKind, literal: String, start: usize, len: usize) -> Self {
        Token {
            kind,
            literal,
            start,
            len,
        }
    }
}
