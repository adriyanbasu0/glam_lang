use crate::token::{Token, TokenKind};

pub struct Lexer {
    input: String,
    position: usize,      // current position in input (points to current char)
    read_position: usize, // current reading position in input (after current char)
    ch: char,             // current char under examination
}

impl Lexer {
    pub fn new(input: String) -> Self {
        let mut lexer = Lexer {
            input,
            position: 0,
            read_position: 0,
            ch: '\0', // null character
        };
        lexer.read_char();
        lexer
    }

    fn read_char(&mut self) {
        if self.read_position >= self.input.len() {
            self.ch = '\0';
        } else {
            self.ch = self.input.chars().nth(self.read_position).unwrap();
        }
        self.position = self.read_position;
        self.read_position += 1;
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        self.skip_comments(); // Skip comments after skipping whitespace

        let current_token_start_pos = self.position;
        let (kind, literal) = match self.ch {
            '=' => {
                if self.peek_char() == '=' {
                    self.read_char(); // consume the second '='
                    (TokenKind::Eq, "==".to_string())
                } else {
                    (TokenKind::Assign, "=".to_string())
                }
            }
            '+' => (TokenKind::Plus, "+".to_string()),
            '-' => (TokenKind::Minus, "-".to_string()),
            '*' => (TokenKind::Asterisk, "*".to_string()),
            '/' => {
                if self.peek_char() == '/' {
                    // This case should be handled by skip_comments, but just in case
                    self.skip_comments();
                    return self.next_token(); // Get the next actual token
                }
                (TokenKind::Slash, "/".to_string())
            }
            '!' => {
                if self.peek_char() == '=' {
                    self.read_char(); // consume the '='
                    (TokenKind::NotEq, "!=".to_string())
                } else {
                    (TokenKind::Bang, "!".to_string())
                }
            }
            '<' => {
                if self.peek_char() == '=' {
                    self.read_char(); // consume the '='
                    (TokenKind::LtEq, "<=".to_string())
                } else {
                    (TokenKind::Lt, "<".to_string())
                }
            }
            '>' => {
                if self.peek_char() == '=' {
                    self.read_char(); // consume the '='
                    (TokenKind::GtEq, ">=".to_string())
                } else {
                    (TokenKind::Gt, ">".to_string())
                }
            }
            ',' => (TokenKind::Comma, ",".to_string()),
            ';' => (TokenKind::Semicolon, ";".to_string()),
            '(' => (TokenKind::LParen, "(".to_string()),
            ')' => (TokenKind::RParen, ")".to_string()),
            '{' => (TokenKind::LBrace, "{".to_string()),
            '}' => (TokenKind::RBrace, "}".to_string()),
            '"' => {
                self.read_char(); // consume the opening quote
                let (literal, kind) = self.read_string_literal();
                self.read_char(); // consume the closing quote or advance
                return Token::new(kind, literal, current_token_start_pos, self.position - current_token_start_pos);
            }
            '\0' => (TokenKind::Eof, "".to_string()),
            _ => {
                if is_letter(self.ch) {
                    let literal = self.read_identifier();
                    let kind = match literal.as_str() {
                        "fn" => TokenKind::Fn,
                        "let" => TokenKind::Let,
                        "mut" => TokenKind::Mut,
                        "if" => TokenKind::If,
                        "else" => TokenKind::Else,
                        "return" => TokenKind::Return,
                        "true" => TokenKind::True,
                        "false" => TokenKind::False,
                        "null" => TokenKind::Null,
                        "print" => TokenKind::Print,
                        _ => TokenKind::Identifier,
                    };
                    return Token::new(kind, literal, current_token_start_pos, self.position - current_token_start_pos);
                } else if is_digit(self.ch) {
                    let literal = self.read_number();
                    return Token::new(TokenKind::Int, literal, current_token_start_pos, self.position - current_token_start_pos);
                } else {
                    (TokenKind::Illegal, self.ch.to_string())
                }
            }
        };

        self.read_char();
        Token::new(kind, literal, current_token_start_pos, self.position - current_token_start_pos)
    }

    fn read_identifier(&mut self) -> String {
        let position = self.position;
        while is_letter(self.ch) || is_digit(self.ch) {
            self.read_char();
        }
        self.input[position..self.position].to_string()
    }

    fn read_number(&mut self) -> String {
        let position = self.position;
        while is_digit(self.ch) {
            self.read_char();
        }
        self.input[position..self.position].to_string()
    }

    fn read_string_literal(&mut self) -> (String, TokenKind) {
        let position = self.position;
        while self.ch != '"' && self.ch != '\0' {
            self.read_char();
        }

        if self.ch == '\0' {
            // Unterminated string
            (self.input[position..self.position].to_string(), TokenKind::Illegal)
        } else {
            (self.input[position..self.position].to_string(), TokenKind::String)
        }
    }

    fn skip_whitespace(&mut self) {
        while self.ch.is_ascii_whitespace() {
            self.read_char();
        }
    }

    fn skip_comments(&mut self) {
        while self.ch == '/' && self.peek_char() == '/' {
            while self.ch != '\n' && self.ch != '\0' {
                self.read_char();
            }
            self.read_char(); // consume the '\n'
            self.skip_whitespace(); // skip any whitespace after the newline
        }
    }

    fn peek_char(&mut self) -> char {
        if self.read_position >= self.input.len() {
            '\0'
        } else {
            self.input.chars().nth(self.read_position).unwrap()
        }
    }
}

fn is_letter(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_digit(ch: char) -> bool {
    ch.is_ascii_digit()
}