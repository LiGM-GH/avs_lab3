use std::collections::LinkedList;

use anyhow::Result;

/// # Understands the following tokens:
/// `[a-z]`, `∧`, `∨`, `¬`, `(`, `)`
#[derive(Debug, PartialEq, Eq)]
pub enum Token {
    LBracket,
    RBracket,
    Variable(char),
    AndSign,
    OrSign,
    NotSign,
}

impl Token {
    fn from_char(c: char) -> Result<Token> {
        match c {
            'a'..='z' => Ok(Token::Variable(c)),
            '∧' => Ok(Token::AndSign),
            '∨' => Ok(Token::OrSign),
            '¬' => Ok(Token::NotSign),
            '(' => Ok(Token::LBracket),
            ')' => Ok(Token::RBracket),
            _ => Err(anyhow::anyhow!("Invalid character")),
        }
    }
}

pub trait TokenSplit {
    type Error;

    fn split_tokens(self) -> Result<LinkedList<Token>>;
}

impl TokenSplit for &str {
    type Error = anyhow::Error;

    fn split_tokens(self) -> Result<LinkedList<Token>> {
        self.chars().map(Token::from_char).collect()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::LinkedList;

    use tap::Tap;

    use crate::token::{Token, TokenSplit};

    #[test]
    fn test_split_tokens() {
        let assumed_tokens = vec![
            Token::Variable('x'),
            Token::AndSign,
            Token::LBracket,
            Token::Variable('y'),
            Token::OrSign,
            Token::Variable('z'),
            Token::RBracket,
            Token::AndSign,
            Token::NotSign,
            Token::Variable('a'),
        ];

        let assumed_result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        assert_eq!("x∧(y∨z)∧¬a".split_tokens().unwrap(), assumed_result)
    }
}
