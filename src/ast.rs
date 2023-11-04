use anyhow::Result;
use std::collections::LinkedList;
use tap::Pipe;

use crate::token::Token;

#[derive(Debug, PartialEq, Eq)]
pub enum Ast {
    Variable(char),
    And(Box<Ast>, Box<Ast>),
    Or(Box<Ast>, Box<Ast>),
    Not(Box<Ast>),
}

impl Ast {
    pub fn execute(&self, variable_values: u32) -> u32 {
        match self {
            Self::Variable(ch) => variable_values << (31 - (*ch as u8 - b'a')) as usize >> 31,
            Self::Or(a, b) => a.execute(variable_values) | b.execute(variable_values),
            Self::And(a, b) => a.execute(variable_values) & b.execute(variable_values),
            Self::Not(a) => a.execute(variable_values) ^ 1,
        }
    }
}

impl TryFrom<TokenOrAst> for Ast {
    type Error = anyhow::Error;
    fn try_from(value: TokenOrAst) -> std::result::Result<Self, Self::Error> {
        match value {
            TokenOrAst::Ast(ast) => Ok(ast),
            TokenOrAst::Token(Token::Variable(var)) => Ok(Ast::Variable(var)),
            TokenOrAst::Token(_) => anyhow::bail!("Token is not an AST!"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, derive_more::From)]
pub enum TokenOrAst {
    Token(Token),
    Ast(Ast),
}

impl TokenOrAst {
    pub fn from_tokens(tokens: LinkedList<Token>) -> Result<LinkedList<TokenOrAst>> {
        tokens
            .into_iter()
            .map(|token| match token {
                Token::Variable(x) => Ok(TokenOrAst::Ast(Ast::Variable(x))),
                _ => Ok(TokenOrAst::Token(token)),
            })
            .collect()
    }

    fn astize_nots(mut this: LinkedList<Self>) -> Result<LinkedList<Self>> {
        let mut cursor = this.cursor_front_mut();

        while cursor.index().is_some() {
            if matches!(cursor.current(), Some(TokenOrAst::Token(Token::NotSign)))
                && matches!(cursor.peek_next(), Some(TokenOrAst::Ast(_)))
            {
                cursor.remove_current();

                let TokenOrAst::Ast(variable) = cursor.remove_current().unwrap() else {
                    unreachable!("We've checked that's Ast");
                };

                cursor.insert_before(TokenOrAst::Ast(Ast::Not(Box::new(variable))));
            }
            cursor.move_next();
        }

        Ok(this)
    }

    fn astize_ands(mut this: LinkedList<Self>) -> Result<LinkedList<Self>> {
        let mut cursor = this.cursor_front_mut();

        while cursor.index().is_some() {
            if matches!(cursor.current(), Some(TokenOrAst::Token(Token::AndSign)))
                && matches!(cursor.peek_next(), Some(TokenOrAst::Ast(_)))
                && matches!(cursor.peek_prev(), Some(TokenOrAst::Ast(_)))
            {
                cursor.remove_current();

                let Some(TokenOrAst::Ast(rhs)) = cursor.remove_current() else {
                    unreachable!("We've checked that's Ast");
                };

                cursor.move_prev();

                let Some(TokenOrAst::Ast(lhs)) = cursor.remove_current() else {
                    unreachable!("cursorWe've checked that's Ast")
                };

                cursor.insert_before(TokenOrAst::Ast(Ast::And(Box::new(lhs), Box::new(rhs))));
                cursor.move_prev();
            }
            cursor.move_next();
        }

        Ok(this)
    }

    fn astize_ors(mut this: LinkedList<Self>) -> Result<LinkedList<Self>> {
        let mut cursor = this.cursor_front_mut();

        while cursor.index().is_some() {
            if matches!(cursor.current(), Some(TokenOrAst::Token(Token::OrSign)))
                && matches!(cursor.peek_next(), Some(TokenOrAst::Ast(_)))
                && matches!(cursor.peek_prev(), Some(TokenOrAst::Ast(_)))
            {
                cursor.remove_current();

                let Some(TokenOrAst::Ast(rhs)) = cursor.remove_current() else {
                    unreachable!("We've checked that's Ast");
                };

                cursor.move_prev();

                let Some(TokenOrAst::Ast(lhs)) = cursor.remove_current() else {
                    unreachable!("We've checked that's Ast")
                };

                cursor.insert_before(TokenOrAst::Ast(Ast::Or(Box::new(lhs), Box::new(rhs))));
                cursor.move_prev();
            }
            cursor.move_next();
        }

        Ok(this)
    }

    pub fn astize(this: LinkedList<Self>) -> Result<Ast> {
        let mut val = Self::fully_astize(this)?;

        assert!(
            val.len() == 1,
            "At this point, `this` should be fully AST-ized. No empty ASTs allowed!"
        );

        val.pop_front().unwrap().try_into()
    }

    fn fully_astize(this: LinkedList<Self>) -> Result<LinkedList<Self>> {
        this.pipe(Self::astize_brackets)?
            .pipe(Self::astize_nots)?
            .pipe(Self::astize_ands)?
            .pipe(Self::astize_ors)
    }

    fn astize_brackets(mut this: LinkedList<Self>) -> Result<LinkedList<Self>> {
        let mut depth = 0;
        let mut lbracket_indices = Vec::with_capacity(this.len() / 2);
        let mut rbracket_indices = Vec::with_capacity(this.len() / 2);
        let mut lbracket_idx = 0;
        let mut cursor = this.cursor_front_mut();

        while cursor.index().is_some() {
            if let Some(Self::Token(Token::LBracket)) = cursor.current() {
                if depth == 0 {
                    lbracket_indices.push(cursor.index().unwrap());
                    lbracket_idx = cursor.index().unwrap();
                }
                depth += 1;
            }

            if let Some(Self::Token(Token::RBracket)) = cursor.current() {
                depth -= 1;

                if depth == 0 {
                    rbracket_indices.push(cursor.index().unwrap());
                    let rbracket_idx = cursor.index().unwrap();
                    for _ in lbracket_idx..rbracket_idx {
                        cursor.move_prev()
                    }
                    let mut val = cursor.split_after();
                    cursor.remove_current();
                    let mut after_brackets = val.split_off(rbracket_idx - lbracket_idx);
                    val.pop_back();
                    let mut val = Self::fully_astize(val)?;
                    val.append(&mut after_brackets);
                    cursor.move_prev();
                    cursor.splice_after(val);
                    cursor.move_next();
                }
            }
            cursor.move_next();
        }

        Ok(this)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::LinkedList;

    use tap::Tap;

    use crate::{
        ast::{Ast, TokenOrAst},
        token::Token,
    };

    #[test]
    fn test_from_tokens() {
        let assumed_tokens = vec![
            TokenOrAst::Ast(Ast::Variable('x')),
            TokenOrAst::Token(Token::AndSign),
            TokenOrAst::Token(Token::LBracket),
            TokenOrAst::Ast(Ast::Variable('y')),
            TokenOrAst::Token(Token::OrSign),
            TokenOrAst::Ast(Ast::Variable('z')),
            TokenOrAst::Token(Token::RBracket),
            TokenOrAst::Token(Token::AndSign),
            TokenOrAst::Token(Token::NotSign),
            TokenOrAst::Ast(Ast::Variable('a')),
        ];

        let assumed_result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

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

        let result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        assert_eq!(assumed_result, TokenOrAst::from_tokens(result).unwrap())
    }

    #[test]
    fn test_astize_nots() {
        let assumed_tokens = vec![
            TokenOrAst::Ast(Ast::Variable('x')),
            TokenOrAst::Token(Token::AndSign),
            TokenOrAst::Token(Token::LBracket),
            TokenOrAst::Ast(Ast::Variable('y')),
            TokenOrAst::Token(Token::OrSign),
            TokenOrAst::Ast(Ast::Variable('z')),
            TokenOrAst::Token(Token::RBracket),
            TokenOrAst::Token(Token::AndSign),
            TokenOrAst::Ast(Ast::Not(Box::new(Ast::Variable('a')))),
        ];

        let assumed_result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        let assumed_tokens = vec![
            TokenOrAst::Ast(Ast::Variable('x')),
            TokenOrAst::Token(Token::AndSign),
            TokenOrAst::Token(Token::LBracket),
            TokenOrAst::Ast(Ast::Variable('y')),
            TokenOrAst::Token(Token::OrSign),
            TokenOrAst::Ast(Ast::Variable('z')),
            TokenOrAst::Token(Token::RBracket),
            TokenOrAst::Token(Token::AndSign),
            TokenOrAst::Token(Token::NotSign),
            TokenOrAst::Ast(Ast::Variable('a')),
        ];

        let result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        assert_eq!(assumed_result, TokenOrAst::astize_nots(result).unwrap())
    }

    #[test]
    fn test_astize_ands() {
        let assumed_tokens = vec![TokenOrAst::Ast(Ast::And(
            Box::new(Ast::Variable('x')),
            Box::new(Ast::Variable('y')),
        ))];

        let assumed_result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        let assumed_tokens = vec![
            TokenOrAst::Ast(Ast::Variable('x')),
            TokenOrAst::Token(Token::AndSign),
            TokenOrAst::Ast(Ast::Variable('y')),
        ];

        let result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        assert_eq!(assumed_result, TokenOrAst::astize_ands(result).unwrap())
    }

    #[test]
    fn test_astize_ors() {
        let assumed_tokens = vec![TokenOrAst::Ast(Ast::Or(
            Box::new(Ast::Variable('x')),
            Box::new(Ast::Variable('y')),
        ))];

        let assumed_result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        let assumed_tokens = vec![
            TokenOrAst::Ast(Ast::Variable('x')),
            TokenOrAst::Token(Token::OrSign),
            TokenOrAst::Ast(Ast::Variable('y')),
        ];

        let result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        assert_eq!(assumed_result, TokenOrAst::astize_ors(result).unwrap())
    }

    #[test]
    fn test_astize_brackets() {
        let assumed_tokens = vec![TokenOrAst::Ast(Ast::Or(
            Box::new(Ast::Variable('x')),
            Box::new(Ast::Variable('y')),
        ))];

        let assumed_result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        let assumed_tokens = vec![
            TokenOrAst::Token(Token::LBracket),
            TokenOrAst::Ast(Ast::Variable('x')),
            TokenOrAst::Token(Token::OrSign),
            TokenOrAst::Ast(Ast::Variable('y')),
            TokenOrAst::Token(Token::RBracket),
        ];

        let result = LinkedList::new().tap_mut(|tokens| {
            for token in assumed_tokens {
                tokens.push_back(token);
            }
        });

        assert_eq!(assumed_result, TokenOrAst::astize_brackets(result).unwrap())
    }

    #[test]
    fn test_execute() {
        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0001;

        assert_eq!(Ast::Variable('a').execute(a), 1);

        test_and();
        test_or();
        test_not();
    }

    fn test_and() {
        use Ast::{And, Variable as Var};
        use Box as B;

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0000;
        assert_eq!(And(B::new(Var('a')), B::new(Var('b'))).execute(a), 0);

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0001;
        assert_eq!(And(B::new(Var('a')), B::new(Var('b'))).execute(a), 0);

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0010;
        assert_eq!(And(B::new(Var('a')), B::new(Var('b'))).execute(a), 0);

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0011;
        assert_eq!(And(B::new(Var('a')), B::new(Var('b'))).execute(a), 1);
    }

    fn test_or() {
        use Ast::{Or, Variable as Var};
        use Box as B;

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0000;
        assert_eq!(Or(B::new(Var('a')), B::new(Var('b'))).execute(a), 0);

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0001;
        assert_eq!(Or(B::new(Var('a')), B::new(Var('b'))).execute(a), 1);

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0010;
        assert_eq!(Or(B::new(Var('a')), B::new(Var('b'))).execute(a), 1);

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0011;
        assert_eq!(Or(B::new(Var('a')), B::new(Var('b'))).execute(a), 1);
    }

    fn test_not() {
        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0000;
        assert_eq!(Ast::Not(Box::new(Ast::Variable('a'))).execute(a), 1);

        let a: u32 = 0b0000_0000_0000_0000_0000_0000_0000_0001;
        assert_eq!(Ast::Not(Box::new(Ast::Variable('a'))).execute(a), 0);
    }
}
