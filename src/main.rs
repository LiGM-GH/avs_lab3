#![feature(linked_list_cursors)]
use anyhow::Result;

use crate::{
    ast::{Ast, TokenOrAst},
    token::TokenSplit,
};

mod ast;
mod token;

fn main() -> Result<()> {
    let file = std::fs::read_to_string("input.txt")?.trim().to_owned();
    let file = file.replace("x", "a");
    let file = file.replace("y", "b");
    let file = file.replace("z", "c");
    let file = file.replace("w", "d");
    println!("x y z w | f");
    println!("-----------");

    // dbg!(&file);

    let tokens = file.split_tokens()?;

    // dbg!(&tokens);

    let ast: Ast = TokenOrAst::astize(TokenOrAst::from_tokens(tokens)?)?.try_into()?;

    for i1 in 0..=1 {
        for i2 in 0..=1 {
            for i3 in 0..=1 {
                for i4 in 0..=1 {
                    let arg = i1 | i2 << 1 | i3 << 2 | i4 << 3;

                    println!(
                        "{i1} {i2} {i3} {i4} | {result}",
                        i1 = i1 % 2,
                        i2 = i2 % 2,
                        i3 = i3 % 2,
                        i4 = i4 % 2,
                        result = ast.execute(arg),
                    );
                }
            }
        }
    }

    // println!("AST: {:#?}", ast);

    Ok(())
}
