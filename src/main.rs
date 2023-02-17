use chumsky::prelude::*;

mod lexer;
mod token;

use lexer::lexer;

fn main() {
    let input = "1 + 2 * 3";
    let tokens = lexer().parse(input).unwrap();
    println!("{:?}", tokens);
}
