#![feature(box_patterns)]

mod ast;
mod semantic_analysis;
mod mir;
mod urcl_gen;

use std::{io::Write, rc::Rc};

use lalrpop_util::*;

pub type Ident = Rc<String>;

lalrpop_mod!(pub grammar);

fn main() {
    let input_file = std::env::args().nth(1).unwrap();

    let input = std::fs::read_to_string(input_file).unwrap();

    let ast = grammar::ProgramParser::new().parse(&input);
    let ast = match ast {
        Ok(ast) => ast,
        Err(e) => {
            println!("{e}");
            panic!();
        }
    };

    let (ast, mut symbol_table) = semantic_analysis::analyse(ast);

    let mir = mir::generate_mir(ast, &mut symbol_table);

    println!("{:#?}", mir);

    let asm = urcl_gen::mir_to_asm(mir, &symbol_table);

    write_to_file(&asm.to_string(), "output.urcl");
}

fn write_to_file(out: &str, file: &str) {
    let mut file = std::fs::File::create(file).unwrap();

    file.write_all(out.as_bytes()).unwrap();
}