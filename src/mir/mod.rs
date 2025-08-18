pub mod mir_def;
pub mod mir_gen;
mod pretty_print;
mod optimizations;

use std::io::Write;

use crate::{ast, semantic_analysis::type_check::{SwitchCases, SymbolTable, TypeTable}};

pub fn generate_mir(ast: ast::Program<ast::TypedExpr>, symbol_table: &mut SymbolTable, type_table: &TypeTable, switch_cases: SwitchCases) -> mir_def::Program {
    let generator = mir_gen::Generator::new(symbol_table, type_table, switch_cases);

    let (mir, mut instrs, mut tmps) = generator.generate(ast);
    
    write_to_file(&mir.to_string(), "unop.mir");

    let optimized_mir = optimizations::optimize(mir, symbol_table, &mut instrs, &mut tmps);

    optimized_mir
}

fn write_to_file(out: &str, file: &str) {
    let mut file = std::fs::File::create(file).unwrap();

    file.write_all(out.as_bytes()).unwrap();
}