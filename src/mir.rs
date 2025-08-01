pub mod mir_def;
mod mir_gen;

use crate::{ast, semantic_analysis::type_check::SymbolTable};

pub fn generate_mir(ast: ast::Program, symbol_table: &mut SymbolTable) -> mir_def::Program {
    let generator = mir_gen::Generator::new(symbol_table);

    generator.generate(ast)
}