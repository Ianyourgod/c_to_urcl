pub mod mir_def;
pub mod mir_gen;

use crate::{ast, semantic_analysis::type_check::{SymbolTable, TypeTable}};

pub fn generate_mir(ast: ast::Program<ast::TypedExpr>, symbol_table: &mut SymbolTable, type_table: &TypeTable) -> mir_def::Program {
    let generator = mir_gen::Generator::new(symbol_table, type_table);

    generator.generate(ast)
}