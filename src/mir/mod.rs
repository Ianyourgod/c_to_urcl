pub mod mir_def;
pub mod mir_gen;

use crate::{ast, semantic_analysis::type_check::{SwitchCases, SymbolTable, TypeTable}};

pub fn generate_mir(ast: ast::Program<ast::TypedExpr>, symbol_table: &mut SymbolTable, type_table: &TypeTable, switch_cases: SwitchCases) -> mir_def::Program {
    let generator = mir_gen::Generator::new(symbol_table, type_table, switch_cases);

    generator.generate(ast)
}