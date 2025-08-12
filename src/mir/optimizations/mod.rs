use crate::{mir::mir_def::Program, semantic_analysis::type_check::SymbolTable};

mod constant_folding;

pub fn optimize(mir: Program, symbol_table: &SymbolTable) -> Program {
    constant_folding::fold_program(mir, symbol_table)
}