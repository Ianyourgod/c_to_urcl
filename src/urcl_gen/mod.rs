pub mod asm;
mod convert;
mod remove_pseudo;
pub mod cpu_definitions;

use crate::{mir::mir_def, semantic_analysis::type_check::SymbolTable};

pub fn mir_to_asm<'a, T: cpu_definitions::CPUDefinition>(mir: mir_def::Program, symbol_table: &'a SymbolTable, backend: &'a T) -> asm::Program<'a, asm::Val, T> {
    let generator = convert::ASMGenerator::new(symbol_table, backend);
    let inital = generator.mir_to_asm(mir);

    std::fs::write("pre_pval_removal.urcl", inital.to_string()).unwrap();

    let no_pvals = remove_pseudo::fix_pvals(inital, symbol_table, backend);

    asm::Program {
        cpu: backend,
        top_level_items: no_pvals.top_level_items
    }
}