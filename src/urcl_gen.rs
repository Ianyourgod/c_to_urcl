pub mod asm;
mod convert;
mod remove_pseudo;

use crate::{mir::mir_def, semantic_analysis::type_check::SymbolTable};

pub fn mir_to_asm(mir: mir_def::Program, symbol_table: &SymbolTable) -> asm::Program<asm::Val> {
    let inital = convert::mir_to_asm(mir);

    //std::fs::write("pre_pval_removal.urcl", inital.to_string()).unwrap();

    let no_pvals = remove_pseudo::fix_pvals(inital, symbol_table);

    no_pvals
}