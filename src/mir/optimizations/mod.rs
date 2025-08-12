use crate::{mir::mir_def::Program, semantic_analysis::type_check::SymbolTable};

mod constant_folding;
mod unreachable_elimination;
mod combine_blocks;

pub fn optimize(mir: Program, symbol_table: &SymbolTable) -> Program {
    let mut mir = mir;

    loop {
        let program_copy = mir.clone();

        mir = constant_folding::fold_program(mir, symbol_table);

        mir = unreachable_elimination::elim_program(mir);

        mir.recalculate_predecessors();

        mir = combine_blocks::combine_program(mir);

        if mir == program_copy {
            break;
        }
    }

    mir
}