use crate::{mir::mir_def::{self, Program}, semantic_analysis::type_check::SymbolTable};

mod pointer_analysis;
mod constant_folding;
mod unreachable_elimination;
mod combine_blocks;
mod copy_propagation;
mod dead_store;
mod inlining;

pub fn optimize(mir: Program, symbol_table: &SymbolTable, instr_count: &mut u64, tmp_count: &mut u64) -> Program {
    let mut program = mir.top_level;

    loop {
        let old_program = program.clone();

        program = program.into_iter().map(|tl|
            match tl {
                mir_def::TopLevel::Fn(func) => {
                    let mut cfg = func.basic_blocks;

                    loop {
                        let program_copy = cfg.clone();

                        cfg = constant_folding::fold_cfg(cfg, symbol_table);

                        cfg = unreachable_elimination::elim_cfg(cfg);

                        cfg.recalculate_predecessors();

                        cfg = combine_blocks::combine_cfg(cfg);

                        let aliased = pointer_analysis::find_aliased(&cfg, symbol_table).into_iter().cloned().collect();

                        cfg.recalculate_predecessors();

                        cfg = copy_propagation::propagate_cfg(cfg, symbol_table, &aliased);

                        // just in case...
                        cfg.recalculate_predecessors();
                        let aliased = pointer_analysis::find_aliased(&cfg, symbol_table).into_iter().cloned().collect();

                        cfg = dead_store::dead_store_fix_cfg(cfg, symbol_table, &aliased);

                        // inlining needs preds
                        cfg.recalculate_predecessors();

                        if cfg == program_copy {
                            break;
                        }
                    }

                    mir_def::TopLevel::Fn(mir_def::Function {
                        name: func.name,
                        global: func.global,
                        params: func.params,
                        basic_blocks: cfg
                    })
                },

                mir_def::TopLevel::Const { .. } |
                mir_def::TopLevel::Var(_) => tl,
            }
        ).collect();

        program = inlining::inline(program, instr_count, tmp_count);

        if program == old_program {
            break;
        }
    }
    

    mir_def::Program {
        top_level: program
    }
}