use crate::{mir::mir_def::{self, Program}, semantic_analysis::type_check::SymbolTable};

mod pointer_analysis;
mod constant_folding;
mod unreachable_elimination;
mod combine_blocks;
mod copy_propagation;

pub fn optimize(mir: Program, symbol_table: &SymbolTable) -> Program {
    let program = mir.top_level.into_iter().map(|tl|
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

                    cfg = copy_propagation::propagate_cfg(cfg, symbol_table, &aliased);

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

    mir_def::Program {
        top_level: program
    }
}