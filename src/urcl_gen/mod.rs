pub mod asm;
mod convert;
mod remove_pseudo;
mod optimizations;
mod fixup;
pub mod cpu_definitions;

use std::collections::{HashMap, HashSet};

use crate::{mir::mir_def, semantic_analysis::type_check::{SymbolTable, TypeTable}, urcl_gen::cpu_definitions::CPUDefinition, Ident};

pub fn mir_to_asm<'a, T: cpu_definitions::CPUDefinition>(mir: mir_def::Program, symbol_table: &'a mut SymbolTable, type_table: &'a TypeTable, backend: &'a T) -> asm::Program<'a, asm::Val, T> {
    let generator = convert::ASMGenerator::new(symbol_table, type_table, backend);
    let (initial, conv_info) = generator.mir_to_asm(mir);

    let initial = asm::Program {
        cpu: backend,
        top_level_items: initial.top_level_items
    };

    let aliased = get_aliased(&initial);
    let statics = get_all_statics(&symbol_table);

    // TODO! make this more efficient
    let stat_and_al = aliased.into_iter().map(|(k, mut v)| {
        v.extend(statics.clone());
        (k, v)
    }).collect();

    let (optimized_pre_pval_rem, callee_saved) = optimizations::optimize_pre_pval(initial, &stat_and_al, &conv_info, &symbol_table, type_table);

    std::fs::write("pre_pval_removal.urcl", optimized_pre_pval_rem.to_string()).unwrap();

    let (no_pvals, stack_offsets) = remove_pseudo::fix_pvals(optimized_pre_pval_rem, symbol_table, type_table, backend);

    let fixed = fixup::fix(no_pvals, callee_saved, stack_offsets, backend);

    let optimized = optimizations::optimize_post_pval(fixed);

    asm::Program {
        cpu: backend,
        top_level_items: optimized.top_level_items
    }
}

fn get_all_statics(symbol_table: &SymbolTable) -> HashSet<asm::Ident> {
    symbol_table.table.iter().filter_map(|(name, entry)| {
        if let crate::semantic_analysis::type_check::IdentifierAttrs::Static { .. } = entry.attrs {
            Some(name.clone())
        } else { None }
    }).collect()
}

fn get_aliased<CPU: CPUDefinition>(prog: &asm::Program<asm::PVal, CPU>) -> HashMap<Ident, HashSet<Ident>> {
    prog.top_level_items.iter().filter_map(|tl| {
        match tl {
            asm::TopLevel::Fn(func) => {
                Some((func.name.clone(), func.instructions.iter().filter_map(|instr| {
                    match instr {
                        asm::Instr::Lea { src, .. } => {
                            match src {
                                asm::PVal::Var(v) => Some(v.clone()),
                                _ => unreachable!()
                            }
                        },
                        _ => None,
                    }
                }).collect()))
            },
            _ => None
        }
    }).collect()
}