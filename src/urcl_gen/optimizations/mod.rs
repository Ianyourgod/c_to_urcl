use std::collections::{HashMap, HashSet};

use crate::{semantic_analysis::type_check::{SymbolTable, TypeTable}, urcl_gen::{asm, convert::ConvInfo, cpu_definitions::CPUDefinition}};

mod label_replace;
pub mod register_allocation;

pub fn optimize_post_pval<CPU: CPUDefinition>(program: asm::Program<asm::Val, CPU>) -> asm::Program<asm::Val, CPU> {
    asm::Program {
        cpu: program.cpu,
        top_level_items: program.top_level_items.into_iter().map(|tl| {
            match tl {
                asm::TopLevel::Fn(func) => asm::TopLevel::Fn(optimize_post_pval_fn(func)),
                _ => tl
            }
        }).collect()
    }
}

fn optimize_post_pval_fn(func: asm::Function<asm::Val>) -> asm::Function<asm::Val> {
    let mut func = func;

    loop {
        let prev_fn = func.clone();

        func = label_replace::run(func);

        if func == prev_fn {
            break func;
        }
    }
}

pub fn optimize_pre_pval<'a, CPU: CPUDefinition>(program: asm::Program<'a, asm::PVal, CPU>, statics_and_aliased: &HashMap<asm::Ident, HashSet<asm::Ident>>, conv_info: &ConvInfo, symbol_table: &SymbolTable, type_table: &TypeTable) -> (asm::Program<'a, asm::PVal, CPU>, HashMap<asm::Ident, HashSet<asm::Reg>>) {
    let mut callee_saved = HashMap::new();

    let prog = asm::Program {
        cpu: program.cpu,
        top_level_items: program.top_level_items.into_iter().map(|tl| {
            match tl {
                asm::TopLevel::Fn(func) => {
                    let s = statics_and_aliased.get(&func.name).unwrap();
                    let (func, c) = optimize_pre_pval_fn(func, program.cpu, s, conv_info, symbol_table, type_table);
                    callee_saved.insert(func.name.clone(), c);
                    asm::TopLevel::Fn(func)
                },
                _ => tl
            }
        }).collect()
    };

    (prog, callee_saved)
}

fn optimize_pre_pval_fn<CPU: CPUDefinition>(mut func: asm::Function<asm::PVal>, cpu: &CPU, statics_and_aliased: &HashSet<asm::Ident>, conv_info: &ConvInfo, symbol_table: &SymbolTable, type_table: &TypeTable) -> (asm::Function<asm::PVal>, HashSet<asm::Reg>) {
    // TODO! get aliased

    let (instrs, callee_saved) = register_allocation::allocate_registers(func.instructions, cpu, statics_and_aliased, conv_info, &func.name, symbol_table, type_table);

    func.instructions = instrs;

    (func, callee_saved)
}