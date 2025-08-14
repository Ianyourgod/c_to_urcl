// TODO! make this actually good

use std::collections::HashSet;

use crate::{mir::mir_def, semantic_analysis::type_check::{IdentifierAttrs, SymbolTable}, Ident};

pub type Aliased<'a> = HashSet<&'a Ident>;

pub fn find_aliased<'a>(cfg: &'a mir_def::CFG, symbol_table: &'a SymbolTable) -> Aliased<'a> {
    let mut aliased = HashSet::new();
    
    cfg.blocks.values().for_each(|block| {
        let aliased = &mut aliased;
        match block {
            mir_def::BasicBlock::Generic(block) => {
                block.instructions.iter().for_each(|instr| {
                    match &instr.instr {
                        mir_def::Instruction::GetAddress { src, .. } => {
                            aliased.insert(src);
                        },
                        _ => ()
                    }
                })
            },
            _ => ()
        }
    });

    for symbol in symbol_table.table.iter() {
        if matches!(symbol.1.attrs, IdentifierAttrs::Static { .. }) {
            aliased.insert(symbol.0);
        }
    }

    aliased
}