//use std::collections::{HashMap, HashSet};
use std::collections::HashSet;

use crate::urcl_gen::asm;

pub fn run(func: asm::Function<asm::Val>) -> asm::Function<asm::Val> {
    let lr = LabelReplacer::new();
    lr.run(func)
}

struct LabelReplacer {
    referenced_labels: HashSet<asm::GenericBlockID>,
    //replace_with: HashMap<asm::GenericBlockID, asm::GenericBlockID>
}

impl LabelReplacer {
    pub fn new() -> Self {
        Self {
            referenced_labels: HashSet::new(),
            //replace_with: HashMap::new(),
        }
    }

    pub fn run(mut self, func: asm::Function<asm::Val>) -> asm::Function<asm::Val> {
        self.collect_referenced(&func);
        let mut func = self.remove_unrefed(func);
        func.instructions = self.remove_jmp_label(func.instructions);
        func
    }

    fn collect_referenced(&mut self, func: &asm::Function<asm::Val>) {
        for instr in &func.instructions {
            match instr {
                asm::Instr::Jmp { label } |
                asm::Instr::Branch { label, .. } => {
                    self.referenced_labels.insert(*label);
                },

                _ => ()
            }
        }
    }

    fn remove_unrefed(&self, func: asm::Function<asm::Val>) -> asm::Function<asm::Val> {
        asm::Function {
            name: func.name,
            instructions: func.instructions.into_iter().filter_map(|instr| {
                if let asm::Instr::Label(l) = instr {
                    if !self.referenced_labels.contains(&l) {
                        None
                    } else {
                        Some(instr)
                    }
                } else {
                    Some(instr)
                }
            }).collect()
        }
    }

    fn remove_jmp_label(&self, instructions: Vec<asm::Instr<asm::Val>>) -> Vec<asm::Instr<asm::Val>> {
        let mut new_instrs = Vec::new();

        let mut instructions = instructions.into_iter().peekable();
        while let Some(instr) = instructions.next() {
            if let asm::Instr::Jmp { label } = instr {
                if instructions.peek() != Some(&asm::Instr::Label(label)) {
                    new_instrs.push(asm::Instr::Jmp { label });
                }
            } else {
                new_instrs.push(instr);
            }
        }

        new_instrs
    }
}