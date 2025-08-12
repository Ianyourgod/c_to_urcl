use std::collections::{HashMap, HashSet, VecDeque};

use crate::mir::mir_def;

pub fn elim_program(program: mir_def::Program) -> mir_def::Program {
    mir_def::Program {
        top_level: program.top_level.into_iter().map(|tl| {
            match tl {
                mir_def::TopLevel::Fn(func) => mir_def::TopLevel::Fn(elim_function(func)),
                mir_def::TopLevel::Var(_) |
                mir_def::TopLevel::Const { .. } => tl
            }
        }).collect()
    }
}

fn elim_function(mut func: mir_def::Function) -> mir_def::Function {
    let mut new_cfg = mir_def::CFG {
        blocks: HashMap::new()
    };

    let mut worklist = VecDeque::new();
    worklist.push_back(mir_def::BlockID::Start);
    let mut complete = HashSet::new();

    while let Some(id) = worklist.pop_front() {
        let block = func.basic_blocks.blocks.remove(&id).unwrap();

        block.get_successors().into_iter().for_each(|id| {
            if !complete.contains(&id) {
                worklist.push_back(id);
                complete.insert(id);
            }
        });

        new_cfg.blocks.insert(id, block);
    }

    mir_def::Function {
        name: func.name,
        global: func.global,
        params: func.params,
        basic_blocks: new_cfg
    }
}