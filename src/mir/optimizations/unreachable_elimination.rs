use std::collections::{HashMap, HashSet, VecDeque};

use crate::mir::mir_def;

pub fn elim_cfg(mut cfg: mir_def::CFG) -> mir_def::CFG {
    let mut new_cfg = mir_def::CFG {
        blocks: HashMap::new()
    };

    let mut worklist = VecDeque::new();
    worklist.push_back(mir_def::BlockID::Start);
    let mut complete = HashSet::new();

    while let Some(id) = worklist.pop_front() {
        let block = cfg.blocks.remove(&id).unwrap();

        block.get_successors().into_iter().for_each(|id| {
            if !complete.contains(&id) {
                worklist.push_back(id);
                complete.insert(id);
            }
        });

        new_cfg.blocks.insert(id, block);
    }

    new_cfg
}