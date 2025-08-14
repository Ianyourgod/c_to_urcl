use crate::mir::mir_def;

pub fn combine_cfg(cfg: mir_def::CFG) -> mir_def::CFG {
    let mut blocks = cfg.blocks;

    let mut blocks_iter = blocks.iter();

    while let Some(block) = blocks_iter.next() {
        let mut suc = block.1.get_successors();
        if suc.len() == 1 {
            let suc = suc.pop().unwrap();

            let s = blocks.get(&suc).unwrap();

            let suc_id = suc;

            if s.get_predecessors().len() == 1
                && let mir_def::BasicBlock::Generic(bloc) = block.1
                && let mir_def::BasicBlock::Generic(suc) = s
            {
                // combine!!!

                let mut instructions = bloc.instructions.clone();
                instructions.append(&mut suc.instructions.clone());

                let new_block = mir_def::BasicBlock::Generic(mir_def::GenericBlock {
                    id: bloc.id,
                    instructions,
                    terminator: suc.terminator.clone(),
                    predecessors: bloc.predecessors.clone()
                });

                blocks.insert(*block.0, new_block);
                blocks.remove(&suc_id);

                blocks_iter = blocks.iter();
            }
        }
    }

    mir_def::CFG { blocks }
}