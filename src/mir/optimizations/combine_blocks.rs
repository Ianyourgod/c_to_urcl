use crate::mir::mir_def;

pub fn combine_program(program: mir_def::Program) -> mir_def::Program {
    mir_def::Program {
        top_level: program.top_level.into_iter().map(|tl| {
            match tl {
                mir_def::TopLevel::Fn(func) => mir_def::TopLevel::Fn(combine_func(func)),

                mir_def::TopLevel::Const { .. } |
                mir_def::TopLevel::Var(_) => tl
            }
        }).collect()
    }
}

fn combine_func(function: mir_def::Function) -> mir_def::Function {
    let mut blocks = function.basic_blocks.blocks;

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

    mir_def::Function {
        name: function.name,
        global: function.global,
        params: function.params,
        basic_blocks: mir_def::CFG { blocks }
    }
}