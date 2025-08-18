use std::collections::{HashMap, HashSet};

use crate::mir::mir_def;

const BASE_INSTRUCTION_LIMIT: usize = 500;

pub fn inline(program: Vec<mir_def::TopLevel>, instr_count: &mut u64, tmp_count: &mut u64) -> Vec<mir_def::TopLevel> {
    let inliner = Inliner::new(instr_count, tmp_count);
    inliner.inline(program)
}

#[derive(Debug, Clone)]
struct FnInfo {
    func: mir_def::Function,
    successors: HashSet<mir_def::Ident>,
    predecessors: HashSet<mir_def::Ident>,
}

impl FnInfo {
    pub fn set_successors(&mut self) {
        for block in self.func.basic_blocks.blocks.values() {
            if let mir_def::BasicBlock::Generic(block) = block {
                for instr in block.instructions.iter() {
                    if let mir_def::Instruction::FunctionCall { ref name, .. } = instr.instr {
                        self.successors.insert(name.clone());
                    }
                }
            }
        }
    }

    pub fn set_predecessors(&mut self, p: HashSet<mir_def::Ident>) {
        self.predecessors = p;
    }
}

#[derive(Debug, Clone)]
struct FnGraph {
    pub fns: HashMap<mir_def::Ident, FnInfo>,
    pub extra: Vec<mir_def::TopLevel>,
    pub recursive: HashSet<mir_def::Ident>,
}

impl FnGraph {
    pub fn new(fns: HashMap<mir_def::Ident, FnInfo>, extra: Vec<mir_def::TopLevel>, recursive: HashSet<mir_def::Ident>) -> Self {
        Self {
            fns,
            extra,
            recursive
        }
    }

    pub fn empty() -> Self {
        Self::new(HashMap::new(), Vec::new(), HashSet::new())
    }

    pub fn from_tl_vec(v: Vec<mir_def::TopLevel>) -> Self {
        let mut fns = HashMap::new();
        let mut extra = Vec::new();

        for tl in v {
            match tl {
                mir_def::TopLevel::Fn(func) => {
                    fns.insert(func.name.clone(), FnInfo {
                        func,
                        successors: HashSet::new(),
                        predecessors: HashSet::new()
                    });
                },

                _ => extra.push(tl)
            }
        }

        let mut s = Self {
            fns,
            extra,
            recursive: HashSet::new()
        };

        s.generate_edges();
        s.generate_recursive();

        s
    }

    fn generate_edges(&mut self) {
        for func in self.fns.iter_mut() {
            func.1.set_successors();
        }

        let mut preds_map = HashMap::new();
        for id in self.fns.keys() {
            preds_map.insert(id.clone(), HashSet::new());
        }

        for (id, func) in &self.fns {
            func.successors.iter().for_each(|s| {
                preds_map.get_mut(s).unwrap().insert(id.clone());
            })
        }

        for (id, preds) in preds_map.into_iter() {
            self.fns.get_mut(&id).unwrap().set_predecessors(preds);
        }
    }

    fn generate_recursive(&mut self) {
        let mut index = 0;
        let mut stack = Vec::new();
        let mut indices = HashMap::new();
        let mut lowlink = HashMap::new();
        let mut on_stack = HashSet::new();

        let fns = self.fns.keys().cloned().collect::<Vec<_>>();

        for v in fns {
            if !indices.contains_key(&v) {
                self.strong_connect(
                    &v,
                    &mut index,
                    &mut stack,
                    &mut indices,
                    &mut lowlink,
                    &mut on_stack,
                );
            }
        }
    }

    // fuck this code btw
    fn strong_connect(
        &mut self,
        v: &mir_def::Ident,
        index: &mut i32,
        stack: &mut Vec<mir_def::Ident>,
        indices: &mut HashMap<mir_def::Ident, i32>,
        lowlink: &mut HashMap<mir_def::Ident, i32>,
        on_stack: &mut HashSet<mir_def::Ident>,
    ) {
        indices.insert(v.clone(), *index);
        lowlink.insert(v.clone(), *index);
        *index += 1;
        stack.push(v.clone());
        on_stack.insert(v.clone());

        if let Some(item) = self.fns.get(v) {
            for w in item.successors.clone() {
                let w = &w;
                if !indices.contains_key(w) {
                    self.strong_connect(
                        w, index, stack, indices, lowlink, on_stack
                    );
                    let lw = *lowlink.get(w).unwrap();
                    let lv = lowlink.get_mut(v).unwrap();
                    *lv = (*lv).min(lw);
                } else if on_stack.contains(w) {
                    let iw = *indices.get(w).unwrap();
                    let lv = lowlink.get_mut(v).unwrap();
                    *lv = (*lv).min(iw);
                }
            }
        }

        if lowlink[v] == indices[v] {
            let mut scc = Vec::new();
            loop {
                let w = stack.pop().unwrap();
                on_stack.remove(&w);
                scc.push(w.clone());
                if w == *v {
                    break;
                }
            }
            if scc.len() > 1 {
                self.recursive.extend(scc);
            } else {
                let only = &scc[0];
                if let Some(item) = self.fns.get(only) {
                    if item.successors.contains(only) {
                        self.recursive.insert(only.clone());
                    }
                }
            }
        }
    }

    pub fn into_tl_vec(self) -> Vec<mir_def::TopLevel> {
        let mut out = self.extra;
        for (_, func) in self.fns.into_iter() {
            out.push(mir_def::TopLevel::Fn(func.func));
        }
        out
    }
}

struct Inliner<'l> {
    fn_graph: FnGraph,
    instr_count: &'l mut u64,
    tmp_count: &'l mut u64,
}

impl<'l> Inliner<'l> {
    pub fn new(instr_count: &'l mut u64, tmp_count: &'l mut u64) -> Self {
        Self {
            fn_graph: FnGraph::empty(),
            instr_count,
            tmp_count
        }
    }

    pub fn inline(mut self, program: Vec<mir_def::TopLevel>) -> Vec<mir_def::TopLevel> {
        self.fn_graph = FnGraph::from_tl_vec(program);

        // TODO! generate the worklist better
        // probably like, the ones that have the least TOTAL predaccessors (like, their preds + their preds preds, etc) first
        self.fn_graph.fns.keys().cloned().collect::<Vec<_>>()
            .into_iter()
            .for_each(|n|self.run_inlining(&n));

        self.fn_graph.into_tl_vec()
    }

    fn run_inlining(&mut self, fn_name: &mir_def::Ident) {
        loop {
            let func = self.fn_graph.fns.get(fn_name).unwrap();
            let call = self.get_first_call(&func.func.basic_blocks);

            if let Some((block_id, instr_id)) = call {
                let block_id = block_id.clone();
                let new_term_id = self.gen_instr_id();
                let next_block_id = self.gen_block_id();
                let func = self.fn_graph.fns.get_mut(fn_name).unwrap();

                let block = func.func.basic_blocks.blocks.get_mut(&block_id).unwrap();
                let block = match block {
                    mir_def::BasicBlock::Generic(b) => b,
                    _ => unreachable!()
                };

                let call_idx = block.instructions.iter().position(|instr|instr.id==instr_id).unwrap();

                let instructions = std::mem::replace(&mut block.instructions, Vec::new());

                let mut staying = instructions;

                let next_b_instrs = staying.split_off(call_idx+1); // +1 so we can have the call at the end of staying, so we don't have to shift items in a vec
                let call_instr = staying.pop().unwrap(); // pop to remove the call
                let staying = staying; // no mut!!!!

                block.instructions = staying;

                let terminator = std::mem::replace(&mut block.terminator, mir_def::BTerminator { id: 0, term: mir_def::Terminator::Jump { target: mir_def::GenericBlockID::Generic(0) } });

                let next_block = mir_def::GenericBlock {
                    id: next_block_id,
                    instructions: next_b_instrs,
                    terminator,
                    predecessors: HashSet::new()
                };

                func.func.basic_blocks.blocks.insert(
                    mir_def::BlockID::Generic(next_block_id), 
                    mir_def::BasicBlock::Generic(next_block)
                );

                let (call_name, args, dst) = match call_instr.instr {
                    mir_def::Instruction::FunctionCall { name, args, dst } => (name, args, dst),
                    _ => unreachable!()
                };

                let (adding, start) = self.get_fn_code_for_inlining(&call_name, args, dst.as_ref(), next_block_id);

                // haha funny paste the same line haha funny
                let func = self.fn_graph.fns.get_mut(fn_name).unwrap();
                for (id, block) in adding {
                    func.func.basic_blocks.blocks.insert(id, block);
                }

                let block = func.func.basic_blocks.blocks.get_mut(&block_id).unwrap();
                let block = match block {
                    mir_def::BasicBlock::Generic(b) => b,
                    _ => unreachable!()
                };

                block.terminator = mir_def::BTerminator {
                    id: new_term_id,
                    term: mir_def::Terminator::Jump { target: start }
                }
            } else {
                break;
            }
        }
    }

    fn gen_block_id(&mut self) -> mir_def::GenericBlockID {
        *self.tmp_count += 1;
        mir_def::GenericBlockID::Generic(*self.tmp_count)
    }

    fn gen_instr_id(&mut self) -> mir_def::InstrID {
        *self.instr_count += 1;
        *self.instr_count
    }

    fn get_first_call<'a>(&self, cfg: &'a mir_def::CFG) -> Option<(&'a mir_def::BlockID, mir_def::InstrID)> {
        cfg.blocks.iter().find_map(|(id, block)| {
            let instrs = match block {
                mir_def::BasicBlock::Generic(b) => b,
                _ => return None
            };

            for instr in &instrs.instructions {
                if let mir_def::Instruction::FunctionCall { ref name, .. } = instr.instr {
                    if self.can_inline(name) {
                        return Some((id, instr.id));
                    }
                }
            }

            return None
        })
    } 

    fn get_fn_code_for_inlining(
        &mut self, 
        fn_name: &mir_def::Ident, 
        args: Vec<mir_def::Val>, 
        dst: Option<&mir_def::Ident>, 
        end_label: mir_def::GenericBlockID
    ) -> (HashMap<mir_def::BlockID, mir_def::BasicBlock>, mir_def::GenericBlockID) 
    {
        let func = &self.fn_graph.fns.get(fn_name).unwrap().func;
        let mut cfg = func.basic_blocks.clone();

        cfg.recalculate_predecessors();

        // INSERT PARAMETERS
        let starts = cfg.blocks.get(&mir_def::BlockID::Start).unwrap().get_successors();
        assert_eq!(starts.len(), 1);

        let start = starts.into_iter().next().unwrap();

        let start_gen = match start {
            mir_def::BlockID::Generic(g) => g,
            _ => unreachable!()
        };

        let start_b = cfg.blocks.get_mut(&start).unwrap();

        // should be generic
        let start_b = match start_b {
            &mut mir_def::BasicBlock::Generic(ref mut b) => b,
            _ => unreachable!()
        };

        let iter = args.into_iter().zip(func.params.iter()).map(|(arg, param)| {
            *self.instr_count += 1;
            mir_def::BInstruction {
                id: *self.instr_count,
                instr: mir_def::Instruction::Copy {
                    src: arg,
                    dst: param.clone()
                }
            }
        });

        let tmp_instrs = std::mem::replace(&mut start_b.instructions, Vec::new());

        let iter = iter.chain(tmp_instrs.into_iter());

        start_b.instructions = iter.collect();     

        // REPLACE RETURNS
        let end = cfg.blocks.get(&mir_def::BlockID::End).unwrap();
        
        let with_returns = end.get_predecessors();

        for b_id in with_returns {
            let block = cfg.blocks.get_mut(&b_id).unwrap();
            let block = match block {
                mir_def::BasicBlock::Generic(b) => b,
                _ => unreachable!()
            };

            let ret_val = match block.terminator.term {
                mir_def::Terminator::Return(ref v) => v,
                _ => unreachable!()
            };

            if let Some(ret_val) = ret_val {
                let dst = dst.unwrap().clone();
                let src = ret_val.clone();
                *self.instr_count += 1;
                block.instructions.push(mir_def::BInstruction {
                    id: *self.instr_count,
                    instr: mir_def::Instruction::Copy {
                        src,
                        dst
                    }
                });
            }

            *self.instr_count += 1;
            block.terminator = mir_def::BTerminator {
                id: *self.instr_count,
                term: mir_def::Terminator::Jump { target: end_label }
            }
        }

        // remove start & end
        cfg.blocks.remove(&mir_def::BlockID::Start);
        cfg.blocks.remove(&mir_def::BlockID::End);

        (cfg.blocks, start_gen)
    }

    fn can_inline(&self, fn_name: &mir_def::Ident) -> bool {
        if self.fn_graph.recursive.contains(fn_name) {
            return false;
        }

        let func = self.fn_graph.fns.get(fn_name).unwrap();

        // TODO! check if it has inline specifier, and if so increase the instruction limit

        let instr_count = func.func.basic_blocks.get_total_instructions();

        return instr_count <= BASE_INSTRUCTION_LIMIT;
    }
}