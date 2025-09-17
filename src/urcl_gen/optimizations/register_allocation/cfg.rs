use std::collections::{HashMap, HashSet, VecDeque};

use crate::urcl_gen::{asm, convert::ConvInfo, cpu_definitions::CPUDefinition};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Reg {
    R(asm::Reg),
    P(asm::Ident),
}

type LiveRegs = HashSet<Reg>;
type InstrID = (BlockID, usize);

#[derive(Debug)]
pub struct CFG<'a, CPU: CPUDefinition> {
    pub blocks: Vec<BasicBlock<'a>>,
    cpu: &'a CPU,
    block_annotations: HashMap<BlockID, LiveRegs>,
    instr_annotations: HashMap<InstrID, LiveRegs>,
    conv_info: &'a ConvInfo,
    fn_name: &'a asm::Ident,
}

impl<'a, CPU: CPUDefinition> CFG<'a, CPU> {
    #[allow(unused)]
    pub fn recalculate_predecessors(&mut self) {
        let mut preds_map = HashMap::new();
        for b in self.blocks.iter() {
            preds_map.insert(b.get_id(), HashSet::new());
        }

        for block in self.blocks.iter() {
            let id = block.get_id();
            block.get_successors(self).into_iter().for_each(|s| {
                preds_map.get_mut(&s).unwrap().insert(id);
            })
        }

        for (id, preds) in preds_map.into_iter() {
            self.blocks.iter_mut().find(|b|id==b.get_id()).unwrap().set_predecessors(preds);
        }
    }
    
    pub fn construct_from_instrs(instrs: &'a Vec<asm::Instr<asm::PVal>>, cpu: &'a CPU, conv_info: &'a ConvInfo, fn_name: &'a asm::Ident) -> Self {
        let bb = Self::partition_into_basic_blocks(instrs);
        let mut s = Self::convert_to_basic_blocks(bb, cpu, conv_info, fn_name);
        s.analyze_liveness();
        s
    }

    fn partition_into_basic_blocks<'b>(instrs: &'b Vec<asm::Instr<asm::PVal>>) -> Vec<&'b[asm::Instr<asm::PVal>]> {
        let mut finished_blocks = Vec::new();
        let mut starting_idx = 0;
        for (idx, instr) in instrs.iter().enumerate() {
            match instr {
                asm::Instr::Label(_) => {
                    if starting_idx + 1 != idx {
                        finished_blocks.push(&instrs[starting_idx..idx]);
                    }
                    starting_idx = idx;
                },
                asm::Instr::Jmp { .. } |
                asm::Instr::Branch { .. } |
                asm::Instr::Ret => {
                    finished_blocks.push(&instrs[starting_idx..idx]);
                    starting_idx = idx;
                }
                _ => (),
            }
        }

        finished_blocks
    }

    fn convert_to_basic_blocks(blocks: Vec<&'a[asm::Instr<asm::PVal>]>, cpu: &'a CPU, conv_info: &'a ConvInfo, fn_name: &'a asm::Ident) -> Self {
        let mut nodes = Vec::with_capacity(blocks.len() + 2);

        let start = BasicBlock::Start { successors: HashSet::new() };
        nodes.push(start);

        let b_len = blocks.len();
        for (i, instrs) in blocks.into_iter().enumerate() {
            let id = nodes.len();

            nodes.push(BasicBlock::Generic(GenericBlock {
                id: asm::GenericBlockID::Generic(id as u64),
                instructions: instrs,
                predecessors: HashSet::new(),
                immediate_successor: if i+1 < b_len {
                    Some(BlockID::Generic(asm::GenericBlockID::Generic((id+1) as u64)))
                } else { None }
            }));
        }

        let end = BasicBlock::End { predecessors: HashSet::new() };
        nodes.push(end);

        Self {
            blocks: nodes,
            cpu,
            block_annotations: HashMap::new(),
            instr_annotations: HashMap::new(),
            conv_info,
            fn_name
        }
    }

    fn analyze_liveness(&mut self) {
        let mut worklist = VecDeque::new();

        self.recalculate_predecessors();

        // TODO! do this in post order
        for block in self.blocks.iter() {
            let id = block.get_id();

            let BasicBlock::Generic(block) = block
            else { continue };

            self.block_annotations.insert(id, LiveRegs::new());

            worklist.push_back(block);
        }

        while let Some(block) = worklist.pop_front() {
            let id = BlockID::Generic(block.id);
            let old_annotation = self.get_block_annotation(&id).unwrap().clone();
            let incoming = self.meet(block);

            // transfer, inlined because rust has bad inner borrow checking for fns
            let mut current_live_regs = incoming;

            for (i, instr) in block.instructions.iter().enumerate().rev() {
                self.instr_annotations.insert((id, i), current_live_regs.clone());

                let (used, updated) = self.find_used_and_updated(instr);

                for r in updated {
                    current_live_regs.remove(&r);
                }

                for r in used {
                    current_live_regs.insert(r);
                }
            }

            self.block_annotations.insert(id, current_live_regs);

            if old_annotation != *self.get_block_annotation(&id).unwrap() {
                for predecessor in &block.predecessors {
                    let predecessor = self.blocks.iter().find(|b|b.get_id()==*predecessor).unwrap();
                    
                    match predecessor {
                        BasicBlock::End { .. } => unreachable!(),
                        BasicBlock::Start { .. } => continue,

                        BasicBlock::Generic(block) => {
                            if !worklist.contains(&block) {
                                worklist.push_back(block);
                            }
                        }
                    }
                }
            }
        }
    }

    // TODO! clone less
    fn meet(&self, block: &GenericBlock) -> LiveRegs {
        let mut live_regs = LiveRegs::new();

        for successor in block.get_successors(self) {
            match successor {
                BlockID::End => {live_regs.insert(self.conv_info.get(self.fn_name).unwrap().ret_vessel.clone());},
                BlockID::Start => unreachable!(),

                BlockID::Generic(_) => {
                    println!("{:?}", successor);
                    let succ_live_regs = self.get_block_annotation(&successor).unwrap();
                    live_regs.extend(succ_live_regs.iter().cloned());
                }
            }
        }

        live_regs
    }

    pub fn find_used_and_updated(&self, instr: &'a asm::Instr<asm::PVal>) -> (Vec<Reg>, Vec<Reg>) {
        match instr {
            asm::Instr::Lea { src, dst } |
            asm::Instr::LLod { src, dst, .. } |
            asm::Instr::Unary { src, dst, .. } |
            asm::Instr::Mov { src, dst } => {
                (Self::pval_to_rv(src), Self::pval_to_rv(dst))
            },
            asm::Instr::Binary { src1, src2, dst, .. } => {
                (Self::pvals_to_rv(&[src1, src2]), Self::pval_to_rv(dst))
            },

            asm::Instr::LStr { src: src1, dst: src2, .. } |
            asm::Instr::Cpy { src: src1, dst: src2 } |
            asm::Instr::Branch { src1, src2, .. } => {
                (Self::pvals_to_rv(&[src1, src2]), Vec::new())
            },

            asm::Instr::Push(src) => {
                (Self::pval_to_rv(src), Vec::new())
            },
            asm::Instr::Pop(dst) => {
                (Vec::new(), Self::pval_to_rv(dst))
            },

            asm::Instr::Call(fn_name) => {
                let f = self.conv_info.get(fn_name).unwrap();

                // used = get regs used to pass params
                let used = f.params.iter().map(|r|Reg::R(*r)).collect();
                let updated = self.cpu.get_caller_saved().into_iter().map(|r|Reg::R(r)).collect();

                (used, updated)
            }

            asm::Instr::Jmp { .. } |
            asm::Instr::Label(_) |
            asm::Instr::Ret |
            asm::Instr::Comment(_) => (Vec::new(), Vec::new())
        }
    }

    fn pvals_to_rv(ps: &[&asm::PVal]) -> Vec<Reg> {
        ps.into_iter().filter_map(|p|Self::pval_to_r(*p)).collect()
    }

    fn pval_to_rv(pval: &asm::PVal) -> Vec<Reg> {
        Self::pval_to_r(pval).into_iter().collect()
    }

    pub fn pval_to_r(pval: &asm::PVal) -> Option<Reg> {
        match pval {
            asm::PVal::Imm(_) | asm::PVal::Label(_) => None,

            asm::PVal::Reg(r) => Some(Reg::R(*r)),
            asm::PVal::Var(v) => Some(Reg::P(v.clone()))
        }
    }

    #[inline]
    fn get_block_annotation<'b>(&'b self, id: &BlockID) -> Option<&'b LiveRegs> {
        self.block_annotations.get(id)
    }

    #[inline]
    pub fn get_instr_annotation<'b>(&'b self, id: &InstrID) -> Option<&'b LiveRegs> {
        self.instr_annotations.get(id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BasicBlock<'a> {
    Start {
        successors: HashSet<BlockID>,
    },
    End {
        predecessors: HashSet<BlockID>,
    },
    Generic(GenericBlock<'a>)
}

impl BasicBlock<'_> {
    #[allow(unused)]
    // TODO! make this not clone every time
    pub fn get_successors<CPU: CPUDefinition>(&self, cfg: &CFG<CPU>) -> HashSet<BlockID> {
        match self {
            BasicBlock::Generic(g) => g.get_successors(cfg),
            BasicBlock::Start { successors } => successors.clone(),
            BasicBlock::End { .. } => HashSet::new()
        }
    }

    #[allow(unused)]
    // TODO! make this not clone every time
    pub fn get_predecessors(&self) -> HashSet<BlockID> {
        match self {
            BasicBlock::End { predecessors } => predecessors.clone(),
            BasicBlock::Start { .. } => HashSet::new(),
            BasicBlock::Generic(b) => b.predecessors.clone(),
        }
    }

    #[allow(unused)]
    pub fn set_predecessors(&mut self, preds: HashSet<BlockID>) {
        match self {
            BasicBlock::Generic(GenericBlock { predecessors, .. }) |
            BasicBlock::End { predecessors } => *predecessors = preds,

            BasicBlock::Start { .. } => ()
        }
    }

    pub fn get_id(&self) -> BlockID {
        match self {
            BasicBlock::End { .. } => BlockID::End,
            BasicBlock::Start { .. } => BlockID::Start,
            BasicBlock::Generic(b) => BlockID::Generic(b.id)
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GenericBlock<'a> {
    pub id: asm::GenericBlockID,
    pub instructions: &'a[asm::Instr<asm::PVal>],
    pub predecessors: HashSet<BlockID>,
    pub immediate_successor: Option<BlockID>,
}

impl GenericBlock<'_> {
    pub fn get_successors<CPU: CPUDefinition>(&self, cfg: &CFG<CPU>) -> HashSet<BlockID> {
        let mut s = HashSet::new();
        let b = self.instructions.last().map(|instr|{
            match instr {
                asm::Instr::Ret => Some(BlockID::End),
                asm::Instr::Branch { label, .. } |
                asm::Instr::Jmp { label } => Some(BlockID::Generic(*label)),
                _ => None
            }
        }).flatten();

        if let Some(is) = self.immediate_successor { s.insert(is); }
        if let Some(b_id) = b {
            let b = cfg.blocks.iter().find(|b| {
                let BasicBlock::Generic(b) = b
                else {
                    return false;
                };

                let Some(asm::Instr::Label(l)) = b.instructions.first()
                else {
                    return false;
                };

                let BlockID::Generic(gid) = b_id
                else {
                    return false;
                };

                gid == *l
            }).unwrap();
            s.insert(b.get_id());
        }

        s
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum BlockID {
    Generic(asm::GenericBlockID),
    Start,
    End
}