use std::collections::{HashMap, HashSet, VecDeque};

use crate::{mir::mir_def, semantic_analysis::type_check::{IdentifierAttrs, SymbolTable}};

pub fn dead_store_fix_cfg(cfg: mir_def::CFG, symbol_table: &SymbolTable, aliased: &HashSet<mir_def::Ident>) -> mir_def::CFG {
    let dead_store_fixer = DeadStoreFixer::new(symbol_table, aliased);
    dead_store_fixer.run(cfg)
}

struct DeadStoreFixer<'a> {
    instruction_annotations: HashMap<mir_def::InstrID, HashSet<mir_def::Ident>>,
    block_annotations: HashMap<mir_def::GenericBlockID, HashSet<mir_def::Ident>>,
    symbol_table: &'a SymbolTable,
    aliased: &'a HashSet<mir_def::Ident>,
}

impl<'a> DeadStoreFixer<'a> {
    pub fn new(symbol_table: &'a SymbolTable, aliased: &'a HashSet<mir_def::Ident>) -> Self {
        Self {
            instruction_annotations: HashMap::new(),
            block_annotations: HashMap::new(),
            symbol_table,
            aliased
        }
    }

    pub fn run(mut self, cfg: mir_def::CFG) -> mir_def::CFG {
        self.liveness_analysis(&cfg);
        mir_def::CFG {
            blocks: cfg.blocks.into_iter().map(|(id, block)| {
                (id, match block {
                    mir_def::BasicBlock::End { .. } |
                    mir_def::BasicBlock::Start { .. } => block,

                    mir_def::BasicBlock::Generic(block) => {
                        mir_def::BasicBlock::Generic(mir_def::GenericBlock {
                            id: block.id,
                            instructions: block.instructions.into_iter().filter(|i|{
                                !self.is_dead_store(i)
                            }).collect(),
                            terminator: block.terminator,
                            predecessors: block.predecessors
                        })
                    }
                })
            }).collect()
        }
    }

    #[inline]
    fn annotate_instr(&mut self, id: mir_def::InstrID, copies: HashSet<mir_def::Ident>) {
        self.instruction_annotations.insert(id, copies);
    }

    #[inline]
    fn annotate_block(&mut self, id: mir_def::GenericBlockID, copies: HashSet<mir_def::Ident>) {
        self.block_annotations.insert(id, copies);
    }

    #[inline]
    fn get_block_annotation(&self, id: &mir_def::GenericBlockID) -> Option<&HashSet<mir_def::Ident>> {
        self.block_annotations.get(id)
    }

    #[inline]
    fn get_instruction_annotation(&self, id: &mir_def::InstrID) -> Option<&HashSet<mir_def::Ident>> {
        self.instruction_annotations.get(id)
    }

    fn transfer(&mut self, block: &mir_def::GenericBlock, initial_alive: HashSet<mir_def::Ident>) {
        let mut current_live = initial_alive;

        // TODO! don't clone this much

        self.annotate_instr(block.terminator.id, current_live.clone());
        match &block.terminator.term {
            mir_def::Terminator::Jump { .. } => (),

            mir_def::Terminator::Return(v) => {
                if let Some(mir_def::Val::Var(v)) = v {
                    current_live.insert(v.clone());
                }
            },
            mir_def::Terminator::JumpCond { src1, src2, .. } => {
                if let mir_def::Val::Var(v) = src1 {
                    current_live.insert(v.clone());
                }
                if let mir_def::Val::Var(v) = src2 {
                    current_live.insert(v.clone());
                }
            }
        }
        for instr in block.instructions.iter().rev() {
            self.annotate_instr(instr.id, current_live.clone());

            match &instr.instr {
                mir_def::Instruction::AddPtr { ptr: src1, idx: src2, dst, .. } |
                mir_def::Instruction::Binary { src1, src2, dst, .. } => {
                    current_live.remove(dst);
                    if let mir_def::Val::Var(v) = src1 {
                        current_live.insert(v.clone());
                    }
                    if let mir_def::Val::Var(v) = src2 {
                        current_live.insert(v.clone());
                    }
                },
                mir_def::Instruction::Copy { src, dst } |
                mir_def::Instruction::Unary { src, dst, .. } => {
                    current_live.remove(dst);
                    if let mir_def::Val::Var(v) = src {
                        current_live.insert(v.clone());
                    }
                },
                mir_def::Instruction::FunctionCall { args, dst, .. } => {
                    if let Some(dst) = dst {
                        current_live.remove(dst);
                    }
                    for arg in args {
                        if let mir_def::Val::Var(v) = arg {
                            current_live.insert(v.clone());
                        }
                    }
                    for s in self.aliased {
                        current_live.insert(s.clone());
                    }
                },
                mir_def::Instruction::Load { src_ptr, dst } => {
                    current_live.remove(dst);
                    if let mir_def::Val::Var(v) = src_ptr {
                        current_live.insert(v.clone());
                    }
                    for s in self.aliased {
                        current_live.insert(s.clone());
                    }
                },
                mir_def::Instruction::GetAddress { dst, .. } => {
                    current_live.remove(dst);
                },
                mir_def::Instruction::Store { src, dst_ptr } => {
                    if let mir_def::Val::Var(v) = src {
                        current_live.insert(v.clone());
                    }
                    if let mir_def::Val::Var(v) = dst_ptr {
                        current_live.insert(v.clone());
                    }
                },
                mir_def::Instruction::CopyToOffset { src, .. } => {
                    if let mir_def::Val::Var(v) = src {
                        current_live.insert(v.clone());
                    }
                },
                mir_def::Instruction::CopyFromOffset { src, dst, .. } => {
                    current_live.remove(dst);
                    current_live.insert(src.clone());
                }
            }
        }

        self.annotate_block(block.id, current_live);
    }

    fn meet(&self, block: &mir_def::GenericBlock, all_statics: &HashSet<mir_def::Ident>) -> HashSet<mir_def::Ident> {
        let mut live_vars = HashSet::new();
        
        for succ in block.terminator.term.get_successors() {
            match succ {
                mir_def::BlockID::End => live_vars = live_vars.union(all_statics).cloned().collect(),
                mir_def::BlockID::Start => unreachable!(),

                mir_def::BlockID::Generic(id) => {
                    let other = self.get_block_annotation(&id).unwrap();

                    live_vars = live_vars.union(other).cloned().collect();
                }
            }
        }

        live_vars
    }

    fn get_all_statics(&self) -> HashSet<mir_def::Ident> {
        self.symbol_table.table.iter().filter_map(|(name, entry)| {
            if let IdentifierAttrs::Static { .. } = entry.attrs {
                Some(name.clone())
            } else { None }
        }).collect()
    }

    fn liveness_analysis(&mut self, cfg: &mir_def::CFG) {
        let statics = self.get_all_statics();
        let mut worklist = VecDeque::new();

        // TODO! do this in post order
        for block in cfg.blocks.values() {
            let mir_def::BasicBlock::Generic(block) = block
            else { continue };

            let id = block.id;

            worklist.push_back(block);
            self.annotate_block(id, HashSet::new());
        }

        while let Some(block) = worklist.pop_front() {
            let old_annotation = self.get_block_annotation(&block.id).unwrap().clone();
            let incoming = self.meet(block, &statics);

            self.transfer(block, incoming);

            if old_annotation != *self.get_block_annotation(&block.id).unwrap() {
                for predecessor in &block.predecessors {
                    let predecessor = cfg.blocks.get(&predecessor).unwrap();
                    
                    match predecessor {
                        mir_def::BasicBlock::End { .. } => unreachable!(),
                        mir_def::BasicBlock::Start { .. } => continue,

                        mir_def::BasicBlock::Generic(block) => {
                            if !worklist.contains(&block) {
                                worklist.push_back(block);
                            }
                        }
                    }
                }
            }
        }
    }

    fn is_dead_store(&self, instruction: &mir_def::BInstruction) -> bool {
        if matches!(instruction.instr, mir_def::Instruction::FunctionCall { .. } | mir_def::Instruction::Store { .. }) {
            return false;
        }

        if let Some(dst) = instruction.instr.get_dst() {
            let live_vars = self.get_instruction_annotation(&instruction.id).unwrap();

            if !live_vars.contains(dst) {
                return true;
            }
        }

        return false;
    }
}