use std::collections::{HashMap, HashSet, VecDeque};

use crate::{mir::mir_def, semantic_analysis::type_check::SymbolTable};

pub fn propagate_cfg(cfg: mir_def::CFG, symbol_table: &SymbolTable, aliased: &HashSet<mir_def::Ident>) -> mir_def::CFG {
    let propagator = Propagator::new(symbol_table, aliased);
    propagator.run(cfg)
}

#[derive(Debug, Clone, PartialEq)]
struct Copy {
    pub src: mir_def::Val,
    pub dst: mir_def::Ident,
}

struct Propagator<'a> {
    instruction_annotations: HashMap<mir_def::InstrID, Vec<Copy>>,
    block_annotations: HashMap<mir_def::GenericBlockID, Vec<Copy>>,
    symbol_table: &'a SymbolTable,
    aliased: &'a HashSet<mir_def::Ident>,
}

impl<'a> Propagator<'a> {
    pub fn new(symbol_table: &'a SymbolTable, aliased: &'a HashSet<mir_def::Ident>) -> Self {
        Self {
            instruction_annotations: HashMap::new(),
            block_annotations: HashMap::new(),
            symbol_table,
            aliased
        }
    }

    pub fn run(mut self, cfg: mir_def::CFG) -> mir_def::CFG {
        self.find_copies(&cfg);
        mir_def::CFG {
            blocks: cfg.blocks.into_iter().map(|(id, block)| {
                (id, match block {
                    mir_def::BasicBlock::End { .. } |
                    mir_def::BasicBlock::Start { .. } => block,

                    mir_def::BasicBlock::Generic(block) => {
                        mir_def::BasicBlock::Generic(mir_def::GenericBlock {
                            id: block.id,
                            instructions: block.instructions.into_iter().filter_map(|i|self.rewrite_instruction(i)).collect(),
                            terminator: self.rewrite_terminator(block.terminator),
                            predecessors: block.predecessors
                        })
                    }
                })
            }).collect()
        }
    }

    #[inline]
    fn annotate_instr(&mut self, id: mir_def::InstrID, copies: Vec<Copy>) {
        self.instruction_annotations.insert(id, copies);
    }

    #[inline]
    fn annotate_block(&mut self, id: mir_def::GenericBlockID, copies: Vec<Copy>) {
        self.block_annotations.insert(id, copies);
    }

    #[inline]
    fn get_block_annotation(&self, id: &mir_def::GenericBlockID) -> Option<&Vec<Copy>> {
        self.block_annotations.get(id)
    }

    #[inline]
    fn get_instruction_annotation(&self, id: &mir_def::InstrID) -> Option<&Vec<Copy>> {
        self.instruction_annotations.get(id)
    }

    fn transfer(&mut self, block: &mir_def::GenericBlock, initial_copies: Vec<Copy>) {
        let mut current_copies = initial_copies;

        // TODO! don't clone this much

        for instr in block.instructions.iter() {
            self.annotate_instr(instr.id, current_copies.clone());

            match &instr.instr {
                mir_def::Instruction::Copy { src, dst } => {
                    if 
                        let mir_def::Val::Var(v) = src && 
                        current_copies.contains(&Copy { src: mir_def::Val::Var(dst.clone()), dst: v.clone() })
                    {
                        continue;
                    }

                    let dst_as_val = mir_def::Val::Var(dst.clone());
                    let src_as_ident = if let mir_def::Val::Var(v) = src { Some(v) } else { None };

                    current_copies = current_copies.into_iter().filter(|copy| {
                        !(copy.src == dst_as_val || Some(&copy.dst) == src_as_ident)
                    }).collect();

                    let src_ty = src.get_type(self.symbol_table);
                    let dst_ty = self.get_v_ty(dst);

                    if src_ty == *dst_ty || src_ty.is_signed() == dst_ty.is_signed() {
                        current_copies.push(Copy {
                            src: src.clone(),
                            dst: dst.clone()
                        })
                    }
                },
                mir_def::Instruction::FunctionCall { dst, .. } => {
                    current_copies = current_copies.into_iter().filter(|copy| {
                        !(
                            self.is_aliased(&copy.src) ||
                            self.is_v_aliased(&copy.dst) ||
                            if let Some(dst) = dst {
                                copy.src == mir_def::Val::Var(dst.clone()) ||
                                copy.dst == *dst
                            } else { false }

                        )
                    }).collect();
                },
                mir_def::Instruction::Store { .. } => {
                    current_copies = current_copies.into_iter().filter(|copy| {
                        !(self.is_aliased(&copy.src) || self.is_v_aliased(&copy.dst))
                    }).collect();
                },

                mir_def::Instruction::AddPtr { dst, .. } |
                mir_def::Instruction::GetAddress { dst, .. } |
                mir_def::Instruction::Load { dst, .. } |
                mir_def::Instruction::CopyToOffset { dst, .. } |
                mir_def::Instruction::CopyFromOffset { dst, .. } |
                mir_def::Instruction::Binary { dst, .. } |
                mir_def::Instruction::Unary { dst, .. } => {
                    current_copies = current_copies.into_iter().filter(|copy| {
                        !(
                            copy.src == mir_def::Val::Var(dst.clone()) ||
                            copy.dst == *dst
                        )
                    }).collect();
                },
            }
        }
        self.annotate_instr(block.terminator.id, current_copies.clone());

        self.annotate_block(block.id, current_copies);
    }

    fn get_v_ty<'b>(&'b self, v: &'b mir_def::Ident) -> &'b mir_def::Type {
        &self.symbol_table.get(v).unwrap().ty
    }

    fn is_v_aliased(&self, v: &mir_def::Ident) -> bool {
        self.aliased.contains(v)
    }

    fn is_aliased(&self, val: &mir_def::Val) -> bool {
        match val {
            mir_def::Val::Num(_) => false,
            mir_def::Val::Var(v) => self.is_v_aliased(v)
        }
    }

    fn intersection(a: Vec<Copy>, b: &Vec<Copy>) -> Vec<Copy> {
        // kinda inneficient, but we're using arrays so who cares
        a.into_iter().filter(|item|b.contains(item)).collect()
    }

    fn meet(&self, block: &mir_def::GenericBlock, all_copies: Vec<Copy>) -> Vec<Copy> {
        let mut copies = all_copies;
        
        for pred in block.predecessors.iter() {
            match pred {
                mir_def::BlockID::End => unreachable!(),
                mir_def::BlockID::Start => return vec![],

                mir_def::BlockID::Generic(id) => {
                    let other = self.get_block_annotation(id).unwrap();

                    copies = Self::intersection(copies, other)
                }
            }
        }

        copies
    }

    fn find_all_copies(cfg: &mir_def::CFG) -> Vec<Copy> {
        cfg.blocks.values().flat_map(|block| {
            match block {
                mir_def::BasicBlock::End { .. } |
                mir_def::BasicBlock::Start { .. } => vec![],

                mir_def::BasicBlock::Generic(block) => {
                    block.instructions.iter().filter_map(|instr| {
                        if let mir_def::Instruction::Copy { ref src, ref dst } = instr.instr {
                            Some(Copy {
                                src: src.clone(),
                                dst: dst.clone()
                            })
                        } else {
                            None
                        }
                    }).collect()
                }
            }
        }).collect()
    }

    fn find_copies(&mut self, cfg: &mir_def::CFG) {
        let all_copies = Self::find_all_copies(cfg);
        let mut worklist = VecDeque::new();

        // TODO! do this in reverse post order
        for block in cfg.blocks.values() {
            let mir_def::BasicBlock::Generic(block) = block
            else { continue };

            let id = block.id;

            worklist.push_back(block);
            self.annotate_block(id, all_copies.clone());
        }

        while let Some(block) = worklist.pop_front() {
            let old_annotation = self.get_block_annotation(&block.id).unwrap().clone();
            let incoming = self.meet(block, all_copies.clone());

            self.transfer(block, incoming);

            if old_annotation != *self.get_block_annotation(&block.id).unwrap() {
                for successor in block.terminator.term.get_successors() {
                    let successor = cfg.blocks.get(&successor).unwrap();
                    
                    match successor {
                        mir_def::BasicBlock::End { .. } => continue,
                        mir_def::BasicBlock::Start { .. } => unreachable!(),

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

    fn replace_operand(op: mir_def::Val, copies: &Vec<Copy>) -> mir_def::Val {
        let v_name = match op {
            mir_def::Val::Num(_) => return op,
            mir_def::Val::Var(ref v) => v
        };

        Self::replace_var(v_name, copies)
    }

    fn replace_var(v: &mir_def::Ident, copies: &Vec<Copy>) -> mir_def::Val {
        if let Some(copy) = copies.into_iter().find(|c|c.dst==*v) {
            copy.src.clone()
        } else {
            mir_def::Val::Var(v.clone())
        }
    }

    fn rewrite_instruction(&self, instruction: mir_def::BInstruction) -> Option<mir_def::BInstruction> {
        let copies = self.get_instruction_annotation(&instruction.id).unwrap();

        Some(mir_def::BInstruction {
            id: instruction.id,
            instr: 
                match instruction.instr {
                    mir_def::Instruction::Copy { src, dst } => {
                        let cpy = Copy { src: src.clone(), dst: dst.clone() };

                        for c in copies.iter() {
                            if
                                *c==cpy ||
                                (
                                    c.src == mir_def::Val::Var(dst.clone()) &&
                                    mir_def::Val::Var(c.dst.clone()) == src
                                )
                            {
                                return None;
                            }
                        }

                        let src = Self::replace_operand(src, copies);

                        mir_def::Instruction::Copy { src, dst }
                    },
                    mir_def::Instruction::Unary { op, inner, dst } => {
                        let inner = Self::replace_operand(inner, copies);
                        mir_def::Instruction::Unary { op, inner, dst }
                    },
                    mir_def::Instruction::Binary { op, src1, src2, dst } => {
                        let src1 = Self::replace_operand(src1, copies);
                        let src2 = Self::replace_operand(src2, copies);
                        mir_def::Instruction::Binary { op, src1, src2, dst }
                    },
                    mir_def::Instruction::FunctionCall { name, args, dst } => {
                        let args = args.into_iter().map(|a|Self::replace_operand(a, copies)).collect();

                        mir_def::Instruction::FunctionCall { name, args, dst }
                    },
                    mir_def::Instruction::Load { src_ptr, dst } => {
                        let src_ptr = Self::replace_operand(src_ptr, copies);

                        mir_def::Instruction::Load { src_ptr, dst }
                    },
                    mir_def::Instruction::Store { src, dst_ptr } => {
                        let src = Self::replace_operand(src, copies);
                        let dst_ptr = Self::replace_operand(dst_ptr, copies);

                        mir_def::Instruction::Store { src, dst_ptr }
                    },
                    mir_def::Instruction::AddPtr { ptr, idx, scale, dst } => {
                        let ptr = Self::replace_operand(ptr, copies);
                        let idx = Self::replace_operand(idx, copies);

                        mir_def::Instruction::AddPtr { ptr, idx, scale, dst }
                    },
                    mir_def::Instruction::CopyFromOffset { src, offset, dst } => {
                        let src = Self::replace_var(&src, copies);

                        let src = if let mir_def::Val::Var(v) = src { v } else { unreachable!() };

                        mir_def::Instruction::CopyFromOffset { src, offset, dst }
                    },
                    mir_def::Instruction::CopyToOffset { src, offset, dst } => {
                        let src = Self::replace_operand(src, copies);

                        mir_def::Instruction::CopyToOffset { src, offset, dst }
                    },


                    mir_def::Instruction::GetAddress { .. } => instruction.instr
                }
        })
    }

    fn rewrite_terminator(&self, terminator: mir_def::BTerminator) -> mir_def::BTerminator {
        let copies = self.get_instruction_annotation(&terminator.id).unwrap();

        mir_def::BTerminator {
            id: terminator.id,
            term: 
                match terminator.term {
                    mir_def::Terminator::Return(v) => {
                        let v = v.map(|v|Self::replace_operand(v, copies));
                        mir_def::Terminator::Return(v)
                    },
                    mir_def::Terminator::JumpCond { target, fail, src1, src2, cond } => {
                        let src1 = Self::replace_operand(src1, copies);
                        let src2 = Self::replace_operand(src2, copies);
                        mir_def::Terminator::JumpCond { target, fail, src1, src2, cond }
                    },

                    mir_def::Terminator::Jump { .. } => terminator.term
                }
        }
    }
}