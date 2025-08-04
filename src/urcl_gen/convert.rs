use std::collections::{HashSet, VecDeque};

use crate::urcl_gen::asm;
use crate::mir::mir_def;
use crate::semantic_analysis::type_check::{IdentifierAttrs, SymbolTable};

pub struct ASMGenerator<'a> {
    pub symbol_table: &'a SymbolTable,
}

impl<'a> ASMGenerator<'a> {
    pub fn new(symbol_table: &'a SymbolTable) -> Self {
        Self {
            symbol_table
        }
    }

    pub fn mir_to_asm(&self, mir: mir_def::Program) -> asm::Program<asm::PVal> {
        asm::Program {
            header_info: asm::HeaderInfo::generic_16bit(),
            top_level_items: mir.top_level.into_iter().map(|tl| {
                match tl {
                    mir_def::TopLevel::Fn(func) => {
                        let mut instructions = Vec::new();

                        let params_len = func.params.len();
                        for (param, offset) in func.params.into_iter().zip(0..params_len) {
                            instructions.push(asm::Instr::LLod {
                                src: asm::Reg::bp_pval(),
                                offset: asm::PVal::Imm((offset * 2 + 2) as i32),
                                dst: asm::PVal::Var(param),
                            });
                        }

                        self.cfg_to_asm(func.basic_blocks, &mut instructions);
                        
                        asm::TopLevel::Fn(asm::Function {
                            name: func.name,
                            instructions
                        })
                    },
                    mir_def::TopLevel::Var(static_var) => {
                        asm::TopLevel::StaticVar {
                            name: static_var.name,
                            global: static_var.global,
                            init: static_var.init
                        }
                    }
                }
            }).collect()
        }
    }

    fn cfg_to_asm(&self, cfg: mir_def::CFG, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
        let mut worklist = VecDeque::new();
        worklist.push_front(mir_def::BlockID::Start);

        let mut done = HashSet::new();

        while let Some(block) = worklist.pop_front() {
            let block = cfg.blocks.get(&block).unwrap();

            for successor in block.get_successors() {
                if !done.contains(&successor) {
                    worklist.push_back(successor);
                    done.insert(successor);
                }
            }

            self.block_to_asm(block.clone(), instructions);
        }
    }

    fn block_to_asm(&self, block: mir_def::BasicBlock, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
        let block = if let mir_def::BasicBlock::Generic(block) = block {
            block
        } else { return; };

        instructions.push(asm::Instr::Label(block.id));

        block.instructions.into_iter().for_each(|i|self.instr_to_asm(i, instructions));
        self.term_to_asm(block.terminator, instructions);
    }

    fn mir_binop_to_asm(&self, op: mir_def::Binop, ty: &mir_def::Type) -> (asm::Binop, bool) {
        match op {
            mir_def::Binop::Add => (asm::Binop::Add, false),
            mir_def::Binop::Sub => (asm::Binop::Sub, false),
            mir_def::Binop::Mul => (asm::Binop::Mul, false),
            mir_def::Binop::Div => if ty.is_signed() { (asm::Binop::SDiv, false) } else { (asm::Binop::Div, false) },
            mir_def::Binop::Mod => (asm::Binop::Mod, false),
            mir_def::Binop::BitwiseAnd => (asm::Binop::And, false),
            mir_def::Binop::BitwiseOr => (asm::Binop::Or, false),
            mir_def::Binop::BitwiseXor => (asm::Binop::Xor, false),
            mir_def::Binop::LeftShift => (asm::Binop::LeftShift, false),
            mir_def::Binop::RightShift => (asm::Binop::RightShift, false),

            /*
            mir_def::Binop::Equal => (asm::Binop::Set(asm::Cond::Equal), true),
            mir_def::Binop::NotEqual => (asm::Binop::Set(asm::Cond::NotEqual), true),
            mir_def::Binop::LessThan => (asm::Binop::Set(asm::Cond::SLessThan), true),
            mir_def::Binop::LessEqual => (asm::Binop::Set(asm::Cond::SLessEqual), true),
            mir_def::Binop::GreaterThan => (asm::Binop::Set(asm::Cond::SGreaterThan), true),
            mir_def::Binop::GreaterEqual => (asm::Binop::Set(asm::Cond::SGreaterEqual), true),
             */

            mir_def::Binop::Equal => (asm::Binop::Set(asm::Cond::Equal), true),
            mir_def::Binop::NotEqual => (asm::Binop::Set(asm::Cond::NotEqual), true),

            mir_def::Binop::LessThan |
            mir_def::Binop::LessEqual |
            mir_def::Binop::GreaterThan |
            mir_def::Binop::GreaterEqual => {
                let is_signed = ty.is_signed();

                (asm::Binop::Set(match op {
                    mir_def::Binop::LessThan => if is_signed { asm::Cond::SLessThan } else { asm::Cond::LessThan },
                    mir_def::Binop::LessEqual => if is_signed { asm::Cond::SLessEqual } else { asm::Cond::LessEqual },
                    mir_def::Binop::GreaterThan => if is_signed { asm::Cond::SGreaterThan } else { asm::Cond::GreaterThan },
                    mir_def::Binop::GreaterEqual => if is_signed { asm::Cond::SGreaterEqual } else { asm::Cond::GreaterEqual },

                    _ => unreachable!()
                }), true)
            }
        }
    }

    fn get_ty_from_val(&self, val: &mir_def::Val) -> mir_def::Type {
        match val {
            mir_def::Val::Num(n) => {
                match n {
                    mir_def::Const::Int(_) => mir_def::Type::Int,
                    mir_def::Const::UInt(_) => mir_def::Type::UInt,
                }
            },
            mir_def::Val::Var(v) => {
                self.symbol_table.get(v).unwrap().ty.clone()
            }
        }
    }

    fn instr_to_asm(&self, instr: mir_def::Instruction, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
        match instr {
            mir_def::Instruction::Binary { op, src1, src2, dst } => {
                let ty = self.get_ty_from_val(&src1);
                let (binop, needs_bit_select) = self.mir_binop_to_asm(op, &ty);

                let src1 = self.val_to_asm(src1, instructions);
                let src2 = self.val_to_asm(src2, instructions);

                let dst = asm::PVal::Var(dst);

                instructions.push(asm::Instr::Binary { binop, src1, src2, dst: dst.clone() });

                if needs_bit_select {
                    instructions.push(asm::Instr::Binary { binop: asm::Binop::And, src1: dst.clone(), src2: asm::PVal::Imm(1), dst })
                }
            },
            mir_def::Instruction::Unary { op, inner, dst } => {
                let unop = match op {
                    mir_def::Unop::Complement => asm::Unop::BitwiseNot,
                    mir_def::Unop::Negate => asm::Unop::Negate
                };

                let src = self.val_to_asm(inner, instructions);

                instructions.push(asm::Instr::Unary { unop, src, dst: asm::PVal::Var(dst) });
            },
            mir_def::Instruction::Copy { src, dst } => {
                let src = self.val_to_asm(src, instructions);
                instructions.push(
                    asm::Instr::Mov { src, dst: asm::PVal::Var(dst) }
                );
            },
            mir_def::Instruction::GetAddress { src, dst } => {
                let entry = self.symbol_table.get(&src).unwrap();

                match entry.attrs {
                    IdentifierAttrs::Fn { .. } => unreachable!(),
                    IdentifierAttrs::Local => {
                        // lea... for now...
                        instructions.push(asm::Instr::Lea {
                            src: asm::PVal::Var(src),
                            dst: asm::PVal::Var(dst)
                        });
                    }
                    IdentifierAttrs::Static { .. } => {
                        let v = asm::PVal::Label(src);
                        instructions.push(asm::Instr::Mov {
                            src: v,
                            dst: asm::PVal::Var(dst)
                        })
                    }
                }
            }
            mir_def::Instruction::FunctionCall { name, args, dst } => {
                // TODO! maybe for iris mode, reserve a few registers for arguments so we can avoid pushing/popping everything?
                
                for arg in args.into_iter().rev() {
                    let arg = self.val_to_asm(arg, instructions);
                    instructions.push(asm::Instr::Push(arg));
                }

                instructions.push(asm::Instr::Call(name));

                instructions.push(asm::Instr::Mov { src: asm::Reg::pval(1), dst: asm::PVal::Var(dst) });
            },
            mir_def::Instruction::Load { src_ptr, dst } => {
                // TODO! use the normal lod instr for this
                let src = self.val_to_asm(src_ptr, instructions);
                instructions.push(asm::Instr::LLod {
                    src,
                    dst: asm::PVal::Var(dst),
                    offset: asm::PVal::Imm(0)
                })
            },
            mir_def::Instruction::Store { src, dst_ptr } => {
                // TODO! use the normal str instr for this
                let src = self.val_to_asm(src, instructions);
                let dst = self.val_to_asm(dst_ptr, instructions);

                instructions.push(asm::Instr::LStr {
                    src,
                    offset: asm::PVal::Imm(0),
                    dst
                });
            }
        }
    }

    fn term_to_asm(&self, term: mir_def::Terminator, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
        match term {
            mir_def::Terminator::Return(val) => {
                let val = self.val_to_asm(val, instructions);

                instructions.push(asm::Instr::Mov { src: val, dst: asm::Reg::pval(1) });
                instructions.push(asm::Instr::Ret);
            },
            mir_def::Terminator::Jump { target } => {
                instructions.push(asm::Instr::Jmp { label: target })
            },
            mir_def::Terminator::JumpCond { target, fail, src1, src2, cond } => {
                let src1 = self.val_to_asm(src1, instructions);
                let src2 = self.val_to_asm(src2, instructions);

                let cond = match cond {
                    mir_def::Cond::Equal => asm::Cond::Equal,
                    mir_def::Cond::NotEqual => asm::Cond::NotEqual,
                    mir_def::Cond::LessThan => asm::Cond::SLessThan,
                    mir_def::Cond::GreaterThan => asm::Cond::SGreaterThan,
                    mir_def::Cond::LessThanEqual => asm::Cond::SLessEqual,
                    mir_def::Cond::GreaterThanEqual => asm::Cond::SGreaterEqual,
                };

                instructions.push(asm::Instr::Branch { label: target, src1, src2, cond });
                instructions.push(asm::Instr::Jmp { label: fail });
            }
        }
    }

    fn val_to_asm(&self, val: mir_def::Val, _instructions: &mut Vec<asm::Instr<asm::PVal>>) -> asm::PVal {
        match val {
            mir_def::Val::Num(n) => asm::PVal::Imm(match n {
                mir_def::Const::Int(n) => n as i32,
                mir_def::Const::UInt(n) => n as i32,
            }),
            mir_def::Val::Var(v) => asm::PVal::Var(v)
        }
    }
}