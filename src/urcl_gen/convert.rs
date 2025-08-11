use std::collections::{HashSet, VecDeque};
use std::rc::Rc;

use crate::urcl_gen::{asm, cpu_definitions::CPUDefinition};
use crate::mir::mir_def;
use crate::semantic_analysis::type_check::{IdentifierAttrs, SymbolTable, SymbolTableEntry, TypeTable};
use crate::Ident;

pub struct ASMGenerator<'a, CPU> 
where
    CPU: CPUDefinition
{
    pub symbol_table: &'a mut SymbolTable,
    cpu: &'a CPU,
    type_table: &'a TypeTable,
    tmp_count: usize,
}

impl<'a, T: CPUDefinition> ASMGenerator<'a, T> {
    pub fn new(symbol_table: &'a mut SymbolTable, type_table: &'a TypeTable, cpu: &'a T) -> Self {
        Self {
            symbol_table,
            cpu,
            type_table,
            tmp_count: 0,
        }
    }

    pub fn mir_to_asm(mut self, mir: mir_def::Program) -> asm::Program<'a, asm::PVal, T> {
        asm::Program {
            cpu: self.cpu,
            top_level_items: mir.top_level.into_iter().map(|tl| {
                match tl {
                    mir_def::TopLevel::Fn(func) => {
                        let mut instructions = Vec::new();

                        let params_len = func.params.len();
                        for (param, offset) in func.params.into_iter().zip(0..params_len) {
                            instructions.push(asm::Instr::LLod {
                                src: asm::Reg::bp_pval(self.cpu),
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
                    },
                    mir_def::TopLevel::Const { name, ty: _ty, init } => {
                        asm::TopLevel::StaticConst { name, init }
                    }
                }
            }).collect()
        }
    }

    fn cfg_to_asm(&mut self, cfg: mir_def::CFG, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
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

    fn block_to_asm(&mut self, block: mir_def::BasicBlock, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
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
                    mir_def::Const::Char(_) => mir_def::Type::Char,
                    mir_def::Const::UChar(_) => mir_def::Type::UChar,

                    mir_def::Const::EnumItem { .. } => unreachable!(),
                }
            },
            mir_def::Val::Var(v) => {
                self.get_ty_from_var(v)
            }
        }
    }

    #[inline]
    fn get_ty_from_var(&self, var: &Ident) -> mir_def::Type {
        self.symbol_table.get(var).unwrap().ty.clone()
    }

    fn gen_tmp_name(&mut self) -> Ident {
        self.tmp_count += 1;
        Rc::new(format!(".conv.asm.v.{}.", self.tmp_count))
    }

    fn make_tmp_var(&mut self, ty: mir_def::Type) -> Ident {
        let name = self.gen_tmp_name();
        let attrs = IdentifierAttrs::Local;
        self.symbol_table.insert(name.clone(), SymbolTableEntry::new(ty, attrs));
        name
    }

    fn instr_to_asm(&mut self, instr: mir_def::Instruction, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
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
                if let mir_def::Type::Struct(name) | mir_def::Type::Union(name) = self.get_ty_from_val(&src) {
                    let entry = self.type_table.entries.get(&name).unwrap();

                    let tmp_src_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    let src = self.val_to_asm(src, instructions);
                    instructions.push(asm::Instr::Lea {
                        src,
                        dst: asm::PVal::Var(tmp_src_ptr.clone())
                    });

                    let tmp_dst_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    instructions.push(asm::Instr::Lea {
                        src: asm::PVal::Var(dst),
                        dst: asm::PVal::Var(tmp_dst_ptr.clone())
                    });

                    self.copy_bytes(tmp_src_ptr, tmp_dst_ptr, entry.size, instructions);

                    return;
                }

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
                    },
                    IdentifierAttrs::Constant { .. } |
                    IdentifierAttrs::Static { .. } => {
                        let v = asm::PVal::Label(src);
                        instructions.push(asm::Instr::Mov {
                            src: v,
                            dst: asm::PVal::Var(dst)
                        })
                    },
                }
            }
            mir_def::Instruction::FunctionCall { name, args, dst } => {
                // TODO! maybe for iris mode, reserve a few registers for arguments so we can avoid pushing/popping everything?
                
                for arg in args.into_iter().rev() {
                    let arg = self.val_to_asm(arg, instructions);
                    instructions.push(asm::Instr::Push(arg));
                }

                instructions.push(asm::Instr::Call(name));

                dst.map(|dst|instructions.push(asm::Instr::Mov { src: asm::Reg::pval(1), dst: asm::PVal::Var(dst) }));
            },
            mir_def::Instruction::Load { src_ptr, dst } => {
                if let mir_def::Type::Struct(name) | mir_def::Type::Union(name) = self.get_ty_from_var(&dst) {
                    let entry = self.type_table.entries.get(&name).unwrap();

                    let tmp_src_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    let src = self.val_to_asm(src_ptr, instructions);
                    instructions.push(asm::Instr::Mov {
                        src,
                        dst: asm::PVal::Var(tmp_src_ptr.clone())
                    });

                    let tmp_dst_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    instructions.push(asm::Instr::Lea {
                        src: asm::PVal::Var(dst),
                        dst: asm::PVal::Var(tmp_dst_ptr.clone())
                    });

                    self.copy_bytes(tmp_src_ptr, tmp_dst_ptr, entry.size, instructions);

                    return;
                }

                let src = self.val_to_asm(src_ptr, instructions);
                instructions.push(asm::Instr::LLod {
                    src,
                    dst: asm::PVal::Var(dst),
                    offset: asm::PVal::Imm(0)
                })
            },
            mir_def::Instruction::Store { src, dst_ptr } => {
                if let mir_def::Type::Struct(name) | mir_def::Type::Union(name) = self.get_ty_from_val(&src) {
                    let entry = self.type_table.entries.get(&name).unwrap();

                    let tmp_src_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    let src = self.val_to_asm(src, instructions);
                    instructions.push(asm::Instr::Lea {
                        src,
                        dst: asm::PVal::Var(tmp_src_ptr.clone())
                    });

                    let tmp_dst_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    let dst = self.val_to_asm(dst_ptr, instructions);
                    instructions.push(asm::Instr::Mov {
                        src: dst,
                        dst: asm::PVal::Var(tmp_dst_ptr.clone())
                    });

                    self.copy_bytes(tmp_src_ptr, tmp_dst_ptr, entry.size, instructions);

                    return;
                }

                let src = self.val_to_asm(src, instructions);
                let dst = self.val_to_asm(dst_ptr, instructions);

                instructions.push(asm::Instr::LStr {
                    src,
                    offset: asm::PVal::Imm(0),
                    dst
                });
            },
            mir_def::Instruction::AddPtr { ptr, idx, scale, dst } => {
                // mult idx and scale, then add with ptr
                let ptr = self.val_to_asm(ptr, instructions);
                let idx = self.val_to_asm(idx, instructions);

                instructions.push(asm::Instr::Binary {
                    binop: asm::Binop::Mul,
                    src1: idx,
                    src2: asm::PVal::Imm(scale as i32),
                    dst: asm::PVal::Var(dst.clone())
                });

                instructions.push(asm::Instr::Binary {
                    binop: asm::Binop::Add,
                    src1: ptr,
                    src2: asm::PVal::Var(dst.clone()),
                    dst: asm::PVal::Var(dst.clone())
                });
            },
            mir_def::Instruction::CopyToOffset { src, offset, dst } => {
                if let mir_def::Type::Struct(name) | mir_def::Type::Union(name) = self.get_ty_from_val(&src) {
                    let entry = self.type_table.entries.get(&name).unwrap();

                    let tmp_src_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    let src = self.val_to_asm(src, instructions);
                    instructions.push(asm::Instr::Lea {
                        src,
                        dst: asm::PVal::Var(tmp_src_ptr.clone())
                    });

                    let tmp_dst_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    instructions.push(asm::Instr::Lea {
                        src: asm::PVal::Var(dst),
                        dst: asm::PVal::Var(tmp_dst_ptr.clone())
                    });
                    instructions.push(asm::Instr::Binary {
                        binop: asm::Binop::Add,
                        src1: asm::PVal::Var(tmp_dst_ptr.clone()),
                        src2: asm::PVal::Imm(offset as i32),
                        dst: asm::PVal::Var(tmp_dst_ptr.clone())
                    });

                    self.copy_bytes(tmp_src_ptr, tmp_dst_ptr, entry.size, instructions);

                    return;
                }

                let src = self.val_to_asm(src, instructions);
                let tmp_out = self.make_tmp_var(mir_def::Type::Pointer(Box::new(self.get_ty_from_var(&dst))));
                let tmp_out = asm::PVal::Var(tmp_out.clone());

                instructions.push(asm::Instr::Lea { src: asm::PVal::Var(dst), dst: tmp_out.clone() });
                instructions.push(asm::Instr::LStr {
                    src,
                    dst: tmp_out,
                    offset: asm::PVal::Imm(offset as i32)
                });
            },
            mir_def::Instruction::CopyFromOffset { src, offset, dst } => {
                if let mir_def::Type::Struct(name) | mir_def::Type::Union(name) = self.get_ty_from_var(&src) {
                    let entry = self.type_table.entries.get(&name).unwrap();

                    let tmp_src_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    let src = asm::PVal::Var(src);
                    instructions.push(asm::Instr::Lea {
                        src,
                        dst: asm::PVal::Var(tmp_src_ptr.clone())
                    });
                    instructions.push(asm::Instr::Binary {
                        binop: asm::Binop::Add,
                        src1: asm::PVal::Var(tmp_src_ptr.clone()),
                        src2: asm::PVal::Imm(offset as i32),
                        dst: asm::PVal::Var(tmp_src_ptr.clone())
                    });

                    let tmp_dst_ptr = self.make_tmp_var(mir_def::Type::Pointer(Box::new(mir_def::Type::Char)));
                    instructions.push(asm::Instr::Lea {
                        src: asm::PVal::Var(dst),
                        dst: asm::PVal::Var(tmp_dst_ptr.clone())
                    });

                    self.copy_bytes(tmp_src_ptr, tmp_dst_ptr, entry.size, instructions);

                    return;
                }

                instructions.push(asm::Instr::Lea { src: asm::PVal::Var(dst), dst: asm::Reg::pval(7) });
                instructions.push(asm::Instr::LLod {
                    src: asm::PVal::Var(src),
                    offset: asm::PVal::Imm(offset as i32),
                    dst: asm::Reg::pval(7),
                });
            }
        }
    }

    fn term_to_asm(&self, term: mir_def::Terminator, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
        match term {
            mir_def::Terminator::Return(val) => {
                val.map(|val| {
                    let val = self.val_to_asm(val, instructions);

                    instructions.push(asm::Instr::Mov { src: val, dst: asm::Reg::pval(1) });
                });
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
                mir_def::Const::Char(n) |
                mir_def::Const::Int(n) => n as i32,
                mir_def::Const::UChar(n) |
                mir_def::Const::UInt(n) => n as i32,

                mir_def::Const::EnumItem { .. } => unreachable!()
            }),
            mir_def::Val::Var(v) => asm::PVal::Var(v)
        }
    }

    fn copy_bytes(&self, src: Ident, dst: Ident, size: u16, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
        let src = asm::PVal::Var(src);
        let dst = asm::PVal::Var(dst);
        
        (0..size).for_each(|_| {
            instructions.push(asm::Instr::Cpy {
                src: src.clone(),
                dst: dst.clone()
            });

            instructions.push(asm::Instr::Binary {
                binop: asm::Binop::Add,
                src1: src.clone(),
                src2: asm::PVal::Imm(1),
                dst: src.clone()
            });
            instructions.push(asm::Instr::Binary {
                binop: asm::Binop::Add,
                src1: dst.clone(),
                src2: asm::PVal::Imm(1),
                dst: dst.clone()
            });
        });
    }
}