use crate::{mir::mir_def, semantic_analysis::type_check::SymbolTable, Ident};

pub fn fold_program(mir: mir_def::Program, symbol_table: &SymbolTable) -> mir_def::Program {
    let folder = Folder::new(symbol_table);

    folder.fold_program(mir)
}

pub struct Folder<'a> {
    symbol_table: &'a SymbolTable 
}

impl<'a> Folder<'a> {
    pub fn new(symbol_table: &'a SymbolTable) -> Self {
        Self {
            symbol_table
        }
    }

    pub fn fold_program(&self, mir: mir_def::Program) -> mir_def::Program {
        mir_def::Program {
            top_level: mir.top_level.into_iter().map(|tl| {
                match tl {
                    mir_def::TopLevel::Var(_) |
                    mir_def::TopLevel::Const { .. } => tl,

                    mir_def::TopLevel::Fn(func) => {
                        mir_def::TopLevel::Fn(self.fold_function(func))
                    }
                }
            }).collect()
        }
    }

    fn fold_function(&self, func: mir_def::Function) -> mir_def::Function {
        mir_def::Function {
            name: func.name,
            global: func.global,
            params: func.params,
            basic_blocks: mir_def::CFG {
                blocks: func.basic_blocks.blocks.into_iter().map(|block| {
                    (block.0, self.fold_block(block.1))
                }).collect()
            }
        }
    }

    fn fold_block(&self, block: mir_def::BasicBlock) -> mir_def::BasicBlock {
        match block {
            mir_def::BasicBlock::End |
            mir_def::BasicBlock::Start { .. } => block,

            mir_def::BasicBlock::Generic(block) => {
                mir_def::BasicBlock::Generic(mir_def::GenericBlock {
                    id: block.id,
                    instructions: block.instructions.into_iter().map(|i|self.fold_instr(i)).collect(),
                    terminator: self.fold_terminator(block.terminator)
                })
            }
        }
    }

    fn fold_instr(&self, instr: mir_def::Instruction) -> mir_def::Instruction {
        match instr {
            mir_def::Instruction::Binary { op, src1, src2, dst } => {
                if let Some(src1) = self.is_const(&src1) && let Some(src2) = self.is_const(&src2) {
                    mir_def::Instruction::Copy {
                        src: mir_def::Val::Num(match op {
                            mir_def::Binop::Add => src1.add(src2),
                            mir_def::Binop::Sub => src1.sub(src2),
                            mir_def::Binop::Mul => src1.mul(src2),
                            mir_def::Binop::Div => src1.div(src2),
                            mir_def::Binop::Mod => src1.modulus(src2),
                            mir_def::Binop::BitwiseAnd => src1.bitwise_and(src2),
                            mir_def::Binop::BitwiseOr => src1.bitwise_or(src2),
                            mir_def::Binop::BitwiseXor => src1.bitwise_xor(src2),
                            mir_def::Binop::LeftShift => src1.shift_left(src2),
                            mir_def::Binop::RightShift => src1.shift_right(src2),
                            mir_def::Binop::GreaterThan => self.bool_to_int(src1.greater_than(src2)),
                            mir_def::Binop::LessThan => self.bool_to_int(src1.less_than(src2)),
                            mir_def::Binop::GreaterEqual => self.bool_to_int(!src1.less_than(src2)),
                            mir_def::Binop::LessEqual => self.bool_to_int(!src1.greater_than(src2)),
                            mir_def::Binop::Equal => self.bool_to_int(src1.equals(src2)),
                            mir_def::Binop::NotEqual => self.bool_to_int(!src1.equals(src2)),
                        }),
                        dst
                    }
                } else {
                    mir_def::Instruction::Binary {
                        op,
                        src1,
                        src2,
                        dst
                    }
                }
            },
            mir_def::Instruction::Unary { op, inner, dst } => {
                if let Some(src) = self.is_const(&inner) {
                    mir_def::Instruction::Copy {
                        src: mir_def::Val::Num(match op {
                            mir_def::Unop::Complement => src.complement(),
                            mir_def::Unop::Negate => src.negate()
                        }),
                        dst
                    }
                } else {
                    mir_def::Instruction::Unary {
                        op,
                        inner,
                        dst
                    }
                }
            },
            mir_def::Instruction::Copy { src, dst } => {
                if let Some(src) = self.is_const(&src) {
                    let src_ty = src.to_type();
                    let dst_ty = self.var_ty(&dst);

                    if src_ty != dst_ty {
                        return mir_def::Instruction::Copy {
                            src: mir_def::Val::Num(mir_def::Const::from_type(src.as_i32(), &dst_ty)),
                            dst
                        };
                    }
                }

                mir_def::Instruction::Copy { src, dst }
            },

            mir_def::Instruction::AddPtr { .. } |
            mir_def::Instruction::CopyFromOffset { .. } |
            mir_def::Instruction::CopyToOffset { .. } |
            mir_def::Instruction::FunctionCall { .. } |
            mir_def::Instruction::GetAddress { .. } |
            mir_def::Instruction::Load { .. } |
            mir_def::Instruction::Store { .. } => instr 
        }
    }

    fn var_ty(&self, var: &Ident) -> mir_def::Type {
        self.symbol_table.get(var).unwrap().ty.clone()
    }

    fn fold_terminator(&self, term: mir_def::Terminator) -> mir_def::Terminator {
        match term {
            mir_def::Terminator::Return(_) |
            mir_def::Terminator::Jump { .. } => term,

            mir_def::Terminator::JumpCond { target, fail, src1, src2, cond } => {
                let s1_c = self.is_const(&src1);
                let s2_c = self.is_const(&src2);

                if let Some(src1) = s1_c && let Some(src2) = s2_c {
                    mir_def::Terminator::Jump { target: if self.evaluate_cond(cond, src1, src2) {
                        target
                    } else {
                        fail
                    }}
                } else {
                    mir_def::Terminator::JumpCond {
                        target,
                        fail,
                        src1,
                        src2,
                        cond
                    }
                }
            }
        }
    }

    fn is_const(&self, val: &mir_def::Val) -> Option<mir_def::Const> {
        match val {
            mir_def::Val::Var(_) => None,
            mir_def::Val::Num(c) => Some(c.clone())
        }
    }

    fn evaluate_cond(&self, cond: mir_def::Cond, src1: mir_def::Const, src2: mir_def::Const) -> bool {
        match cond {
            mir_def::Cond::Equal => src1.equals(src2),
            mir_def::Cond::NotEqual => !src1.equals(src2),
            mir_def::Cond::GreaterThan => src1.greater_than(src2),
            mir_def::Cond::LessThan => src1.less_than(src2),
            mir_def::Cond::LessThanEqual => !src1.greater_than(src2),
            mir_def::Cond::GreaterThanEqual => !src1.less_than(src2),
        }
    }

    #[inline]
    fn bool_to_int(&self, b: bool) -> mir_def::Const {
        if b { mir_def::Const::Int(1) } else { mir_def::Const::Int(0) }
    }
}