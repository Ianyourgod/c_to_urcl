use std::collections::HashMap;

use crate::urcl_gen::asm;
use crate::mir::mir_def::Ident;

pub fn fix_pvals(program: asm::Program<asm::PVal>) -> asm::Program<asm::Val> {
    let mut r = RemovePseudo::new();

    r.generate_program(program)
}

#[derive(Debug, Clone)]
struct RemovePseudo {
    vars: HashMap<Ident, u32>,
    stack_offset: u32
}

impl RemovePseudo {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            stack_offset: 0,
        }
    }

    pub fn generate_program(&mut self, program: asm::Program<asm::PVal>) -> asm::Program<asm::Val> {
        asm::Program {
            header_info: program.header_info,
            functions: program.functions.into_iter().map(|f| self.generate_function(f)).collect()
        }
    }

    fn generate_function(&mut self, function: asm::Function<asm::PVal>) -> asm::Function<asm::Val> {
        self.stack_offset = 0;
        
        let mut instructions = Vec::with_capacity(function.instructions.len() + 5);

        instructions.push(asm::Instr::Push(asm::Reg::val(2)));
        instructions.push(asm::Instr::Mov { src: asm::Reg::val(3), dst: asm::Reg::val(2) });
        instructions.push(asm::Instr::Binary { binop: asm::Binop::Add, src1: asm::Reg::val(3), src2: asm::Val::Imm(0), dst: asm::Reg::val(3) });

        function.instructions.into_iter().for_each(|i|self.generate_instruction(i, &mut instructions));

        *instructions.get_mut(2).unwrap() =
            asm::Instr::Binary {
                binop: asm::Binop::Add,
                src1: asm::Reg::val(3),
                src2: asm::Val::Imm(self.stack_offset as i32),
                dst: asm::Reg::val(3)
            };

        asm::Function {
            name: function.name,
            instructions
        }
    }

    fn generate_instruction(&mut self, instruction: asm::Instr<asm::PVal>, instructions: &mut Vec<asm::Instr<asm::Val>>) {
        const PVAL_DST: u8 = 7;
        const PVAL_SRC1: u8 = 7;
        const PVAL_SRC2: u8 = 8;
        
        match instruction {
            asm::Instr::Binary { binop, src1, src2, dst } => {
                let src1 = self.convert_pval_src(src1, PVAL_SRC1, instructions);
                let src2 = self.convert_pval_src(src2, PVAL_SRC2, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, PVAL_DST);

                instructions.push(asm::Instr::Binary { binop, src1, src2, dst });

                if let Some(idx) = idx { self.pval_dst_write(PVAL_DST, idx, instructions); }
            },
            asm::Instr::Unary { unop, src, dst } => {
                let src = self.convert_pval_src(src, PVAL_SRC1, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, PVAL_DST);

                instructions.push(asm::Instr::Unary { unop, src, dst });

                if let Some(idx) = idx { self.pval_dst_write(PVAL_DST, idx, instructions); }
            },
            asm::Instr::Mov { src, dst } => {
                let src = self.convert_pval_src(src, PVAL_SRC1, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, PVAL_DST);

                instructions.push(asm::Instr::Mov { src, dst });

                if let Some(idx) = idx { self.pval_dst_write(PVAL_DST, idx, instructions); }
            },
            asm::Instr::LLod { src, dst, offset } => {
                let offset = self.convert_pval_src(offset, 7, instructions);
                instructions.push(asm::Instr::LLod { src, dst, offset })
            },
            asm::Instr::LStr { src, dst, offset } => {
                let offset = self.convert_pval_src(offset, 7, instructions);
                let src = self.convert_pval_src(src, PVAL_SRC1, instructions);

                instructions.push(asm::Instr::LStr { src, dst, offset })
            },
            asm::Instr::Push(src) => {
                let src = self.convert_pval_src(src, PVAL_SRC1, instructions);

                instructions.push(asm::Instr::Push(src))
            },
            asm::Instr::Branch { label, src1, src2, cond } => {
                let src1 = self.convert_pval_src(src1, 7, instructions);
                let src2 = self.convert_pval_src(src2, 8, instructions);

                instructions.push(asm::Instr::Branch { label, src1, src2, cond })
            }
            asm::Instr::Pop(dst) => {
                let (dst, idx) = self.convert_pval_dst(dst, PVAL_DST);

                instructions.push(asm::Instr::Pop(dst));

                if let Some(idx) = idx { self.pval_dst_write(PVAL_DST, idx, instructions); }
            },

            asm::Instr::Call(n) => instructions.push(asm::Instr::Call(n)),
            asm::Instr::Ret => {
                instructions.push(asm::Instr::Mov { src: asm::Reg::val(2), dst: asm::Reg::val(3) });
                instructions.push(asm::Instr::Pop(asm::Reg::val(2)));
                instructions.push(asm::Instr::Ret)
            },
            asm::Instr::Jmp { label } => instructions.push(asm::Instr::Jmp { label }),
            asm::Instr::Label(label) => instructions.push(asm::Instr::Label(label)),
        }
    }

    fn convert_pval_src(&mut self, pval: asm::PVal, load_to: u8, instructions: &mut Vec<asm::Instr<asm::Val>>) -> asm::Val {
        match pval {
            asm::PVal::Imm(n) => asm::Val::Imm(n),
            asm::PVal::Reg(r) => asm::Val::Reg(r),
            asm::PVal::Var(v) => {
                let v = *self.vars.entry(v).or_insert_with(|| {
                    self.stack_offset += 1;
                    self.stack_offset
                }) as i32;

                // now we need to lod it
                instructions.push(asm::Instr::LLod { src: asm::Reg::new(2), dst: asm::Reg::new(load_to), offset: asm::Val::Imm(v) });

                asm::Reg::val(load_to)
            }
        }
    }

    fn convert_pval_dst(&mut self, pval: asm::PVal, write_to: u8) -> (asm::Val, Option<i32>) {
        (match pval {
            asm::PVal::Imm(n) => asm::Val::Imm(n),
            asm::PVal::Reg(r) => asm::Val::Reg(r),
            asm::PVal::Var(v) => {
                let v = *self.vars.entry(v).or_insert_with(|| {
                    self.stack_offset += 1;
                    self.stack_offset
                }) as i32;

                return (asm::Reg::val(write_to), Some(v));
            }
        }, None)
    }

    fn pval_dst_write(&mut self, written_to: u8, idx: i32, instructions: &mut Vec<asm::Instr<asm::Val>>) {
        instructions.push(asm::Instr::LStr {
            src: asm::Reg::val(written_to),
            dst: asm::Reg::new(2),
            offset: asm::Val::Imm(idx)
        });
    }
}