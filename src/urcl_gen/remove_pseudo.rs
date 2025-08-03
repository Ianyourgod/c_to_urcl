use std::collections::HashMap;

use crate::semantic_analysis::type_check::{IdentifierAttrs, SymbolTable};
use crate::urcl_gen::asm;
use crate::mir::mir_def::Ident;

pub fn fix_pvals(program: asm::Program<asm::PVal>, symbol_table: &SymbolTable) -> asm::Program<asm::Val> {
    let mut r = RemovePseudo::new(symbol_table);

    r.generate_program(program)
}

#[derive(Debug, Clone)]
enum VarPosition {
    Label(Ident),
    Stack(u32),
}

#[derive(Debug, Clone)]
struct RemovePseudo<'a> {
    vars: HashMap<Ident, VarPosition>,
    stack_offset: u32,
    symbol_table: &'a SymbolTable
}

impl<'a> RemovePseudo<'a> {
    pub fn new(symbol_table: &'a SymbolTable) -> Self {
        Self {
            vars: HashMap::new(),
            stack_offset: 0,
            symbol_table,
        }
    }

    pub fn generate_program(&mut self, program: asm::Program<asm::PVal>) -> asm::Program<asm::Val> {
        asm::Program {
            header_info: program.header_info,
            top_level_items: program.top_level_items.into_iter().map(|f| {
                match f {
                    asm::TopLevel::Fn(f) => asm::TopLevel::Fn(self.generate_function(f)),
                    asm::TopLevel::StaticVar { name, global, init } => asm::TopLevel::StaticVar { name, global, init }
                }
            }).collect()
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
                let offset = self.convert_pval_src(offset, PVAL_SRC1, instructions);
                let src = self.convert_pval_src(src, PVAL_SRC2, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, PVAL_DST);

                instructions.push(asm::Instr::LLod { src, dst, offset });

                if let Some(idx) = idx { self.pval_dst_write(PVAL_DST, idx, instructions); }
            },
            asm::Instr::LStr { src, dst, offset } => {
                let offset = self.convert_pval_src(offset, PVAL_SRC2, instructions);
                let src = self.convert_pval_src(src, PVAL_SRC1, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, PVAL_DST);

                instructions.push(asm::Instr::LStr { src, dst, offset });

                if let Some(idx) = idx { self.pval_dst_write(PVAL_DST, idx, instructions); }
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
            asm::Instr::Lea { src, dst } => {
                let (dst, idx) = self.convert_pval_dst(dst, PVAL_DST);

                match src {
                    asm::PVal::Imm(_) |
                    asm::PVal::Reg(_) => unreachable!(),

                    asm::PVal::Label(l) => {
                        let src = asm::Val::Label(l);
                        instructions.push(asm::Instr::Mov { src, dst });
                    },
                    asm::PVal::Var(v) => {
                        let entry = self.symbol_table.get(&v).unwrap();

                        match entry.attrs {
                            IdentifierAttrs::Fn { .. } => unreachable!(),

                            IdentifierAttrs::Local => {
                                let v = if let VarPosition::Stack(s) = self.vars.get(&v).unwrap() { *s } else { unreachable!() };

                                instructions.push(asm::Instr::Binary { binop: asm::Binop::Add, src1: asm::Reg::val(2), src2: asm::Val::Imm(v as i32), dst });
                            },
                            IdentifierAttrs::Static { .. } => {
                                let src = asm::Val::Label(v);
                                instructions.push(asm::Instr::Mov { src, dst });
                            }
                        }
                    }
                }

                if let Some(idx) = idx { self.pval_dst_write(PVAL_DST, idx, instructions); }
            }

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
            asm::PVal::Label(l) => asm::Val::Label(l),
            asm::PVal::Var(v) => {
                let v = self.vars.entry(v.clone()).or_insert_with(|| {
                    let entry = self.symbol_table.get(&v).unwrap();

                    match entry.attrs {
                        IdentifierAttrs::Static { .. } => {
                            VarPosition::Label(v)
                        }
                        IdentifierAttrs::Fn { .. } |
                        IdentifierAttrs::Local => unreachable!()
                    }
                });

                match v {
                    VarPosition::Stack(n) => {
                        instructions.push(asm::Instr::LLod { src: asm::Reg::val(2), dst: asm::Reg::val(load_to), offset: asm::Val::Imm(*n as i32) });
                    },
                    VarPosition::Label(l) => {
                        instructions.push(asm::Instr::LLod { src: asm::Val::Label(l.clone()), dst: asm::Reg::val(load_to), offset: asm::Val::Imm(0) });
                    }
                }

                asm::Reg::val(load_to)
            }
        }
    }

    fn convert_pval_dst(&mut self, pval: asm::PVal, write_to: u8) -> (asm::Val, Option<VarPosition>) {
        (match pval {
            asm::PVal::Imm(n) => asm::Val::Imm(n),
            asm::PVal::Reg(r) => asm::Val::Reg(r),
            asm::PVal::Label(l) => asm::Val::Label(l),
            asm::PVal::Var(v) => {
                let v = self.vars.entry(v.clone()).or_insert_with(|| {
                    let entry = self.symbol_table.get(&v).unwrap();

                    match entry.attrs {
                        IdentifierAttrs::Local => {
                            self.stack_offset += 1;
                            VarPosition::Stack(self.stack_offset)
                        },
                        IdentifierAttrs::Static { .. } => {
                            VarPosition::Label(v)
                        }
                        IdentifierAttrs::Fn { .. } => unreachable!()
                    }
                });

                return (asm::Reg::val(write_to), Some(v.clone()));
            },
        }, None)
    }

    fn pval_dst_write(&mut self, written_to: u8, idx: VarPosition, instructions: &mut Vec<asm::Instr<asm::Val>>) {
        match idx {
            VarPosition::Label(l) => {
                instructions.push(asm::Instr::LStr {
                    src: asm::Reg::val(written_to),
                    dst: asm::Val::Label(l),
                    offset: asm::Val::Imm(0)
                });
            },
            VarPosition::Stack(n) => {
                instructions.push(asm::Instr::LStr {
                    src: asm::Reg::val(written_to),
                    dst: asm::Reg::val(2),
                    offset: asm::Val::Imm(n as i32)
                });
            }
        }
        
    }
}