use std::collections::HashMap;

use crate::semantic_analysis::type_check::{IdentifierAttrs, SymbolTable, TypeTable};
use crate::urcl_gen::{asm, cpu_definitions::CPUDefinition};
use crate::mir::mir_def::Ident;

pub fn fix_pvals<'a, T:CPUDefinition>(program: asm::Program<'a, asm::PVal, T>, symbol_table: &'a SymbolTable, type_table: &'a TypeTable, cpu: &'a T) -> (asm::Program<'a, asm::Val, T>, HashMap<asm::Ident, u64>) {
    let r = RemovePseudo::new(symbol_table, type_table, cpu);

    r.generate_program(program)
}

#[derive(Debug, Clone)]
enum VarPosition {
    Label(Ident),
    Stack(u64),
}

struct RemovePseudo<'a, T: CPUDefinition> {
    vars: HashMap<Ident, VarPosition>,
    stack_offset: u64,
    symbol_table: &'a SymbolTable,
    type_table: &'a TypeTable,
    cpu: &'a T
}

impl<'a, T: CPUDefinition> RemovePseudo<'a, T> {
    pub fn new(symbol_table: &'a SymbolTable, type_table: &'a TypeTable, cpu: &'a T) -> Self {
        Self {
            vars: HashMap::new(),
            stack_offset: 0,
            symbol_table,
            type_table,
            cpu,
        }
    }

    pub fn generate_program(mut self, program: asm::Program<asm::PVal, T>) -> (asm::Program<asm::Val, T>, HashMap<asm::Ident, u64>) {
        let mut stack_offsets = HashMap::new();
        
        let prog = asm::Program {
            cpu: program.cpu,
            top_level_items: program.top_level_items.into_iter().map(|f| {
                match f {
                    asm::TopLevel::Fn(f) => {
                        let name = f.name.clone();

                        let r = asm::TopLevel::Fn(self.generate_function(f));

                        stack_offsets.insert(name, self.stack_offset);

                        r
                    },
                    asm::TopLevel::StaticVar { name, global, init } => asm::TopLevel::StaticVar { name, global, init },
                    asm::TopLevel::StaticConst { name, init } => asm::TopLevel::StaticConst { name, init }
                }
            }).collect()
        };

        (prog, stack_offsets)
    }

    fn generate_function(&mut self, function: asm::Function<asm::PVal>) -> asm::Function<asm::Val> {
        self.stack_offset = 0;
        
        let mut instructions = Vec::with_capacity(function.instructions.len());

        function.instructions.into_iter().for_each(|i|self.generate_instruction(i, &mut instructions));

        asm::Function {
            name: function.name,
            instructions
        }
    }

    fn generate_instruction(&mut self, instruction: asm::Instr<asm::PVal>, instructions: &mut Vec<asm::Instr<asm::Val>>) {
        let tmp_regs = self.cpu.get_temp_regs();
        let pval_src1 = tmp_regs.0;
        let pval_src2 = tmp_regs.1;
        let pval_src3 = tmp_regs.2;
        
        let pval_dst = self.cpu.get_temp_dst_reg();

        //instructions.push(asm::Instr::Comment(instruction.to_string()));
        
        match instruction {
            asm::Instr::Binary { binop, src1, src2, dst } => {
                let src1 = self.convert_pval_src(src1, pval_src1, instructions);
                let src2 = self.convert_pval_src(src2, pval_src2, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, pval_dst);

                instructions.push(asm::Instr::Binary { binop, src1, src2, dst });

                if let Some(idx) = idx { self.pval_dst_write(pval_dst, idx, instructions); }
            },
            asm::Instr::Unary { unop, src, dst } => {
                let src = self.convert_pval_src(src, pval_src1, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, pval_dst);

                instructions.push(asm::Instr::Unary { unop, src, dst });

                if let Some(idx) = idx { self.pval_dst_write(pval_dst, idx, instructions); }
            },
            asm::Instr::Mov { src, dst } => {
                let src = self.convert_pval_src(src, pval_src1, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, pval_dst);

                instructions.push(asm::Instr::Mov { src, dst });

                if let Some(idx) = idx { self.pval_dst_write(pval_dst, idx, instructions); }
            },
            asm::Instr::LLod { src, dst, offset } => {
                let offset = self.convert_pval_src(offset, pval_src1, instructions);
                let src = self.convert_pval_src(src, pval_src2, instructions);
                let (dst, idx) = self.convert_pval_dst(dst, pval_dst);

                instructions.push(asm::Instr::LLod { src, dst, offset });

                if let Some(idx) = idx { self.pval_dst_write(pval_dst, idx, instructions); }
            },
            asm::Instr::LStr { src, dst, offset } => {
                let offset = self.convert_pval_src(offset, pval_src2, instructions);
                let src = self.convert_pval_src(src, pval_src1, instructions);
                let dst = self.convert_pval_src(dst, pval_src3, instructions);

                //println!("STR {:?} -> {:?} {:?}", src, dst, offset);
                instructions.push(asm::Instr::LStr { src, dst, offset });
            },
            asm::Instr::Push(src) => {
                let src = self.convert_pval_src(src, pval_src1, instructions);

                instructions.push(asm::Instr::Push(src))
            },
            asm::Instr::Branch { label, src1, src2, cond } => {
                let src1 = self.convert_pval_src(src1, pval_src1, instructions);
                let src2 = self.convert_pval_src(src2, pval_src2, instructions);

                instructions.push(asm::Instr::Branch { label, src1, src2, cond })
            }
            asm::Instr::Pop(dst) => {
                let (dst, idx) = self.convert_pval_dst(dst, pval_dst);

                instructions.push(asm::Instr::Pop(dst));

                if let Some(idx) = idx { self.pval_dst_write(pval_dst, idx, instructions); }
            },
            asm::Instr::Lea { src, dst } => {
                let (dst, idx) = self.convert_pval_dst(dst, pval_dst);

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
                                let v = if let VarPosition::Stack(s) = self.get_var_pos(v) { s } else { unreachable!() };

                                instructions.push(asm::Instr::Binary { binop: asm::Binop::Sub, src1: asm::Reg::bp_val(self.cpu), src2: asm::Val::Imm(v as i32), dst });
                            },
                            IdentifierAttrs::Constant { .. } |
                            IdentifierAttrs::Static { .. } => {
                                let src = asm::Val::Label(v);
                                instructions.push(asm::Instr::Mov { src, dst });
                            }
                        }
                    }
                }

                if let Some(idx) = idx { self.pval_dst_write(pval_dst, idx, instructions); }
            },
            asm::Instr::Cpy { src, dst } => {
                let src = self.convert_pval_src(src, pval_src1, instructions);
                let dst = self.convert_pval_src(dst, pval_src2, instructions);

                instructions.push(asm::Instr::Cpy {
                    src,
                    dst
                });
            }

            asm::Instr::Call(n) => instructions.push(asm::Instr::Call(n)),
            asm::Instr::Ret => instructions.push(asm::Instr::Ret),
            asm::Instr::Comment(c) => instructions.push(asm::Instr::Comment(c)),
            asm::Instr::Jmp { label } => instructions.push(asm::Instr::Jmp { label }),
            asm::Instr::Label(label) => instructions.push(asm::Instr::Label(label)),
        }
    }

    fn convert_pval_src(&mut self, pval: asm::PVal, load_to: asm::Reg, instructions: &mut Vec<asm::Instr<asm::Val>>) -> asm::Val {
        match pval {
            asm::PVal::Imm(n) => asm::Val::Imm(n),
            asm::PVal::Reg(r) => asm::Val::Reg(r),
            asm::PVal::Label(l) => asm::Val::Label(l),
            asm::PVal::Var(v) => {
                let v = self.vars.entry(v.clone()).or_insert_with(|| {
                    let entry = self.symbol_table.get(&v).unwrap();

                    match entry.attrs {
                        IdentifierAttrs::Constant { .. } |
                        IdentifierAttrs::Static { .. } => {
                            VarPosition::Label(v)
                        }
                        IdentifierAttrs::Fn { .. } |
                        IdentifierAttrs::Local => {
                            self.stack_offset += entry.ty.size(self.type_table) as u64;
                            VarPosition::Stack(self.stack_offset)
                        }
                    }
                });

                match v {
                    VarPosition::Stack(n) => {
                        instructions.push(asm::Instr::LLod { src: asm::Reg::bp_val(self.cpu), dst: asm::Val::Reg(load_to), offset: asm::Val::Imm(-(*n as i32)) });
                    },
                    VarPosition::Label(l) => {
                        // TODO! use normal lod instr
                        instructions.push(asm::Instr::LLod { src: asm::Val::Label(l.clone()), dst: asm::Val::Reg(load_to), offset: asm::Val::Imm(0) });
                    }
                }

                asm::Val::Reg(load_to)
            },
        }
    }

    fn convert_pval_dst(&mut self, pval: asm::PVal, write_to: asm::Reg) -> (asm::Val, Option<VarPosition>) {
        (match pval {
            asm::PVal::Imm(n) => asm::Val::Imm(n),
            asm::PVal::Reg(r) => asm::Val::Reg(r),
            asm::PVal::Label(l) => asm::Val::Label(l),
            asm::PVal::Var(v) => {
                let v = self.get_var_pos(v);

                return (asm::Val::Reg(write_to), Some(v));
            },
        }, None)
    }

    fn get_var_pos(&mut self, var: Ident) -> VarPosition {
        self.vars.entry(var.clone()).or_insert_with(|| {
            let entry = self.symbol_table.get(&var).unwrap();

            match entry.attrs {
                IdentifierAttrs::Local => {
                    self.stack_offset += entry.ty.size(self.type_table) as u64;
                    VarPosition::Stack(self.stack_offset)
                },
                IdentifierAttrs::Constant { .. } |
                IdentifierAttrs::Static { .. } => {
                    VarPosition::Label(var)
                },
                IdentifierAttrs::Fn { .. } => unreachable!()
            }
        }).clone()
    }

    fn pval_dst_write(&mut self, written_to: asm::Reg, idx: VarPosition, instructions: &mut Vec<asm::Instr<asm::Val>>) {
        match idx {
            VarPosition::Label(l) => {
                instructions.push(asm::Instr::LStr {
                    src: asm::Val::Reg(written_to),
                    dst: asm::Val::Label(l),
                    offset: asm::Val::Imm(0)
                });
            },
            VarPosition::Stack(n) => {
                instructions.push(asm::Instr::LStr {
                    src: asm::Val::Reg(written_to),
                    dst: asm::Reg::bp_val(self.cpu),
                    offset: asm::Val::Imm(-(n as i32))
                });
            }
        }
        
    }
}