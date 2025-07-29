use std::collections::{HashSet, VecDeque};

use crate::urcl_gen::asm;
use crate::mir::mir_def;

pub fn mir_to_asm(mir: mir_def::Program) -> asm::Program<asm::PVal> {
    asm::Program {
        header_info: asm::HeaderInfo::iris(),
        functions: mir.functions.into_iter().map(|func| {
            let mut instructions = Vec::new();

            cfg_to_asm(func.basic_blocks, &mut instructions);
            
            asm::Function {
                name: func.name,
                instructions
            }
        }).collect()
    }
}

fn cfg_to_asm(cfg: mir_def::CFG, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
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

        block_to_asm(block.clone(), instructions);
    }
}

fn block_to_asm(block: mir_def::BasicBlock, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
    let block = if let mir_def::BasicBlock::Generic(block) = block {
        block
    } else { return; };

    instructions.push(asm::Instr::Label(block.id));

    block.instructions.into_iter().for_each(|i|instr_to_asm(i, instructions));
    term_to_asm(block.terminator, instructions);
}

fn instr_to_asm(instr: mir_def::Instruction, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
    match instr {
        mir_def::Instruction::Binary { op, src1, src2, dst } => {
            let (binop, needs_bit_select) = match op {
                mir_def::Binop::Add => (asm::Binop::Add, false),
                mir_def::Binop::Sub => (asm::Binop::Sub, false),
                mir_def::Binop::Mul => (asm::Binop::Mul, false),
                mir_def::Binop::Div => (asm::Binop::SDiv, false),
                mir_def::Binop::Mod => (asm::Binop::Mod, false),
                mir_def::Binop::BitwiseAnd => (asm::Binop::And, false),
                mir_def::Binop::BitwiseOr => (asm::Binop::Or, false),
                mir_def::Binop::BitwiseXor => (asm::Binop::Xor, false),
                mir_def::Binop::LeftShift => (asm::Binop::LeftShift, false),
                mir_def::Binop::RightShift => (asm::Binop::RightShift, false),

                mir_def::Binop::Equal => (asm::Binop::Set(asm::Cond::Equal), true),
                mir_def::Binop::NotEqual => (asm::Binop::Set(asm::Cond::NotEqual), true),
                mir_def::Binop::LessThan => (asm::Binop::Set(asm::Cond::SLessThan), true),
                mir_def::Binop::LessEqual => (asm::Binop::Set(asm::Cond::SLessEqual), true),
                mir_def::Binop::GreaterThan => (asm::Binop::Set(asm::Cond::SGreaterThan), true),
                mir_def::Binop::GreaterEqual => (asm::Binop::Set(asm::Cond::SGreaterEqual), true),
            };

            let src1 = val_to_asm(src1, instructions);
            let src2 = val_to_asm(src2, instructions);

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

            let src = val_to_asm(inner, instructions);

            instructions.push(asm::Instr::Unary { unop, src, dst: asm::PVal::Var(dst) });
        },
        mir_def::Instruction::Copy { src, dst } => {
            let src = val_to_asm(src, instructions);
            instructions.push(
                asm::Instr::Mov { src, dst: asm::PVal::Var(dst) }
            );
        }
    }
}

fn term_to_asm(term: mir_def::Terminator, instructions: &mut Vec<asm::Instr<asm::PVal>>) {
    match term {
        mir_def::Terminator::Return(val) => {
            let val = val_to_asm(val, instructions);

            instructions.push(asm::Instr::Mov { src: val, dst: asm::Reg::pval(1) });
            instructions.push(asm::Instr::Ret);
        },
        mir_def::Terminator::Jump { target } => {
            instructions.push(asm::Instr::Jmp { label: target })
        },
        mir_def::Terminator::JumpCond { target, fail, src1, src2, cond } => {
            let src1 = val_to_asm(src1, instructions);
            let src2 = val_to_asm(src2, instructions);

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

fn val_to_asm(val: mir_def::Val, _instructions: &mut Vec<asm::Instr<asm::PVal>>) -> asm::PVal {
    match val {
        mir_def::Val::Num(n) => asm::PVal::Imm(n),
        mir_def::Val::Var(v) => asm::PVal::Var(v)
    }
}