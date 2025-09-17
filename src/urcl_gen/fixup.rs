use std::collections::{HashMap, HashSet};

use crate::urcl_gen::{asm, cpu_definitions::CPUDefinition};

type CalleeSaved = HashMap<asm::Ident, HashSet<asm::Reg>>;
type StackOffsets = HashMap<asm::Ident, u64>;

pub fn fix<'a, CPU: CPUDefinition>(program: asm::Program<'a, asm::Val, CPU>, callee_saved: CalleeSaved, stack_offsets: StackOffsets, cpu: &'a CPU) -> asm::Program<'a, asm::Val, CPU> {
    let fixer_upper = FixerUpper::new(callee_saved, stack_offsets, cpu);

    fixer_upper.fix(program)
}

struct FixerUpper<'a, CPU: CPUDefinition> {
    callee_saved: CalleeSaved,
    stack_offsets: StackOffsets,
    cpu: &'a CPU,
}

impl<'a, CPU: CPUDefinition> FixerUpper<'a, CPU> {
    pub fn new(callee_saved: CalleeSaved, stack_offsets: StackOffsets, cpu: &'a CPU) -> Self {
        Self {
            callee_saved,
            stack_offsets,
            cpu
        }
    }

    pub fn fix(&self, mut program: asm::Program<'a, asm::Val, CPU>) -> asm::Program<'a, asm::Val, CPU> {
        let mut tl = program.top_level_items.into_iter().map(|tl| {
            match tl {
                asm::TopLevel::Fn(func) => {
                    asm::TopLevel::Fn(self.fix_fn(func))
                },
                _ => tl
            }
        }).collect::<Vec<_>>();

        tl.sort_by(|a,b| {
            let a_is_fn = matches!(a, asm::TopLevel::Fn(_));
            let b_is_fn = matches!(b, asm::TopLevel::Fn(_));

            b_is_fn.cmp(&a_is_fn)
        });

        program.top_level_items = tl;

        program
    }

    fn fix_fn(&self, mut func: asm::Function<asm::Val>) -> asm::Function<asm::Val> {
        let stack_offset = *self.stack_offsets.get(&func.name).unwrap();

        let mut instructions = Vec::with_capacity(func.instructions.len() + if stack_offset == 0 { 0 } else { 5 });

        let callee_saved = self.callee_saved.get(&func.name).unwrap();

        let include_sf = stack_offset > 0 || callee_saved.len() > 0;

        if include_sf {
            instructions.push(asm::Instr::Push(asm::Reg::bp_val(self.cpu)));
            instructions.push(asm::Instr::Mov { src: asm::Reg::sp_val(), dst: asm::Reg::bp_val(self.cpu) });
            // placeholder
            instructions.push(asm::Instr::Binary { binop: asm::Binop::Sub, src1: asm::Reg::sp_val(), src2: asm::Val::Imm(stack_offset as i32), dst: asm::Reg::sp_val() });
        }

        for reg in callee_saved {
            instructions.push(asm::Instr::Push(asm::Val::Reg(*reg)));
        }

        func.instructions.into_iter().for_each(|instr|self.fix_instr(instr, &mut instructions, include_sf, callee_saved));

        func.instructions = instructions;

        func
    }

    /*
    ret:
    instructions.push(asm::Instr::Mov { src: asm::Reg::bp_val(self.cpu), dst: asm::Reg::sp_val() });
    instructions.push(asm::Instr::Pop(asm::Reg::bp_val(self.cpu)));
     */

    fn fix_instr(&self, instr: asm::Instr<asm::Val>, instructions: &mut Vec<asm::Instr<asm::Val>>, include_sf: bool, callee_saved: &HashSet<asm::Reg>) {
        match instr {
            asm::Instr::Ret => {
                for reg in callee_saved {
                    instructions.push(asm::Instr::Pop(asm::Val::Reg(*reg)));
                }

                if include_sf {
                    instructions.push(asm::Instr::Mov { src: asm::Reg::bp_val(self.cpu), dst: asm::Reg::sp_val() });
                    instructions.push(asm::Instr::Pop(asm::Reg::bp_val(self.cpu)));
                }
                instructions.push(asm::Instr::Ret);
            },
            _ => instructions.push(instr)
        }
    }
}