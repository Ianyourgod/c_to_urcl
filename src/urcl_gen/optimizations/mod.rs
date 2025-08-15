use crate::urcl_gen::{asm, cpu_definitions::CPUDefinition};

mod label_replace;

pub fn optimize<CPU: CPUDefinition>(program: asm::Program<asm::Val, CPU>) -> asm::Program<asm::Val, CPU> {
    asm::Program {
        cpu: program.cpu,
        top_level_items: program.top_level_items.into_iter().map(|tl| {
            match tl {
                asm::TopLevel::Fn(func) => asm::TopLevel::Fn(optimize_fn(func)),
                _ => tl
            }
        }).collect()
    }
}

fn optimize_fn(func: asm::Function<asm::Val>) -> asm::Function<asm::Val> {
    let mut func = func;

    loop {
        let prev_fn = func.clone();

        func = label_replace::run(func);

        if func == prev_fn {
            break func;
        }
    }
}