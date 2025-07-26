pub mod asm;
mod convert;
mod remove_pseudo;

use crate::mir::mir_def;

pub fn mir_to_asm(mir: mir_def::Program) -> asm::Program<asm::Val> {
    let inital = convert::mir_to_asm(mir);
    let no_pvals = remove_pseudo::fix_pvals(inital);

    no_pvals
}