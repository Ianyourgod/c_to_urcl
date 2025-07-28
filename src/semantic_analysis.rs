use crate::ast::*;

mod name_analysis;

pub fn analyse(program: Program) -> Program {
    let na = name_analysis::Analyzer::new();
    na.analyze(program)
}