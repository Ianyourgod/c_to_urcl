use crate::ast::*;

mod name_analysis;
mod loop_label;

pub fn analyse(program: Program) -> Program {
    let na = name_analysis::Analyzer::new();
    let mut ast = na.analyze(program);
    let mut ll = loop_label::LoopLabeler::new();
    ll.label(&mut ast);

    ast
}