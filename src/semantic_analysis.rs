use crate::ast::*;

mod name_analysis;
mod loop_label;
mod type_check;

pub fn analyse(program: Program) -> Program {
    let na = name_analysis::Analyzer::new();
    let mut ast = na.analyze(program);

    let mut ll = loop_label::LoopLabeler::new();
    ll.label(&mut ast);

    let tc = type_check::TypeChecker::new();
    let (ast, _symbol_table) = tc.typecheck(ast);

    ast
}