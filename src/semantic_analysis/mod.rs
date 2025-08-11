use crate::ast::*;

mod name_analysis;
mod loop_label;
pub mod type_check;

pub fn analyse(program: Program<Expr>) -> (Program<TypedExpr>, type_check::SymbolTable, type_check::TypeTable, type_check::SwitchCases) {
    let na = name_analysis::Analyzer::new();
    let mut ast = na.analyze(program);

    let mut ll = loop_label::LoopLabeler::new();
    ll.label(&mut ast);

    let tc = type_check::TypeChecker::new();
    
    tc.typecheck(ast)
}