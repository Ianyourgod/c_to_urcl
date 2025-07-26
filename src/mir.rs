pub mod mir_def;
mod mir_gen;

use crate::ast;

pub fn generate_mir(ast: ast::Program) -> mir_def::Program {
    let mut generator = mir_gen::Generator::new();

    generator.generate(ast)
}