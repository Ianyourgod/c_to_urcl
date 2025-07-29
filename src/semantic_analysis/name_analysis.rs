use std::collections::HashMap;
use std::rc::Rc;

use crate::Ident;

use crate::ast;

#[derive(Debug, Clone)]
pub struct Context {
    pub mappings: HashMap<Ident, ContextItem>
}

#[derive(Debug)]
pub struct ContextItem {
    pub ident: Ident,
    pub from_this_scope: bool,
}

impl Clone for ContextItem {
    fn clone(&self) -> Self {
        Self {
            ident: self.ident.clone(),
            from_this_scope: false
        }
    }
}

impl ContextItem {
    pub fn new(name: Ident) -> Self {
        Self {
            ident: name,
            from_this_scope: true,
        }
    }
}

pub struct Analyzer {
    pub tmp_count: u32
}

impl Analyzer {
    pub fn new() -> Self {
        Self { tmp_count: 0 }
    }

    pub fn analyze(mut self, program: ast::Program) -> ast::Program {
        let mut ctx = Context { mappings: HashMap::new() };

        ast::Program {
            functions: program.functions.into_iter().map(|f|self.analyze_function(f, &mut ctx)).collect()
        }
    }

    fn gen_new_ident(&mut self, old_ident: &Ident) -> Ident {
        self.tmp_count += 1;
        Rc::new(format!(".na.gen.{}.{}", old_ident, self.tmp_count))
    }

    fn analyze_function(&mut self, function: ast::FunctionDecl, context: &mut Context) -> ast::FunctionDecl {
        let global = true;
        let name = self.add_new_name(function.name, context, !global);

        ast::FunctionDecl {
            name,
            block: self.analyze_block(function.block, context)
        }
    }

    fn analyze_block(&mut self, block: ast::Block, context: &mut Context) -> ast::Block {
        let mut context = context.clone();
        ast::Block { statements: block.statements.into_iter().map(|stmt| {
            match stmt {
                ast::BlockItem::Declaration(decl) => {
                    ast::BlockItem::Declaration(self.analyze_var_decl(decl, &mut context))
                },
                ast::BlockItem::Statement(stmt) => {
                    ast::BlockItem::Statement(self.analyze_statement(stmt, &mut context))
                }
            }
        }).collect() }
    }

    fn add_new_name(&mut self, old_name: Ident, context: &mut Context, gen_new_name: bool) -> Ident {
        if let Some(item) = context.mappings.get(&old_name) && item.from_this_scope {
            panic!("Cannot redefine {old_name}");
        }

        let name = if gen_new_name {
            self.gen_new_ident(&old_name)
        } else {
            old_name.clone()
        };
        context.mappings.insert(old_name, ContextItem::new(name.clone()));
        name
    }

    fn analyze_var_decl(&mut self, var_decl: ast::VarDeclaration, context: &mut Context) -> ast::VarDeclaration {
        let name = self.add_new_name(var_decl.name, context, true);

        ast::VarDeclaration::new(name, var_decl.expr.map(|expr|self.analyze_expr(expr, context)))
    }

    fn analyze_statement(&mut self, statement: ast::Statement, context: &mut Context) -> ast::Statement {
        match statement {
            ast::Statement::Return(expr) => {
                ast::Statement::Return(self.analyze_expr(expr, context))
            },
            ast::Statement::Expr(expr) => {
                ast::Statement::Expr(self.analyze_expr(expr, context))
            },
            ast::Statement::If(cond, box (then, else_stmt)) => {
                let cond = self.analyze_expr(cond, context);

                let then = self.analyze_statement(then, context);
                let else_stmt = else_stmt.map(|e|self.analyze_statement(e, context));

                ast::Statement::If(cond, Box::new((then, else_stmt)))
            },
            ast::Statement::Block(block) => {
                ast::Statement::Block(self.analyze_block(block, context))
            }
        }
    }

    fn analyze_expr(&mut self, expr: ast::Expr, context: &mut Context) -> ast::Expr {
        match expr {
            ast::Expr::Binary(ast::BinOp::Assign(assign_type), box (var, val)) => {
                let var = self.analyze_expr(var, context);
                match var {
                    ast::Expr::Var(_) => (),
                    _ => panic!("Expected var, found {:?}", var)
                }

                let val = self.analyze_expr(val, context);

                ast::Expr::Binary(ast::BinOp::Assign(assign_type), Box::new((var, val)))
            },
            ast::Expr::Binary(op, box (l, r)) => {
                let l = self.analyze_expr(l, context);
                let r = self.analyze_expr(r, context);

                ast::Expr::Binary(op, Box::new((l,r)))
            },
            ast::Expr::Unary(op, box inner) => {
                let inner = self.analyze_expr(inner, context);

                ast::Expr::Unary(op, Box::new(inner))
            },
            ast::Expr::Var(name) => {
                let name = if let Some(n) = context.mappings.get(&name) {
                    n
                } else {
                    panic!("Unknown var: {name}");
                };

                ast::Expr::Var(name.ident.clone())
            },
            ast::Expr::Ternary(box (cond, l, r)) => {
                let cond = self.analyze_expr(cond, context);
                let l = self.analyze_expr(l, context);
                let r = self.analyze_expr(r, context);

                ast::Expr::Ternary(Box::new((cond, l, r)))
            },

            ast::Expr::Number(_) => expr,
        }
    }
}