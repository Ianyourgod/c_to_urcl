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
    pub has_linkage: bool,
}

impl Clone for ContextItem {
    fn clone(&self) -> Self {
        Self {
            ident: self.ident.clone(),
            from_this_scope: false,
            has_linkage: self.has_linkage,
        }
    }
}

impl ContextItem {
    pub fn new(ident: Ident, has_linkage: bool) -> Self {
        Self {
            ident,
            from_this_scope: true,
            has_linkage
        }
    }
}

// TODO! convert this to take a &mut instead of taking ownership and returning a new one

pub struct Analyzer {
    pub tmp_count: u32
}

impl Analyzer {
    pub fn new() -> Self {
        Self { tmp_count: 0 }
    }

    pub fn analyze(mut self, program: ast::Program<ast::Expr>) -> ast::Program<ast::Expr> {
        let mut ctx = Context { mappings: HashMap::new() };

        ast::Program {
            top_level_items: program.top_level_items.into_iter().map(|f|{
                match f {
                    ast::Declaration::Fn(func) => {
                        ast::Declaration::Fn(self.analyze_function(func, &mut ctx))
                    },
                    ast::Declaration::Var(var) => {
                        ast::Declaration::Var(self.analyze_file_scope_var_decl(var, &mut ctx))
                    }
                }
            }).collect()
        }
    }

    fn gen_new_ident(&mut self, old_ident: &Ident) -> Ident {
        self.tmp_count += 1;
        Rc::new(format!(".na.gen.{}.{}", old_ident, self.tmp_count))
    }

    fn analyze_file_scope_var_decl(&mut self, mut decl: ast::VarDeclaration<ast::Expr>, context: &mut Context) -> ast::VarDeclaration<ast::Expr> {
        self.add_new_name(decl.name.clone(), context, true);

        decl.expr = decl.expr.map(|e|self.analyze_expr(e, context));

        decl
    }

    fn analyze_function(&mut self, function: ast::FunctionDecl<ast::Expr>, context: &mut Context) -> ast::FunctionDecl<ast::Expr> {
        let global = function.storage_class != Some(ast::StorageClass::Static);
        let name = self.add_new_name(function.name, context, global);

        let mut context = context.clone();
        let context = &mut context;

        let params = function.params.into_iter().map(|(ty, param)| {
            if let Some(item) = context.mappings.get(&param) && item.from_this_scope {
                panic!("Cannot declare parameter with same name, {param}");
            }

            (ty, self.add_new_name(param, context, false))
        }).collect();

        ast::FunctionDecl {
            name,
            ret_ty: function.ret_ty,
            params,
            block: function.block.map(|b|self.analyze_block(b, context)),
            storage_class: function.storage_class
        }
    }

    fn analyze_decl(&mut self, decl: ast::Declaration<ast::Expr>, is_top_level: bool, context: &mut Context) -> ast::Declaration<ast::Expr> {
        match decl {
            ast::Declaration::Var(var_decl) => {
                ast::Declaration::Var(self.analyze_var_decl(var_decl, context))
            },
            ast::Declaration::Fn(fn_decl) => {
                if fn_decl.block.is_some() && !is_top_level {
                    panic!("No function scope functions!!!!!");
                }

                ast::Declaration::Fn(self.analyze_function(fn_decl, context))
            }
        }
    }

    fn analyze_block(&mut self, block: ast::Block<ast::Expr>, context: &mut Context) -> ast::Block<ast::Expr> {
        ast::Block { statements: block.statements.into_iter().map(|stmt| {
            match stmt {
                ast::BlockItem::Declaration(decl) => {
                    ast::BlockItem::Declaration(self.analyze_decl(decl, false, context))
                },
                ast::BlockItem::Statement(stmt) => {
                    ast::BlockItem::Statement(self.analyze_statement(stmt, context))
                }
            }
        }).collect() }
    }

    fn add_new_name(&mut self, old_name: Ident, context: &mut Context, has_linkage: bool) -> Ident {
        let name = if !has_linkage {
            self.gen_new_ident(&old_name)
        } else {
            old_name.clone()
        };
        context.mappings.insert(old_name, ContextItem::new(name.clone(), has_linkage));
        name
    }

    fn analyze_var_decl(&mut self, var_decl: ast::VarDeclaration<ast::Expr>, context: &mut Context) -> ast::VarDeclaration<ast::Expr> {
        let is_extern = var_decl.storage_class == Some(ast::StorageClass::Extern);
        
        if let Some(item) = context.mappings.get(&var_decl.name)
           && item.from_this_scope
           && !(item.has_linkage && is_extern)
        {
            panic!("Conflicting local declarations for {}", var_decl.name);
        }

        if is_extern {
            self.add_new_name(var_decl.name.clone(), context, true);

            return var_decl;
        }

        let name = self.add_new_name(var_decl.name, context, false);

        ast::VarDeclaration::new(name, var_decl.ty, var_decl.expr.map(|expr|self.analyze_expr(expr, context)), var_decl.storage_class)
    }

    fn analyze_statement(&mut self, statement: ast::Statement<ast::Expr>, context: &mut Context) -> ast::Statement<ast::Expr> {
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
                ast::Statement::Block(self.analyze_block(block, &mut context.clone()))
            },
            ast::Statement::While(cond, box stmt, label) => {
                let cond = self.analyze_expr(cond, context);

                let stmt = self.analyze_statement(stmt, context);

                ast::Statement::While(cond, Box::new(stmt), label)
            },
            ast::Statement::DoWhile(cond, box stmt, label) => {
                let cond = self.analyze_expr(cond, context);

                let stmt = self.analyze_statement(stmt, context);

                ast::Statement::DoWhile(cond, Box::new(stmt), label)
            },
            ast::Statement::For { init, cond, post, body, label } => {
                let mut context = context.clone();
                let context = &mut context;
                
                let init = match init {
                    ast::ForInit::Decl(decl) => ast::ForInit::Decl(self.analyze_var_decl(decl, context)),
                    ast::ForInit::Expr(expr) => ast::ForInit::Expr(self.analyze_expr(expr, context)),
                    ast::ForInit::None => ast::ForInit::None
                };

                let cond = cond.map(|c|self.analyze_expr(c, context));

                let post = post.map(|p|self.analyze_expr(p, context));

                let body = Box::new(self.analyze_statement(*body, context));

                ast::Statement::For { init, cond, post, body, label }
            }
            ast::Statement::Break(_) |
            ast::Statement::Continue(_) => statement,
        }
    }

    fn get_ctx_item<'a>(&self, old_ident: &Ident, context: &'a Context) -> &'a ContextItem {
        if let Some(n) = context.mappings.get(old_ident) {
            n
        } else {
            panic!("Unknown item: {old_ident}");
        }
    } 

    fn analyze_expr(&mut self, expr: ast::Expr, context: &Context) -> ast::Expr {
        ast::Expr::new(match expr.0 {
            ast::DefaultExpr::Binary(ast::BinOp::Assign(assign_type), box (var, val)) => {
                let var = self.analyze_expr(var, context);
                let val = self.analyze_expr(val, context);

                ast::DefaultExpr::Binary(ast::BinOp::Assign(assign_type), Box::new((var, val)))
            },
            ast::DefaultExpr::Binary(op, box (l, r)) => {
                let l = self.analyze_expr(l, context);
                let r = self.analyze_expr(r, context);

                ast::DefaultExpr::Binary(op, Box::new((l,r)))
            },
            ast::DefaultExpr::Unary(op, box inner) => {
                let inner = self.analyze_expr(inner, context);

                ast::DefaultExpr::Unary(op, Box::new(inner))
            },
            ast::DefaultExpr::Var(name) => {
                let name = self.get_ctx_item(&name, context);

                ast::DefaultExpr::Var(name.ident.clone())
            },
            ast::DefaultExpr::Ternary(box (cond, l, r)) => {
                let cond = self.analyze_expr(cond, context);
                let l = self.analyze_expr(l, context);
                let r = self.analyze_expr(r, context);

                ast::DefaultExpr::Ternary(Box::new((cond, l, r)))
            },
            ast::DefaultExpr::FunctionCall(name, exprs) => {
                let name = self.get_ctx_item(&name, context);

                let exprs = exprs.into_iter().map(|e|self.analyze_expr(e, context)).collect();

                ast::DefaultExpr::FunctionCall(name.ident.clone(), exprs)
            },
            ast::DefaultExpr::Cast(ty, box inner) => {
                let inner = self.analyze_expr(inner, context);

                ast::DefaultExpr::Cast(ty, Box::new(inner))
            }

            ast::DefaultExpr::Number(_) => expr.0,
        })
    }
}