use std::collections::HashMap;
use std::rc::Rc;

use crate::Ident;

use crate::ast;

#[derive(Debug, Clone)]
pub struct Context {
    pub name_mappings: HashMap<Ident, ContextItem>,
    pub struct_map: HashMap<Ident, UserDefContext>,
    pub union_map: HashMap<Ident, UserDefContext>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            name_mappings: HashMap::new(),
            struct_map: HashMap::new(),
            union_map: HashMap::new(),
        }
    }
}

#[derive(Debug)]
pub struct UserDefContext {
    pub ident: Ident,
    pub from_this_scope: bool,
}

impl UserDefContext {
    pub fn new(ident: Ident) -> Self {
        Self {
            ident,
            from_this_scope: true,
        }
    }
}

impl Clone for UserDefContext {
    fn clone(&self) -> Self {
        Self {
            ident: self.ident.clone(),
            from_this_scope: false,
        }
    }
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
        let mut ctx = Context::new();

        ast::Program {
            top_level_items: program.top_level_items.into_iter().map(|f|{
                match f {
                    ast::Declaration::Fn(func) => {
                        ast::Declaration::Fn(self.analyze_function(func, &mut ctx))
                    },
                    ast::Declaration::Var(var) => {
                        ast::Declaration::Var(self.analyze_file_scope_var_decl(var, &mut ctx))
                    },
                    ast::Declaration::Struct(struct_decl) => {
                        ast::Declaration::Struct(self.analyze_struct(struct_decl, &mut ctx))
                    },
                    ast::Declaration::Union(union_decl) => {
                        ast::Declaration::Union(self.analyze_union(union_decl, &mut ctx))
                    },
                }
            }).collect()
        }
    }

    fn gen_new_ident(&mut self, old_ident: &Ident) -> Ident {
        self.tmp_count += 1;
        Rc::new(format!(".na.gen.{}.{}", old_ident, self.tmp_count))
    }

    fn analyze_struct(&mut self, struct_decl: ast::StructDeclaration, context: &mut Context) -> ast::StructDeclaration {
        let unique_tag = if let Some(ref old_entry) = context.struct_map.get(&struct_decl.name) && old_entry.from_this_scope {
            old_entry.ident.clone()
        } else {
            let tag = self.gen_new_ident(&struct_decl.name);
            context.struct_map.insert(struct_decl.name.clone(), UserDefContext::new(tag.clone()));
            tag
        };

        let members = struct_decl.members.into_iter().map(|member| {
            let ty = self.process_type(member.ty, context);
            ast::MemberDeclaration::new(member.name, ty)
        }).collect();

        ast::StructDeclaration::new(unique_tag, members)
    }

    fn analyze_union(&mut self, union_decl: ast::UnionDeclaration, context: &mut Context) -> ast::UnionDeclaration {
        let unique_tag = if let Some(ref old_entry) = context.union_map.get(&union_decl.name) && old_entry.from_this_scope {
            old_entry.ident.clone()
        } else {
            let tag = self.gen_new_ident(&union_decl.name);
            context.union_map.insert(union_decl.name.clone(), UserDefContext::new(tag.clone()));
            tag
        };

        let members = union_decl.members.into_iter().map(|member| {
            let ty = self.process_type(member.ty, context);
            ast::MemberDeclaration::new(member.name, ty)
        }).collect();

        ast::UnionDeclaration::new(unique_tag, members)
    }

    fn process_type(&mut self, ty: ast::Type, context: &Context) -> ast::Type {
        match ty {
            ast::Type::Struct(struct_name) => {
                if let Some(entry) = context.struct_map.get(&struct_name) {
                    ast::Type::Struct(entry.ident.clone())
                } else {
                    panic!("Cannot use undeclared struct type {struct_name}");
                }
            },
            ast::Type::Union(union_name) => {
                println!("{union_name}");
                if let Some(entry) = context.union_map.get(&union_name) {
                    ast::Type::Union(entry.ident.clone())
                } else {
                    panic!("Cannot use undeclared union type");
                }
            },
            ast::Type::Pointer(inner_ty) => {
                let inner_ty = self.process_type(*inner_ty, context);

                ast::Type::Pointer(Box::new(inner_ty))
            },
            ast::Type::Array(inner_ty, len) => {
                let inner_ty = self.process_type(*inner_ty, context);

                ast::Type::Array(Box::new(inner_ty), len)
            },
            ast::Type::Fn { params, ret_ty } => {
                let ret_ty = Box::new(self.process_type(*ret_ty, context));
                let params = params.into_iter().map(|ty| self.process_type(ty, context)).collect();

                ast::Type::Fn { params, ret_ty }
            },

            ast::Type::Void |
            ast::Type::Int  | ast::Type::UInt  |
            ast::Type::Char | ast::Type::UChar => ty,
        }
    }

    fn analyze_file_scope_var_decl(&mut self, mut decl: ast::VarDeclaration<ast::Expr>, context: &mut Context) -> ast::VarDeclaration<ast::Expr> {
        self.add_new_name(decl.name.clone(), context, true);

        decl.ty = self.process_type(decl.ty, context);
        decl.expr = decl.expr.map(|i|self.analyze_init(i, context));

        decl
    }

    fn analyze_init(&mut self, init: ast::Initializer<ast::Expr>, context: &Context) -> ast::Initializer<ast::Expr> {
        match init {
            ast::Initializer::Single(e) => ast::Initializer::Single(self.analyze_expr(e, context)),
            ast::Initializer::Compound(c) => ast::Initializer::Compound(c.into_iter().map(|i|self.analyze_init(i, context)).collect()),
            ast::Initializer::Fields(f) => ast::Initializer::Fields(f.into_iter().map(|(n,i)|(n,self.analyze_init(i, context))).collect()),
        }
    }

    fn analyze_function(&mut self, function: ast::FunctionDecl<ast::Expr>, context: &mut Context) -> ast::FunctionDecl<ast::Expr> {
        let global = function.storage_class != Some(ast::StorageClass::Static);
        let name = self.add_new_name(function.name, context, global);

        let mut context = context.clone();
        let context = &mut context;

        let params = function.params.into_iter().map(|(ty, param)| {
            if let Some(item) = context.name_mappings.get(&param) && item.from_this_scope {
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
            },
            ast::Declaration::Struct(struct_decl) => {
                ast::Declaration::Struct(self.analyze_struct(struct_decl, context))
            },
            ast::Declaration::Union(union_decl) => {
                ast::Declaration::Union(self.analyze_union(union_decl, context))
            },
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
        context.name_mappings.insert(old_name, ContextItem::new(name.clone(), has_linkage));
        name
    }

    fn analyze_var_decl(&mut self, var_decl: ast::VarDeclaration<ast::Expr>, context: &mut Context) -> ast::VarDeclaration<ast::Expr> {
        let is_extern = var_decl.storage_class == Some(ast::StorageClass::Extern);

        if let Some(item) = context.name_mappings.get(&var_decl.name)
           && item.from_this_scope
           && !(item.has_linkage && is_extern)
        {
            panic!("Conflicting local declarations for {}", var_decl.name);
        }

        if is_extern {
            self.add_new_name(var_decl.name.clone(), context, true);

            return ast::VarDeclaration::new(
                var_decl.name, 
                self.process_type(var_decl.ty, context),
                var_decl.expr,
                var_decl.storage_class
            );
        }

        let name = self.add_new_name(var_decl.name, context, false);

        ast::VarDeclaration::new(
            name,
            self.process_type(var_decl.ty, context),
            var_decl.expr.map(|i|self.analyze_init(i, context)),
            var_decl.storage_class
        )
    }

    fn analyze_statement(&mut self, statement: ast::Statement<ast::Expr>, context: &mut Context) -> ast::Statement<ast::Expr> {
        match statement {
            ast::Statement::Return(expr) => {
                ast::Statement::Return(expr.map(|expr|self.analyze_expr(expr, context)))
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
        if let Some(n) = context.name_mappings.get(old_ident) {
            n
        } else {
            panic!("Unknown item: {old_ident}");
        }
    } 

    fn analyze_expr(&mut self, expr: ast::Expr, context: &Context) -> ast::Expr {
        ast::Expr::new(match expr.0 {
            ast::DefaultExpr::Subscript(box (obj, idx)) => {
                let obj = self.analyze_expr(obj, context);
                let idx = self.analyze_expr(idx, context);

                ast::DefaultExpr::Subscript(Box::new((obj, idx)))
            },
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
                let ty = self.process_type(ty, context);
                let inner = self.analyze_expr(inner, context);

                ast::DefaultExpr::Cast(ty, Box::new(inner))
            },
            ast::DefaultExpr::SizeOf(box inner) => {
                let inner = self.analyze_expr(inner, context);

                ast::DefaultExpr::SizeOf(Box::new(inner))
            },
            ast::DefaultExpr::SizeOfT(ty) => {
                let ty = self.process_type(ty, context);

                ast::DefaultExpr::SizeOfT(ty)
            },
            ast::DefaultExpr::MemberAccess(box inner, member) => {
                let inner = self.analyze_expr(inner, context);

                ast::DefaultExpr::MemberAccess(Box::new(inner), member)
            },
            ast::DefaultExpr::PtrMemberAccess(box inner, member) => {
                let inner = self.analyze_expr(inner, context);

                ast::DefaultExpr::PtrMemberAccess(Box::new(inner), member)
            },
            ast::DefaultExpr::CompoundLiteral(ty, box init) => {
                let ty = self.process_type(ty, context);

                let init = self.analyze_init(init, context);

                ast::DefaultExpr::CompoundLiteral(ty, Box::new(init))
            }

            ast::DefaultExpr::String(_)    |
            ast::DefaultExpr::Constant(_) => expr.0,
        })
    }
}