use std::collections::HashMap;
use std::fmt::Display;

use crate::ast::{self, Expr, TypedExpr, DefaultExpr, Type, Statement};
use crate::Ident;

#[derive(Debug, Clone)]
pub struct SymbolTable {
    pub table: HashMap<Ident, SymbolTableEntry>
}

#[derive(Debug, Clone)]
pub struct SymbolTableEntry {
    pub ty: Type,
    pub attrs: IdentifierAttrs,
}

impl SymbolTableEntry {
    pub fn new(ty: Type, attrs: IdentifierAttrs) -> Self {
        Self {
            ty,
            attrs
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum IdentifierAttrs {
    Fn {
        defined: bool,
        global: bool,
    },
    Static {
        init: InitialValue,
        global: bool,
    },
    Local
}

#[derive(Debug, Clone, Copy)]
pub enum InitialValue {
    Tentative,
    Initial(StaticInit),
    NoInit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StaticInit {
    IntInit(i16),
    UIntInit(u16),
}

impl StaticInit {
    pub fn from_const(c: ast::Const) -> Self {
        match c {
            ast::Const::Int(n) => Self::IntInit(n),
            ast::Const::UInt(n) => Self::UIntInit(n)
        }
    }
}

impl Display for StaticInit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            StaticInit::IntInit(n) => &n.to_string(),
            StaticInit::UIntInit(n) => &n.to_string()
        };

        f.write_str(s)
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            table: HashMap::new()
        }
    }

    pub fn insert(&mut self, name: Ident, entry: SymbolTableEntry) -> Option<SymbolTableEntry> {
        self.table.insert(name, entry)
    }

    pub fn get(&self, name: &Ident) -> Option<&SymbolTableEntry> {
        self.table.get(name)
    }
}

pub struct TypeChecker {
    symbol_table: SymbolTable,
    current_ret_ty: Type,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            current_ret_ty: Type::Int,
        }
    }

    pub fn typecheck(mut self, program: ast::Program<Expr>) -> (ast::Program<TypedExpr>, SymbolTable) {
        let program = ast::Program {
            top_level_items:
                program.top_level_items.into_iter().map(|f|{
                    match f {
                        ast::Declaration::Fn(f) => {
                            self.current_ret_ty = f.ret_ty.clone();
                            ast::Declaration::Fn(self.typecheck_function(f))
                        },
                        ast::Declaration::Var(v) => {
                            ast::Declaration::Var(self.typecheck_file_scope_var_decl(v))
                        }
                    }
                }).collect()
        };

        (program, self.symbol_table)
    }

    fn typecheck_function(&mut self, function: ast::FunctionDecl<Expr>) -> ast::FunctionDecl<TypedExpr> {
        let fn_type = Type::Fn {
            params: function.params.iter().map(|(t, _)|t.clone()).collect(),
            ret_ty: Box::new(function.ret_ty.clone())
        };
        let has_body = function.block.is_some();
        let mut global = function.storage_class != Some(ast::StorageClass::Static);

        let already_defined = if let Some(old_entry) = self.symbol_table.get(&function.name) {
            if old_entry.ty != fn_type {
                panic!("Invalid function declaration");
            }
            let (old_defined, old_global) = if let IdentifierAttrs::Fn { defined, global } = old_entry.attrs { (defined, global) } else { unreachable!() };
            if old_defined && has_body {
                panic!("Function is defined more than once");
            }

            if old_global && function.storage_class == Some(ast::StorageClass::Static) {
                panic!("Static function declaration of {} follows non-static declaration", function.name);
            }
            global = old_global;

            old_defined
        } else { false };

        let attrs = IdentifierAttrs::Fn {
            defined: already_defined || has_body,
            global
        };
        self.symbol_table.insert(function.name.clone(), SymbolTableEntry::new(fn_type, attrs));

        let block = function.block.map(|block| {
            let attrs = IdentifierAttrs::Local;
            for (ty, param) in &function.params {
                self.symbol_table.insert(param.clone(), SymbolTableEntry::new(ty.clone(), attrs));
            }

            self.typecheck_block(block)
        });

        ast::FunctionDecl {
            name: function.name,
            ret_ty: function.ret_ty,
            params: function.params,
            block,
            storage_class: function.storage_class
        }
    }

    fn typecheck_file_scope_var_decl(&mut self, var_decl: ast::VarDeclaration<ast::Expr>) -> ast::VarDeclaration<TypedExpr> {
        let (mut initial_value, init_is_const, expr) = if let Some(ast::Expr(DefaultExpr::Number(n))) = &var_decl.expr {
            (InitialValue::Initial(StaticInit::from_const(*n)), true, Some(TypedExpr::new(DefaultExpr::Number(*n), n.to_type())))
        } else if var_decl.expr.is_none() {
            (if var_decl.storage_class == Some(ast::StorageClass::Extern) {
                InitialValue::NoInit
            } else {
                InitialValue::Tentative
            }, false, None)
        } else {
            panic!("Non-constant static init");
        };

        let mut global = var_decl.storage_class != Some(ast::StorageClass::Static);

        if let Some(old_entry) = self.symbol_table.get(&var_decl.name) {
            if let Type::Fn { .. } = old_entry.ty {
                panic!("Function redeclared as a variable!");
            }

            let (old_init, old_global) = if let IdentifierAttrs::Static { init, global } = old_entry.attrs { (init, global) } else { unreachable!() };

            if var_decl.storage_class == Some(ast::StorageClass::Extern) {
                global = old_global;
            } else if old_global != global {
                panic!("Conflicting variable linkage with variable {}", var_decl.name);
            }

            if let InitialValue::Initial(_) = old_init {
                if init_is_const {
                    panic!("Conflicting file scope variable definitions with variable {}", var_decl.name);
                } else {
                    initial_value = old_init;
                }
            } else if !init_is_const && let InitialValue::Tentative = old_init {
                initial_value = old_init;
            }
        }

        let attrs = IdentifierAttrs::Static { init: initial_value, global };
        self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(Type::Int, attrs));

        ast::VarDeclaration {
            name: var_decl.name,
            ty: var_decl.ty,
            expr,
            storage_class: var_decl.storage_class,
        }
    }

    fn typecheck_var_decl(&mut self, var_decl: ast::VarDeclaration<ast::Expr>) -> ast::VarDeclaration<TypedExpr> {
        if var_decl.storage_class == Some(ast::StorageClass::Extern) {
            if var_decl.expr.is_some() {
                panic!("Cannot have init on local extern variable declaration");
            }
            if let Some(old_entry) = self.symbol_table.get(&var_decl.name) {
                if let Type::Fn { .. } = old_entry.ty {
                    panic!("Function redeclared as a variable");
                }
            } else {
                let attrs = IdentifierAttrs::Static { init: InitialValue::NoInit, global: true };
                self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(Type::Int, attrs));
            }

            return ast::VarDeclaration::new(var_decl.name, var_decl.ty, None, var_decl.storage_class);
        }

        if var_decl.storage_class == Some(ast::StorageClass::Static) {
            let (init, expr) = if let Some(ast::Expr(DefaultExpr::Number(n))) = var_decl.expr {
                (InitialValue::Initial(StaticInit::from_const(n)), Some(TypedExpr::new(DefaultExpr::Number(n), n.to_type())))
            } else if var_decl.expr.is_none() {
                (InitialValue::Initial(StaticInit::IntInit(0)), None)
            } else {
                panic!("Non-constant init on static variable {}", var_decl.name);
            };

            let attrs = IdentifierAttrs::Static { init: init, global: false };
            self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(Type::Int, attrs));

            return ast::VarDeclaration::new(var_decl.name, var_decl.ty, expr, var_decl.storage_class);
        }
        
        let attrs = IdentifierAttrs::Local;
        self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(Type::Int, attrs));
        let expr = var_decl.expr.map(|e|self.typecheck_expr(e));
        return ast::VarDeclaration::new(var_decl.name, var_decl.ty, expr, var_decl.storage_class);
    }

    fn typecheck_block(&mut self, block: ast::Block<ast::Expr>) -> ast::Block<TypedExpr> {
        ast::Block {
            statements: block.statements.into_iter().map(|block_item| {
                match block_item {
                    ast::BlockItem::Declaration(decl) => {
                        ast::BlockItem::Declaration(self.typecheck_declaration(decl))
                    },
                    ast::BlockItem::Statement(stmt) => {
                        ast::BlockItem::Statement(self.typecheck_statement(stmt))
                    }
                }
            }).collect()
        }
    }

    fn typecheck_declaration(&mut self, decl: ast::Declaration<ast::Expr>) -> ast::Declaration<TypedExpr> {
        match decl {
            ast::Declaration::Fn(func_decl) => {
                ast::Declaration::Fn(self.typecheck_function(func_decl))
            },
            ast::Declaration::Var(var_decl) => {
                ast::Declaration::Var(self.typecheck_var_decl(var_decl))
            }
        }
    }

    fn typecheck_statement(&mut self, stmt: Statement<ast::Expr>) -> Statement<TypedExpr> {
        match stmt {
            Statement::Return(expr) => {
                let e = self.typecheck_expr(expr);

                let expr = self.convert_to(e, &self.current_ret_ty);

                Statement::Return(expr)
            },
            Statement::Block(block) => Statement::Block(self.typecheck_block(block)),
            Statement::Expr(expr) => Statement::Expr(self.typecheck_expr(expr)),
            Statement::If(cond, box (then_stmt, else_stmt)) => {
                let cond = self.typecheck_expr(cond);

                let then_stmt = self.typecheck_statement(then_stmt);
                let else_stmt = else_stmt.map(|s|self.typecheck_statement(s));

                Statement::If(cond, Box::new((then_stmt, else_stmt)))
            },
            Statement::While(cond, box stmt, label) => {
                let cond = self.typecheck_expr(cond);

                let stmt = self.typecheck_statement(stmt);

                Statement::While(cond, Box::new(stmt), label)
            },
            Statement::DoWhile(cond, box stmt, label) => {
                let cond = self.typecheck_expr(cond);

                let stmt = self.typecheck_statement(stmt);

                Statement::DoWhile(cond, Box::new(stmt), label)
            },
            Statement::For { init, cond, post, box body, label } => {
                let init = match init {
                    ast::ForInit::Decl(decl) => ast::ForInit::Decl(self.typecheck_var_decl(decl)),
                    ast::ForInit::Expr(expr) => ast::ForInit::Expr(self.typecheck_expr(expr)),
                    ast::ForInit::None => ast::ForInit::None,
                };

                let cond = cond.map(|c|self.typecheck_expr(c));
                let post = post.map(|p|self.typecheck_expr(p));

                let body = Box::new(self.typecheck_statement(body));

                Statement::For { init, cond, post, body, label }
            },


            Statement::Break(l) => Statement::Break(l),
            Statement::Continue(l) => Statement::Continue(l)
        }
    }

    fn typecheck_expr(&mut self, expr: ast::Expr) -> TypedExpr {
        match expr.0 {
            DefaultExpr::Number(c) => {
                TypedExpr::new(DefaultExpr::Number(c), c.to_type())
            },
            DefaultExpr::FunctionCall(name, params) => {
                let fn_ty = self.symbol_table.get(&name).unwrap();

                let (params_ty, ret_ty) = if let Type::Fn { params, ret_ty } = &fn_ty.ty { (params, ret_ty) } else {
                    panic!("Variable used in function call");
                };

                if params.len() != params_ty.len() {
                    panic!("Wrong number of args in function call");
                }

                let ret_ty = (**ret_ty).clone();

                let params: Vec<TypedExpr> = params.into_iter().zip(params_ty.clone()).map(|(p, ty)|{
                    let e = self.typecheck_expr(p);
                    self.convert_to(e, &ty)
                }).collect();

                TypedExpr::new(DefaultExpr::FunctionCall(name, params), ret_ty)
            },
            DefaultExpr::Binary(ast::BinOp::Assign(assign_ty), box (left, right)) => {
                let left = self.typecheck_expr(left);
                let right = self.typecheck_expr(right);

                let left_ty = left.ty.clone();
                let right = self.convert_to(right, &left_ty);

                TypedExpr::new(
                    DefaultExpr::Binary(ast::BinOp::Assign(assign_ty), Box::new((left, right))), left_ty)
            },
            DefaultExpr::Binary(op, box (left, right)) => {
                let left = self.typecheck_expr(left);
                let right = self.typecheck_expr(right);

                if op == ast::BinOp::And || op == ast::BinOp::Or {
                    return TypedExpr::new(DefaultExpr::Binary(op, Box::new((left, right))), Type::Int);
                }

                let common_type = left.ty.get_common_type(&right.ty).clone();

                let left = self.convert_to(left, &common_type);
                let right = self.convert_to(right, &common_type);

                let ty = if op.is_arithmetic() { common_type } else { Type::Int };

                TypedExpr::new(DefaultExpr::Binary(op, Box::new((left, right))), ty)
            },
            DefaultExpr::Unary(op, box inner) => {
                let inner = self.typecheck_expr(inner);

                let ty = match op {
                    ast::UnOp::Not => Type::Int,
                    _ => inner.ty.clone()
                };

                TypedExpr::new(DefaultExpr::Unary(op, Box::new(inner)), ty)
            },
            DefaultExpr::Var(v) => {
                let ty = &self.symbol_table.get(&v).unwrap().ty;
                if let Type::Fn { .. } = ty {
                    panic!("Function used as variable");
                }

                TypedExpr::new(DefaultExpr::Var(v), ty.clone())
            },
            DefaultExpr::Ternary(box (cond, then_expr, else_expr)) => {
                let cond = self.typecheck_expr(cond);
                let then_expr = self.typecheck_expr(then_expr);
                let else_expr = self.typecheck_expr(else_expr);

                let then_ty = then_expr.ty.clone();
                let else_expr = self.convert_to(else_expr, &then_ty);

                TypedExpr::new(DefaultExpr::Ternary(Box::new((cond, then_expr, else_expr))), then_ty)
            },
            DefaultExpr::Cast(t, box inner) => {
                let inner = self.typecheck_expr(inner);

                TypedExpr::new(DefaultExpr::Cast(t.clone(), Box::new(inner)), t)
            }
        }
    }

    fn convert_to(&self, expr: TypedExpr, ty: &Type) -> TypedExpr {
        if expr.ty == *ty {
            return expr;
        }

        return TypedExpr::new(DefaultExpr::Cast(ty.clone(), Box::new(expr)), ty.clone())
    }
}