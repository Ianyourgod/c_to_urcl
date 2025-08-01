use std::collections::HashMap;

use crate::ast;
use crate::Ident;

#[derive(Debug, Clone)]
pub struct SymbolTable {
    pub table: HashMap<Ident, SymbolTableEntry>
}

#[derive(Debug, Clone)]
pub struct SymbolTableEntry {
    pub ty: ast::Type,
    pub attrs: IdentifierAttrs,
}

impl SymbolTableEntry {
    pub fn new(ty: ast::Type, attrs: IdentifierAttrs) -> Self {
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
    Initial(i32),
    NoInit,
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
    symbol_table: SymbolTable
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            symbol_table: SymbolTable::new()
        }
    }

    pub fn typecheck(mut self, program: ast::Program) -> (ast::Program, SymbolTable) {
        let program = ast::Program {
            top_level_items:
                program.top_level_items.into_iter().map(|f|{
                    match f {
                        ast::Declaration::Fn(f) => {
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

    fn typecheck_function(&mut self, mut function: ast::FunctionDecl) -> ast::FunctionDecl {
        let fn_type = ast::Type::Fn(function.params.len());
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

        function.block = function.block.map(|block| {
            let attrs = IdentifierAttrs::Local;
            for param in &function.params {
                self.symbol_table.insert(param.clone(), SymbolTableEntry::new(ast::Type::Int, attrs));
            }

            self.typecheck_block(block)
        });

        function
    }

    fn typecheck_file_scope_var_decl(&mut self, var_decl: ast::VarDeclaration) -> ast::VarDeclaration {
        let (mut initial_value, init_is_const) = if let Some(ast::Expr::Number(n)) = &var_decl.expr {
            (InitialValue::Initial(*n), true)
        } else if let None = var_decl.expr {
            (if var_decl.storage_class == Some(ast::StorageClass::Extern) {
                InitialValue::NoInit
            } else {
                InitialValue::Tentative
            }, false)
        } else {
            panic!("Non-constant static init");
        };

        let mut global = var_decl.storage_class != Some(ast::StorageClass::Static);

        if let Some(old_entry) = self.symbol_table.get(&var_decl.name) {
            if let ast::Type::Fn(_) = old_entry.ty {
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
        self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(ast::Type::Int, attrs));

        var_decl
    }

    fn typecheck_var_decl(&mut self, mut var_decl: ast::VarDeclaration) -> ast::VarDeclaration {
        if var_decl.storage_class == Some(ast::StorageClass::Extern) {
            if var_decl.expr.is_some() {
                panic!("Cannot have init on local extern variable declaration");
            }
            if let Some(old_entry) = self.symbol_table.get(&var_decl.name) {
                if let ast::Type::Fn(_) = old_entry.ty {
                    panic!("Function redeclared as a variable");
                }
            } else {
                let attrs = IdentifierAttrs::Static { init: InitialValue::NoInit, global: true };
                self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(ast::Type::Int, attrs));
            }

            return var_decl;
        }

        if var_decl.storage_class == Some(ast::StorageClass::Static) {
            let init = if let Some(ast::Expr::Number(n)) = var_decl.expr {
                InitialValue::Initial(n)
            } else if var_decl.expr.is_none() {
                InitialValue::Initial(0)
            } else {
                panic!("Non-constant init on static variable {}", var_decl.name);
            };

            let attrs = IdentifierAttrs::Static { init: init, global: false };
            self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(ast::Type::Int, attrs));

            return var_decl;
        }
        
        let attrs = IdentifierAttrs::Local;
        self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(ast::Type::Int, attrs));
        var_decl.expr = var_decl.expr.map(|e|self.typecheck_expr(e));
        return var_decl;
    }

    fn typecheck_block(&mut self, mut block: ast::Block) -> ast::Block {
        block.statements = block.statements.into_iter().map(|block_item| {
            match block_item {
                ast::BlockItem::Declaration(decl) => {
                    ast::BlockItem::Declaration(self.typecheck_declaration(decl))
                },
                ast::BlockItem::Statement(stmt) => {
                    ast::BlockItem::Statement(self.typecheck_statement(stmt))
                }
            }
        }).collect();

        block
    }

    fn typecheck_declaration(&mut self, decl: ast::Declaration) -> ast::Declaration {
        match decl {
            ast::Declaration::Fn(func_decl) => {
                ast::Declaration::Fn(self.typecheck_function(func_decl))
            },
            ast::Declaration::Var(var_decl) => {
                ast::Declaration::Var(self.typecheck_var_decl(var_decl))
            }
        }
    }

    fn typecheck_statement(&mut self, stmt: ast::Statement) -> ast::Statement {
        match stmt {
            ast::Statement::Return(expr) => ast::Statement::Return(self.typecheck_expr(expr)),
            ast::Statement::Block(block) => ast::Statement::Block(self.typecheck_block(block)),
            ast::Statement::Expr(expr) => ast::Statement::Expr(self.typecheck_expr(expr)),
            ast::Statement::If(cond, box (then_stmt, else_stmt)) => {
                let cond = self.typecheck_expr(cond);

                let then_stmt = self.typecheck_statement(then_stmt);
                let else_stmt = else_stmt.map(|s|self.typecheck_statement(s));

                ast::Statement::If(cond, Box::new((then_stmt, else_stmt)))
            },
            ast::Statement::While(cond, box stmt, label) => {
                let cond = self.typecheck_expr(cond);

                let stmt = self.typecheck_statement(stmt);

                ast::Statement::While(cond, Box::new(stmt), label)
            },
            ast::Statement::DoWhile(cond, box stmt, label) => {
                let cond = self.typecheck_expr(cond);

                let stmt = self.typecheck_statement(stmt);

                ast::Statement::DoWhile(cond, Box::new(stmt), label)
            },
            ast::Statement::For { init, cond, post, box body, label } => {
                let init = match init {
                    ast::ForInit::Decl(decl) => ast::ForInit::Decl(self.typecheck_var_decl(decl)),
                    ast::ForInit::Expr(expr) => ast::ForInit::Expr(self.typecheck_expr(expr)),
                    ast::ForInit::None => ast::ForInit::None,
                };

                let cond = cond.map(|c|self.typecheck_expr(c));
                let post = post.map(|p|self.typecheck_expr(p));

                let body = Box::new(self.typecheck_statement(body));

                ast::Statement::For { init, cond, post, body, label }
            },


            ast::Statement::Break(_) |
            ast::Statement::Continue(_) => stmt
        }
    }

    fn typecheck_expr(&mut self, expr: ast::Expr) -> ast::Expr {
        match expr {
            ast::Expr::Number(_) => expr,

            ast::Expr::FunctionCall(name, params) => {
                let fn_ty = self.symbol_table.get(&name).unwrap();

                let fn_ty = if let ast::Type::Fn(t) = fn_ty.ty { t } else {
                    panic!("Variable used in function call");
                };

                if fn_ty != params.len() {
                    panic!("Wrong number of args in function call");
                }

                let params = params.into_iter().map(|p|self.typecheck_expr(p)).collect();

                ast::Expr::FunctionCall(name, params)
            },
            ast::Expr::Binary(op, box (left, right)) => {
                let left = self.typecheck_expr(left);
                let right = self.typecheck_expr(right);

                ast::Expr::Binary(op, Box::new((left, right)))
            },
            ast::Expr::Unary(op, box inner) => {
                let inner = self.typecheck_expr(inner);

                ast::Expr::Unary(op, Box::new(inner))
            },
            ast::Expr::Var(v) => {
                if let ast::Type::Fn(_) = self.symbol_table.get(&v).unwrap().ty {
                    panic!("Function used as variable");
                }

                ast::Expr::Var(v)
            },
            ast::Expr::Ternary(box (cond, then_expr, else_expr)) => {
                let cond = self.typecheck_expr(cond);
                let then_expr = self.typecheck_expr(then_expr);
                let else_expr = self.typecheck_expr(else_expr);

                ast::Expr::Ternary(Box::new((cond, then_expr, else_expr)))
            }
        }
    }
}