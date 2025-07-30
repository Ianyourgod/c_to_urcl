use std::collections::HashMap;

use crate::ast;
use crate::Ident;

#[derive(Debug, Clone)]
pub struct SymbolTable {
    table: HashMap<Ident, SymbolTableEntry>
}

#[derive(Debug, Clone)]
pub struct SymbolTableEntry {
    pub ty: ast::Type,
    pub defined: bool
}

impl SymbolTableEntry {
    pub fn new(ty: ast::Type, defined: bool) -> Self {
        Self {
            ty,
            defined
        }
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

    pub fn get(&mut self, name: &Ident) -> Option<&SymbolTableEntry> {
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
            functions:
                program.functions.into_iter().map(|f|self.typecheck_function(f)).collect()
        };

        (program, self.symbol_table)
    }

    fn typecheck_function(&mut self, mut function: ast::FunctionDecl) -> ast::FunctionDecl {
        let fn_type = ast::Type::Fn(function.params.len());
        let has_body = function.block.is_some();

        let already_defined = if let Some(old_entry) = self.symbol_table.get(&function.name) {
            if old_entry.ty != fn_type {
                panic!("Invalid function declaration");
            }
            if old_entry.defined && has_body {
                panic!("Function is defined more than once");
            }
            old_entry.defined
        } else { false };

        self.symbol_table.insert(function.name.clone(), SymbolTableEntry::new(fn_type, already_defined || has_body));

        function.block = function.block.map(|block| {
            for param in &function.params {
                self.symbol_table.insert(param.clone(), SymbolTableEntry::new(ast::Type::Int, true));
            }

            self.typecheck_block(block)
        });

        function
    }

    fn typecheck_var_decl(&mut self, mut var_decl: ast::VarDeclaration) -> ast::VarDeclaration {
        self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(ast::Type::Int, var_decl.expr.is_some()));
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