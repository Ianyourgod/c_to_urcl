use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

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

#[derive(Debug, Clone)]
pub enum IdentifierAttrs {
    Fn {
        defined: bool,
        global: bool,
    },
    Static {
        init: InitialValue,
        global: bool,
    },
    Constant {
        init: StaticInit
    },
    Local
}

#[derive(Debug, Clone)]
pub enum InitialValue {
    Tentative,
    Initial(Vec<StaticInit>),
    NoInit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticInit {
    IntInit(i16),
    UIntInit(u16),
    CharInit(i16),
    UCharInit(u16),
    String {
        val: String,
        null_terminated: bool
    },
    Pointer(Ident), // pointer to another static object
    ZeroInit,
}

impl StaticInit {
    #[allow(dead_code)]
    pub fn from_const(c: ast::Const) -> Self {
        match c {
            ast::Const::Char(n) |
            ast::Const::Int(n) => Self::IntInit(n),
            ast::Const::UChar(n) |
            ast::Const::UInt(n) => Self::UIntInit(n),
        }
    }
}

impl Display for StaticInit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            StaticInit::IntInit(n) => &n.to_string(),
            StaticInit::UIntInit(n) => &n.to_string(),
            StaticInit::CharInit(n) => &n.to_string(),
            StaticInit::UCharInit(n) => &n.to_string(),
            StaticInit::String { val, null_terminated } => {
                let null_term = if *null_terminated { ", 0" } else { "" };
                &format!("\"{val}\"{null_term}")
            },
            StaticInit::Pointer(n) => &format!(".{n}"),
            StaticInit::ZeroInit => "0"
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
    strings: u32
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            current_ret_ty: Type::Int,
            strings: 0
        }
    }

    pub fn typecheck(mut self, program: ast::Program<Expr>) -> (ast::Program<TypedExpr>, SymbolTable) {
        let program = ast::Program {
            top_level_items:
                program.top_level_items.into_iter().filter_map(|f|{
                    match f {
                        ast::Declaration::Fn(f) => {
                            self.current_ret_ty = f.ret_ty.clone();
                            Some(ast::Declaration::Fn(self.typecheck_function(f)))
                        },
                        ast::Declaration::Var(v) => {
                            self.typecheck_file_scope_var_decl(v);

                            None
                        }
                    }
                }).collect()
        };

        (program, self.symbol_table)
    }

    fn typecheck_function(&mut self, function: ast::FunctionDecl<Expr>) -> ast::FunctionDecl<TypedExpr> {
        let fn_type = Type::Fn {
            params: function.params.iter().map(|(t, _)|{
                if let Type::Array(t, _) = t {
                    t.as_ref()
                } else {
                    t
                }.clone()
            }).collect(),
            ret_ty: Box::new(function.ret_ty.clone())
        };
        let has_body = function.block.is_some();
        let mut global = function.storage_class != Some(ast::StorageClass::Static);

        if matches!(function.ret_ty, Type::Array(_, _)) {
            panic!("A function cannot return an array");
        }

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
            for (ty, param) in &function.params {
                let attrs = IdentifierAttrs::Local;
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

    // we can return nothing as tacky uses the symbol table to generate static vars
    fn typecheck_file_scope_var_decl(&mut self, var_decl: ast::VarDeclaration<Expr>) {
        let default_init = if var_decl.storage_class == Some(ast::StorageClass::Extern) {
            InitialValue::NoInit
        } else {
            InitialValue::Tentative
        };
        
        let initial_value = if let Some(init) = var_decl.expr {
            InitialValue::Initial(self.init_to_static(init, &var_decl.ty))
        } else { default_init };

        let current_global = var_decl.storage_class != Some(ast::StorageClass::Static);

        let (global, init) = if let Some(old_entry) = self.symbol_table.get(&var_decl.name) {
            if matches!(old_entry.ty, Type::Fn { .. }) {
                panic!("Function redeclared as a variable!");
            }

            let (old_init, old_global) = if let IdentifierAttrs::Static { init, global } = &old_entry.attrs { (init, *global) } else { unreachable!() };

            if old_entry.ty != var_decl.ty {
                panic!("Conflicting file scope variable definitions (types)");
            }

            let global =
                if var_decl.storage_class == Some(ast::StorageClass::Extern) { old_global }
                else if current_global == old_global { current_global }
                else { panic!("Conflicting file scope variable linkage"); };

            let init = match (&old_init, &initial_value) {
                (InitialValue::Initial(_), InitialValue::Initial(_)) => panic!("Conflicting global variable definitions"),
                (InitialValue::Initial(_), _) => old_init.clone(),
                (InitialValue::Tentative, InitialValue::Tentative|InitialValue::NoInit) => InitialValue::Tentative,
                (_, InitialValue::Initial(_)|InitialValue::NoInit) => initial_value,
                _ => panic!("You did something wrong with global vars man")
            };

            (global, init)
        } else {
            (current_global, initial_value)
        };

        let attrs = IdentifierAttrs::Static { init, global };
        self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(var_decl.ty, attrs));
    }

    fn init_to_static(&mut self, init: ast::Initializer<Expr>, ty: &Type) -> Vec<StaticInit> {
        match (init, ty) {
            (ast::Initializer::Compound(inits), ast::Type::Array(_, _)) => {
                self.compound_init_to_static_inits_rec(inits, ty)
            },
            (ast::Initializer::Single(Expr(DefaultExpr::String(s))), ast::Type::Pointer(inner_ty)) => {
                if !inner_ty.is_char_ty() {
                    panic!("Cannot use a string initializer for a non-char pointer");
                }

                let string_name = self.strings;
                self.strings += 1;
                let string_name = format!(".str..{string_name}.");

                let str_len = s.len();

                let string_name = Rc::new(string_name);

                self.symbol_table.insert(string_name.clone(),
                    SymbolTableEntry::new(
                        ast::Type::Array(Box::new(ast::Type::Char), (str_len+1) as u16),
                        IdentifierAttrs::Constant { init: StaticInit::String { val: s, null_terminated: true } }
                    )
                );

                let init = StaticInit::Pointer(string_name);

                vec![init]
            }
            (ast::Initializer::Single(Expr(DefaultExpr::String(s))), ast::Type::Array(inner_ty, len)) => {
                if !inner_ty.is_char_ty() {
                    panic!("Cannot initialize non-char array with a string");
                }
                if s.len() > *len as usize {
                    panic!("String too long for array");
                }
                let null_terminated = s.len() != *len as usize;
                let extra_needed = (*len as i16 - s.len() as i16) - 1;
                let init = StaticInit::String { val: s, null_terminated };

                let extra = if extra_needed >= 0 { std::iter::repeat_n(self.static_zero_init(&inner_ty).into_iter().next().unwrap(), extra_needed as usize).collect() } else { vec![] };

                let mut out = vec![init];
                out.extend(extra.into_iter());
                out
            },
            (_, ast::Type::Array(_, _)) => panic!("Cannot initialize array to non-compound"),
            (ast::Initializer::Single(Expr(DefaultExpr::Constant(c))), _) => vec![self.const_to_init(c)],
            (_, _) => panic!("Invalid static init"),
        }
    }

    fn const_to_init(&self, c: ast::Const) -> StaticInit {
        // TODO! we don't check that pointers are 0
        match c {
            ast::Const::Int(n) => StaticInit::IntInit(n),
            ast::Const::UInt(n) => StaticInit::UIntInit(n),
            ast::Const::Char(n) => StaticInit::CharInit(n),
            ast::Const::UChar(n) => StaticInit::UCharInit(n),
        }
    }

    fn compound_init_to_static_inits_rec(&self, inits: Vec<ast::Initializer<Expr>>, ty: &Type) -> Vec<StaticInit> {
        inits.into_iter().flat_map(|i| {
            match (i, ty) {
                (ast::Initializer::Compound(c), Type::Array(inner_ty, len)) => {
                    let len = *len as usize;
                    
                    if c.len() > len {
                        panic!("Too many inits");
                    }

                    let needed_zeros = len - c.len();

                    let inits = self.compound_init_to_static_inits_rec(c, inner_ty.as_ref());
                    inits.into_iter().chain(std::iter::repeat(StaticInit::ZeroInit).take(needed_zeros)).collect()
                },
                (ast::Initializer::Compound(_), _) => panic!("Cannot use compound on non-compound type"),
                (ast::Initializer::Single(Expr(DefaultExpr::Constant(c))), _) => vec![self.const_to_init(c)],
                (_, _) => panic!("You did something wrong with a compound static init")
            }
        }).collect()
    }

    fn static_zero_init(&self, ty: &Type) -> Vec<StaticInit> {
        match ty {
            ast::Type::Array(inner_ty, len) => {
                std::iter::repeat(self.static_zero_init(inner_ty.as_ref()))
                    .flat_map(|i|i)
                    .take(*len as usize)
                    .collect()
            },
            ast::Type::Int => vec![StaticInit::IntInit(0)],
            ast::Type::UInt => vec![StaticInit::UIntInit(0)],
            ast::Type::Pointer(_) => vec![StaticInit::IntInit(0)],
            ast::Type::Char => vec![StaticInit::CharInit(0)],
            ast::Type::UChar => vec![StaticInit::UCharInit(0)],

            ast::Type::Fn { .. } => unreachable!()
        }
    }

    fn typecheck_var_decl(&mut self, var_decl: ast::VarDeclaration<Expr>) -> ast::VarDeclaration<TypedExpr> {
        if var_decl.storage_class == Some(ast::StorageClass::Extern) {
            if var_decl.expr.is_some() {
                panic!("Cannot have init on local extern variable declaration");
            }
            if let Some(old_entry) = self.symbol_table.get(&var_decl.name) {
                if matches!(old_entry.ty, Type::Fn { .. }) {
                    panic!("Function redeclared as a variable");
                }
            } else {
                let attrs = IdentifierAttrs::Static { init: InitialValue::NoInit, global: true };
                self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(var_decl.ty.clone(), attrs));
            }

            return ast::VarDeclaration::new(var_decl.name, var_decl.ty, None, var_decl.storage_class);
        }

        if var_decl.storage_class == Some(ast::StorageClass::Static) {
            let init = if let Some(init) = var_decl.expr {
                InitialValue::Initial(self.init_to_static(init, &var_decl.ty))
            } else {
                InitialValue::Initial(self.static_zero_init(&var_decl.ty))
            };

            let attrs = IdentifierAttrs::Static { init: init, global: false };
            self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(var_decl.ty.clone(), attrs));

            return ast::VarDeclaration::new(var_decl.name, var_decl.ty, None, var_decl.storage_class);
        }
        
        let attrs = IdentifierAttrs::Local;
        self.symbol_table.insert(var_decl.name.clone(), SymbolTableEntry::new(var_decl.ty.clone(), attrs));

        let expr = var_decl.expr.map(|e|self.typecheck_init(e, var_decl.ty.clone()));

        return ast::VarDeclaration::new(var_decl.name, var_decl.ty, expr, var_decl.storage_class);
    }

    fn typecheck_init(&mut self, init: ast::Initializer<Expr>, target_type: Type) -> ast::Initializer<TypedExpr> {
        match (&target_type, init) {
            (Type::Array(inner_ty, len), ast::Initializer::Single(Expr(DefaultExpr::String(s)))) => {
                if !inner_ty.is_char_ty() {
                    panic!("Cannot initialize a non-char array with a string");
                }
                if s.len() > *len as usize {
                    panic!("Too many characters in string");
                }

                ast::Initializer::Single(TypedExpr::new(DefaultExpr::String(s), target_type))
            },
            (_, ast::Initializer::Single(expr)) => {
                let expr = self.typecheck_and_convert(expr);
                let expr = self.convert_by_assignment(expr, &target_type);
                ast::Initializer::Single(expr)
            },
            (Type::Array(inner_ty, len), ast::Initializer::Compound(inits)) => {
                let len = *len as usize;
                
                if inits.len() > len {
                    panic!("Too many values in compound initializer");
                }

                let extra_needed = len - inits.len();

                let inits = inits.into_iter().map(|init| {
                    self.typecheck_init(init, (**inner_ty).clone())
                }).collect::<Vec<_>>().into_iter().chain(std::iter::repeat(self.zero_init(inner_ty.as_ref())).take(extra_needed)).collect::<Vec<_>>();

                ast::Initializer::Compound(inits)
            },
            _ => panic!("Cannot initialize a scalar object with a compound initializer")
        }
    }

    fn zero_init(&self, ty: &Type) -> ast::Initializer<TypedExpr> {
        match ty {
            Type::Int => ast::Initializer::Single(TypedExpr::new(DefaultExpr::Constant(ast::Const::Int(0)), ast::Type::Int)),
            Type::UInt => ast::Initializer::Single(TypedExpr::new(DefaultExpr::Constant(ast::Const::UInt(0)), ast::Type::Int)),
            Type::Pointer(_) => ast::Initializer::Single(TypedExpr::new(DefaultExpr::Constant(ast::Const::Int(0)), ty.clone())),
            Type::Array(ty, len) => {
                ast::Initializer::Compound(std::iter::repeat(self.zero_init(ty.as_ref())).take(*len as usize).collect())
            },
            Type::Char => ast::Initializer::Single(TypedExpr::new(DefaultExpr::Constant(ast::Const::Char(0)), ast::Type::Char)),
            Type::UChar => ast::Initializer::Single(TypedExpr::new(DefaultExpr::Constant(ast::Const::UChar(0)), ast::Type::UChar)),

            Type::Fn { .. } => panic!("Cannot zero init a function"),
        }
    }

    fn typecheck_block(&mut self, block: ast::Block<Expr>) -> ast::Block<TypedExpr> {
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

    fn typecheck_declaration(&mut self, decl: ast::Declaration<Expr>) -> ast::Declaration<TypedExpr> {
        match decl {
            ast::Declaration::Fn(func_decl) => {
                ast::Declaration::Fn(self.typecheck_function(func_decl))
            },
            ast::Declaration::Var(var_decl) => {
                ast::Declaration::Var(self.typecheck_var_decl(var_decl))
            }
        }
    }

    fn typecheck_statement(&mut self, stmt: Statement<Expr>) -> Statement<TypedExpr> {
        match stmt {
            Statement::Return(expr) => {
                let e = self.typecheck_and_convert(expr);

                let expr = self.convert_by_assignment(e, &self.current_ret_ty);

                Statement::Return(expr)
            },
            Statement::Block(block) => Statement::Block(self.typecheck_block(block)),
            Statement::Expr(expr) => Statement::Expr(self.typecheck_and_convert(expr)),
            Statement::If(cond, box (then_stmt, else_stmt)) => {
                let cond = self.typecheck_and_convert(cond);

                let then_stmt = self.typecheck_statement(then_stmt);
                let else_stmt = else_stmt.map(|s|self.typecheck_statement(s));

                Statement::If(cond, Box::new((then_stmt, else_stmt)))
            },
            Statement::While(cond, box stmt, label) => {
                let cond = self.typecheck_and_convert(cond);

                let stmt = self.typecheck_statement(stmt);

                Statement::While(cond, Box::new(stmt), label)
            },
            Statement::DoWhile(cond, box stmt, label) => {
                let cond = self.typecheck_and_convert(cond);

                let stmt = self.typecheck_statement(stmt);

                Statement::DoWhile(cond, Box::new(stmt), label)
            },
            Statement::For { init, cond, post, box body, label } => {
                let init = match init {
                    ast::ForInit::Decl(decl) => ast::ForInit::Decl(self.typecheck_var_decl(decl)),
                    ast::ForInit::Expr(expr) => ast::ForInit::Expr(self.typecheck_and_convert(expr)),
                    ast::ForInit::None => ast::ForInit::None,
                };

                let cond = cond.map(|c|self.typecheck_and_convert(c));
                let post = post.map(|p|self.typecheck_and_convert(p));

                let body = Box::new(self.typecheck_statement(body));

                Statement::For { init, cond, post, body, label }
            },


            Statement::Break(l) => Statement::Break(l),
            Statement::Continue(l) => Statement::Continue(l)
        }
    }

    fn typecheck_and_convert(&mut self, expr: Expr) -> TypedExpr {
        let expr = self.typecheck_expr(expr);

        match &expr.ty {
            Type::Array(el_ty, _) => {
                let ty = el_ty.clone();
                TypedExpr::new(
                    DefaultExpr::Unary(ast::UnOp::AddressOf, Box::new(expr)),
                    Type::Pointer(ty)
                )
            }
            _ => expr
        }
    }

    fn typecheck_expr(&mut self, expr: Expr) -> TypedExpr {
        match expr.0 {
            DefaultExpr::Constant(c) => {
                TypedExpr::new(DefaultExpr::Constant(c), c.to_type())
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
                    let e = self.typecheck_and_convert(p);
                    self.convert_by_assignment(e, &ty)
                }).collect();

                TypedExpr::new(DefaultExpr::FunctionCall(name, params), ret_ty)
            },
            DefaultExpr::Binary(ast::BinOp::Assign(assign_ty), box (left, right)) => {
                let left = self.typecheck_and_convert(left);

                if !self.is_lvalue(&left) {
                    panic!("Cannot assign to a non-lvalue")
                }

                let right = self.typecheck_and_convert(right);

                let left_ty = left.ty.clone();
                let right = self.convert_by_assignment(right, &left_ty);

                TypedExpr::new(
                    DefaultExpr::Binary(ast::BinOp::Assign(assign_ty), Box::new((left, right))), left_ty)
            },
            DefaultExpr::Binary(op @ (ast::BinOp::Equal | ast::BinOp::NotEqual), box (left, right)) => {
                let left = self.typecheck_and_convert(left);
                let right = self.typecheck_and_convert(right);

                let common_type = if left.ty.is_pointer_type() || right.ty.is_pointer_type() {
                    self.get_common_pointer_type(&left, &right).clone()
                } else {
                    left.ty.get_common_type(&right.ty)
                };

                let left = self.convert_to(left, &common_type);
                let right = self.convert_to(right, &common_type);

                TypedExpr::new(DefaultExpr::Binary(op, Box::new((left, right))), ast::Type::Int)
            },
            DefaultExpr::Binary(ast::BinOp::Add, box (left, right)) => {
                let left = self.typecheck_and_convert(left);
                let right = self.typecheck_and_convert(right);

                if left.ty.is_arithmetic() && right.ty.is_arithmetic() {
                    let common_type = left.ty.get_common_type(&right.ty);

                    let left = self.convert_to(left, &common_type);
                    let right = self.convert_to(right, &common_type);

                    let ty = Type::Int;

                    TypedExpr::new(DefaultExpr::Binary(ast::BinOp::Add, Box::new((left, right))), ty)
                } else if left.ty.is_pointer_type() && right.ty.is_arithmetic() {
                    let right = self.convert_to(right, &ast::Type::Int);
                    let ty = left.ty.clone();
                    TypedExpr::new(DefaultExpr::Binary(ast::BinOp::Add, Box::new((left, right))), ty)
                } else if right.ty.is_pointer_type() && left.ty.is_arithmetic() {
                    let left = self.convert_to(left, &ast::Type::Int);
                    let ty = right.ty.clone();
                    TypedExpr::new(DefaultExpr::Binary(ast::BinOp::Add, Box::new((left, right))), ty)
                } else {
                    panic!()
                }
            },
            DefaultExpr::Binary(ast::BinOp::Sub, box (left, right)) => {
                let left = self.typecheck_and_convert(left);
                let right = self.typecheck_and_convert(right);

                if left.ty.is_arithmetic() && right.ty.is_arithmetic() {
                    let common_type = left.ty.get_common_type(&right.ty);

                    let left = self.convert_to(left, &common_type);
                    let right = self.convert_to(right, &common_type);

                    let ty = Type::Int;

                    TypedExpr::new(DefaultExpr::Binary(ast::BinOp::Sub, Box::new((left, right))), ty)
                } else if left.ty.is_pointer_type() && right.ty.is_arithmetic() {
                    let right = self.convert_to(right, &ast::Type::Int);
                    let ty = left.ty.clone();
                    TypedExpr::new(DefaultExpr::Binary(ast::BinOp::Add, Box::new((left, right))), ty)
                } else if left.ty.is_pointer_type() && left.ty == right.ty {
                    let ty = left.ty.clone();
                    TypedExpr::new(DefaultExpr::Binary(ast::BinOp::Add, Box::new((left, right))), ty)
                } else {
                    panic!()
                }
            },
            DefaultExpr::Binary(op, box (left, right)) => {
                let left = self.typecheck_and_convert(left);
                let right = self.typecheck_and_convert(right);

                if op == ast::BinOp::And || op == ast::BinOp::Or {
                    return TypedExpr::new(DefaultExpr::Binary(op, Box::new((left, right))), Type::Int);
                }

                let common_type = left.ty.get_common_type(&right.ty);

                let left = self.convert_to(left, &common_type);
                let right = self.convert_to(right, &common_type);

                let ty = if op.is_arithmetic() { common_type } else { Type::Int };

                TypedExpr::new(DefaultExpr::Binary(op, Box::new((left, right))), ty)
            },
            DefaultExpr::Unary(ast::UnOp::Not, box inner) => {
                let inner = self.typecheck_and_convert(inner);

                let ty = Type::Int;

                TypedExpr::new(DefaultExpr::Unary(ast::UnOp::Not, Box::new(inner)), ty)
            },
            DefaultExpr::Unary(ast::UnOp::Dereference, box inner) => {
                let inner = self.typecheck_and_convert(inner);

                match &inner.ty {
                    Type::Pointer(ty) => {
                        let ty = (**ty).clone();
                        TypedExpr::new(DefaultExpr::Unary(ast::UnOp::Dereference, Box::new(inner)), ty)
                    },
                    _ => panic!("Cannot deref non-pointer type")
                }
            },
            DefaultExpr::Unary(ast::UnOp::AddressOf, box inner) => {
                let inner = self.typecheck_expr(inner);
                if !self.is_lvalue(&inner) {
                    panic!("Cannot get the address of a non-lvalue");
                }

                let ty = Type::Pointer(Box::new(inner.ty.clone()));

                TypedExpr::new(DefaultExpr::Unary(ast::UnOp::AddressOf, Box::new(inner)), ty)
                
            },
            DefaultExpr::Unary(op, box inner) => {
                let inner = self.typecheck_and_convert(inner);

                let ty = inner.ty.clone();

                if ty.is_pointer_type() { panic!("Cannot negate or complement a pointer"); }
                let inner = if ty.is_char_ty() { self.convert_to(inner, &Type::Int) } else { inner };

                TypedExpr::new(DefaultExpr::Unary(op, Box::new(inner)), ty)
            },
            DefaultExpr::Var(v) => {
                let ty = &self.symbol_table.get(&v).unwrap().ty;
                if matches!(ty, Type::Fn { .. }) {
                    panic!("Function used as variable");
                }

                TypedExpr::new(DefaultExpr::Var(v), ty.clone())
            },
            DefaultExpr::Ternary(box (cond, then_expr, else_expr)) => {
                let cond = self.typecheck_and_convert(cond);
                let then_expr = self.typecheck_and_convert(then_expr);
                let else_expr = self.typecheck_and_convert(else_expr);

                let common_type = if then_expr.ty.is_pointer_type() || else_expr.ty.is_pointer_type() {
                    self.get_common_pointer_type(&then_expr, &else_expr).clone()
                } else {
                    then_expr.ty.get_common_type(&else_expr.ty)
                };

                let then_expr = self.convert_to(then_expr, &common_type);
                let else_expr = self.convert_to(else_expr, &common_type);

                TypedExpr::new(DefaultExpr::Ternary(Box::new((cond, then_expr, else_expr))), common_type)
            },
            DefaultExpr::Cast(t, box inner) => {
                let inner = self.typecheck_and_convert(inner);

                if matches!(t, Type::Array(_, _)) {
                    panic!("Cannot cast to an array type");
                }

                TypedExpr::new(DefaultExpr::Cast(t.clone(), Box::new(inner)), t)
            },
            DefaultExpr::Subscript(box (obj, idx)) => {
                let obj = self.typecheck_and_convert(obj);
                let idx = self.typecheck_and_convert(idx);

                let (refed_ty, obj, idx) = if let Some(ty) = obj.ty.refed_ptr_ty() && idx.ty.is_arithmetic() {
                    (ty.clone(), obj, self.convert_to(idx, &Type::Int))
                } else if obj.ty.is_arithmetic() && let Some(ty) = idx.ty.refed_ptr_ty() {
                    (ty.clone(), self.convert_to(obj, &Type::Int), idx)
                } else {
                    panic!("Subscript must have ptr and int operands");
                };

                TypedExpr::new(DefaultExpr::Subscript(Box::new((obj, idx))), refed_ty)
            },

            DefaultExpr::String(s) => {
                let len = s.len() + 1;
                TypedExpr::new(DefaultExpr::String(s), Type::Array(Box::new(Type::Char), len as u16)) 
            }
        }
    }

    fn is_lvalue(&self, expr: &TypedExpr) -> bool {
        match expr.expr {
            DefaultExpr::Var(_) |
            DefaultExpr::Unary(ast::UnOp::Dereference, _) |
            DefaultExpr::Subscript(_) => true,
            _ => false
        }
    }

    fn convert_to(&self, expr: TypedExpr, ty: &Type) -> TypedExpr {
        if expr.ty == *ty {
            return expr;
        }

        return TypedExpr::new(DefaultExpr::Cast(ty.clone(), Box::new(expr)), ty.clone())
    }

    fn is_null_pointer_constant(&self, expr: &TypedExpr) -> bool {
        match expr.expr {
            DefaultExpr::Constant(c) => {
                match c {
                    ast::Const::Int(0)   |
                    ast::Const::UInt(0) => true,
                    _ => false,
                }
            },
            _ => false
        }
    }

    fn get_common_pointer_type<'a>(&self, e1: &'a TypedExpr, e2: &'a TypedExpr) -> &'a Type {
        if e1.ty == e2.ty {
            return &e1.ty;
        }

        if self.is_null_pointer_constant(e1) {
            return &e2.ty;
        }

        if self.is_null_pointer_constant(e2) {
            return &e1.ty;
        }

        panic!("Expressions have incompatible types");
    }

    fn convert_by_assignment(&self, expr: TypedExpr, ty: &Type) -> TypedExpr {
        if expr.ty == *ty {
            return expr;
        }

        if (expr.ty.is_arithmetic() && ty.is_arithmetic()) ||
           (self.is_null_pointer_constant(&expr) && ty.is_pointer_type())
        {
            return self.convert_to(expr, ty);
        }

        panic!("Cannot convert type");
    }
}