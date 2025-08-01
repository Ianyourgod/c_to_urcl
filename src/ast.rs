#![allow(unused)]

use std::rc::Rc;

use crate::Ident;

#[derive(Debug, Clone)]
pub struct Program {
    pub top_level_items: Vec<Declaration>,
}

impl Program {
    pub fn new(fns: Vec<Declaration>) -> Self {
        Self {
            top_level_items: fns,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDecl {
    pub name: Ident,
    pub params: Vec<Ident>,
    pub block: Option<Block>,
    pub storage_class: Option<StorageClass>,
}

impl FunctionDecl {
    pub fn new(name: String, params: Vec<(Type, String)>, block: Option<Block>, storage_class: Option<StorageClass>) -> Self {
        Self {
            name: Rc::new(name),
            params: params.into_iter().map(|(_, s)|Rc::new(s)).collect(),
            block,
            storage_class
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<BlockItem>
}

impl Block {
    pub fn new(statements: Vec<BlockItem>) -> Self {
        Self {
            statements
        }
    }
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Var(VarDeclaration),
    Fn(FunctionDecl)
}

#[derive(Debug, Clone)]
pub enum BlockItem {
    Statement(Statement),
    Declaration(Declaration),
}

#[derive(Debug, Clone)]
pub enum Statement {
    Return(Expr),
    Expr(Expr),
    If(Expr, Box<(Statement, Option<Statement>)>),
    Block(Block),
    While(Expr, Box<Statement>, u32),
    DoWhile(Expr, Box<Statement>, u32),
    For {
        init: ForInit,
        cond: Option<Expr>,
        post: Option<Expr>,
        body: Box<Statement>,
        label: u32,
    },
    Break(u32),
    Continue(u32),
}

#[derive(Debug, Clone)]
pub enum ForInit {
    Decl(VarDeclaration),
    Expr(Expr),
    None,
}

#[derive(Debug, Clone)]
pub struct VarDeclaration {
    pub name: Ident,
    pub expr: Option<Expr>,
    pub storage_class: Option<StorageClass>,
}

impl VarDeclaration {
    pub fn new(name: Ident, expr: Option<Expr>, storage_class: Option<StorageClass>) -> Self {
        Self { name, expr, storage_class }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Number(i32),
    Binary(BinOp, Box<(Expr, Expr)>),
    Unary(UnOp, Box<Expr>),
    Var(Ident),
    Ternary(Box<(Expr, Expr, Expr)>),
    FunctionCall(Ident, Vec<Expr>)
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Complement,
    Negate,
    Not,
}

#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanEqual,
    GreaterThanEqual,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    LeftShift,
    RightShift,
    Assign(AssignType),
}

#[derive(Debug, Clone, Copy)]
pub enum AssignType {
    Normal,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    LeftShift,
    RightShift,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    Fn(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageClass {
    Static,
    Extern,
}

#[derive(Debug, Clone)]
pub enum Specifier {
    Storage(StorageClass),
    Type(Type)
}