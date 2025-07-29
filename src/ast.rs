#![allow(unused)]

use std::rc::Rc;

use crate::Ident;

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<FunctionDecl>,
}

impl Program {
    pub fn new(fns: Vec<FunctionDecl>) -> Self {
        Self {
            functions: fns,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDecl {
    pub name: Ident,
    pub block: Block,
}

impl FunctionDecl {
    pub fn new(name: String, block: Block) -> Self {
        Self {
            name: Rc::new(name),
            block
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
pub enum BlockItem {
    Statement(Statement),
    Declaration(VarDeclaration),
}

#[derive(Debug, Clone)]
pub enum Statement {
    Return(Expr),
    Expr(Expr),
    If(Expr, Box<(Statement, Option<Statement>)>),
    Block(Block),
}

#[derive(Debug, Clone)]
pub struct VarDeclaration {
    pub name: Ident,
    pub expr: Option<Expr>,
}

impl VarDeclaration {
    pub fn new(name: Ident, expr: Option<Expr>) -> Self {
        Self { name, expr }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Number(i32),
    Binary(BinOp, Box<(Expr, Expr)>),
    Unary(UnOp, Box<Expr>),
    Var(Ident),
    Ternary(Box<(Expr, Expr, Expr)>)
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