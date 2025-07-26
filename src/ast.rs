#![allow(unused)]

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
    pub name: String,
    pub block: Block,
}

impl FunctionDecl {
    pub fn new(name: String, block: Block) -> Self {
        Self {
            name,
            block
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Statement>
}

impl Block {
    pub fn new(statements: Vec<Statement>) -> Self {
        Self {
            statements
        }
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Return(Expr)
}

#[derive(Debug, Clone)]
pub enum Expr {
    Number(i32),
    Binary(BinOp, Box<(Expr, Expr)>),
    Unary(UnOp, Box<Expr>)
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Complement,
    Negate,
    Not,
}

#[derive(Debug, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
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
}