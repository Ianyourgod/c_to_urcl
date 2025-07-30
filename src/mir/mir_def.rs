use std::{collections::HashMap, fmt::Display};

pub use crate::Ident;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum GenericBlockID {
    Generic(u32),
    LoopBreak(u32),
    LoopContinue(u32),
}

impl Display for GenericBlockID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (s, n) = match self {
            GenericBlockID::Generic(n) => ("gen.", *n),
            GenericBlockID::LoopBreak(n) => ("lbreak.", *n),
            GenericBlockID::LoopContinue(n) => ("lcont", *n)
        };

        f.write_str(s)?;
        f.write_str(&n.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<Function>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Ident,
    pub params: Vec<Ident>,
    pub basic_blocks: CFG,
}

#[derive(Debug, Clone)]
pub struct CFG {
    pub blocks: HashMap<BlockID, BasicBlock>,
}

#[derive(Debug, Clone)]
pub enum BasicBlock {
    Start {
        successors: Vec<BlockID>
    },
    End,
    Generic(GenericBlock)
}

impl BasicBlock {
    pub fn get_successors(&self) -> Vec<BlockID> {
        match self {
            BasicBlock::Generic(g) => g.terminator.get_successors(),
            BasicBlock::Start { successors } => successors.clone(),
            BasicBlock::End => vec![]
        }
    }
}

#[derive(Debug, Clone)]
pub struct GenericBlock {
    pub id: GenericBlockID,
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum BlockID {
    Generic(GenericBlockID),
    Start,
    End
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Binary {
        op: Binop,
        src1: Val,
        src2: Val,
        dst: Ident
    },
    Unary {
        op: Unop,
        inner: Val,
        dst: Ident
    },
    Copy {
        src: Val,
        dst: Ident
    },
    FunctionCall {
        name: Ident,
        args: Vec<Val>,
        dst: Ident,
    }
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Return(Val),
    Jump {
        target: GenericBlockID,
    },
    JumpCond {
        target: GenericBlockID,
        fail: GenericBlockID,
        src1: Val,
        src2: Val,
        cond: Cond
    },
}

impl Terminator {
    pub fn get_successors(&self) -> Vec<BlockID> {
        match self {
            Terminator::Return(_) => vec![BlockID::End],
            Terminator::Jump { target } => vec![BlockID::Generic(*target)],
            Terminator::JumpCond { target, fail, .. } => vec![BlockID::Generic(*target), BlockID::Generic(*fail)],
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
pub enum Cond {
    Equal,
    NotEqual,
    GreaterThan,
    GreaterThanEqual,
    LessThan,
    LessThanEqual
}

#[derive(Debug, Clone, Copy)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    LeftShift,
    RightShift,
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

#[derive(Debug, Clone, Copy)]
pub enum Unop {
    Complement,
    Negate,
}

#[derive(Debug, Clone)]
pub enum Val {
    Num(i32),
    Var(Ident),
}