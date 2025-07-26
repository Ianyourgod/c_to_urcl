use std::{collections::HashMap, rc::Rc};

pub type Ident = Rc<String>;
pub type GenericBlockID = u32;

#[derive(Debug, Clone)]
pub struct Program {
    pub functions: Vec<Function>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Ident,
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
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    LeftShift,
    RightShift,
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