use std::collections::HashSet;
use std::{collections::HashMap, fmt::Display};

use crate::semantic_analysis::type_check::SymbolTable;
pub use crate::Ident;
pub use crate::semantic_analysis::type_check::StaticInit;
pub use crate::ast::{Const, Type};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum GenericBlockID {
    Generic(u64),
    LoopBreak(u64),
    LoopContinue(u64),
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

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub top_level: Vec<TopLevel>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TopLevel {
    Fn(Function),
    Var(StaticVariable),
    Const {
        name: Ident,
        ty: Type,
        init: StaticInit
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    pub name: Ident,
    #[allow(unused)]
    pub global: bool,
    pub params: Vec<Ident>,
    pub basic_blocks: Option<CFG>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StaticVariable {
    pub name: Ident,
    pub global: bool,
    #[allow(unused)]
    pub ty: Type,
    pub init: Vec<StaticInit>
}

#[derive(Debug, Clone, PartialEq)]
pub struct CFG {
    pub blocks: HashMap<BlockID, BasicBlock>,
}

impl CFG {
    pub fn recalculate_predecessors(&mut self) {
        let mut preds_map = HashMap::new();
        for id in self.blocks.keys().into_iter() {
            preds_map.insert(*id, HashSet::new());
        }

        for (id, block) in &self.blocks {
            block.get_successors().into_iter().for_each(|s| {
                preds_map.get_mut(&s).unwrap().insert(*id);
            })
        }

        for (id, preds) in preds_map.into_iter() {
            self.blocks.get_mut(&id).unwrap().set_predecessors(preds);
        }
    }

    pub fn get_total_instructions(&self) -> usize {
        let mut size = 0;
        for b in self.blocks.values() {
            if let BasicBlock::Generic(block) = b {
                size += block.instructions.len() + 1; // +1 for terminator
            }
        }
        size
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BasicBlock {
    Start {
        successors: HashSet<BlockID>,
    },
    End {
        predecessors: HashSet<BlockID>,
    },
    Generic(GenericBlock)
}

impl BasicBlock {
    // TODO! make this not clone every time
    pub fn get_successors(&self) -> HashSet<BlockID> {
        match self {
            BasicBlock::Generic(g) => {
                let mut s = HashSet::new();
                let (a, b) = g.terminator.term.get_successors();

                s.insert(a);
                if let Some(b) = b { s.insert(b); }

                s
            },
            BasicBlock::Start { successors } => successors.clone(),
            BasicBlock::End { .. } => HashSet::new()
        }
    }

    // TODO! make this not clone every time
    pub fn get_predecessors(&self) -> HashSet<BlockID> {
        match self {
            BasicBlock::End { predecessors } => predecessors.clone(),
            BasicBlock::Start { .. } => HashSet::new(),
            BasicBlock::Generic(b) => b.predecessors.clone(),
        }
    }

    pub fn set_predecessors(&mut self, preds: HashSet<BlockID>) {
        match self {
            BasicBlock::Generic(GenericBlock { predecessors, .. }) |
            BasicBlock::End { predecessors } => *predecessors = preds,

            BasicBlock::Start { .. } => ()
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct GenericBlock {
    pub id: GenericBlockID,
    pub instructions: Vec<BInstruction>,
    pub terminator: BTerminator,
    pub predecessors: HashSet<BlockID>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum BlockID {
    Generic(GenericBlockID),
    Start,
    End
}

pub type InstrID = u64;

#[derive(Debug, Clone, PartialEq)]
pub struct BInstruction {
    pub id: InstrID,
    pub instr: Instruction,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    Binary {
        op: Binop,
        src1: Val,
        src2: Val,
        dst: Ident
    },
    Unary {
        op: Unop,
        src: Val,
        dst: Ident
    },
    Copy {
        src: Val,
        dst: Ident
    },
    FunctionCall {
        name: Ident,
        args: Vec<Val>,
        dst: Option<Ident>,
    },
    GetAddress {
        src: Ident,
        dst: Ident,
    },
    Load {
        src_ptr: Val,
        dst: Ident,
    },
    Store {
        src: Val,
        dst_ptr: Val,
    },
    AddPtr {
        ptr: Val,
        idx: Val,
        scale: i16,
        dst: Ident,
    },
    CopyToOffset {
        src: Val,
        offset: i16,
        dst: Ident,
    },
    CopyFromOffset {
        src: Ident,
        offset: i16,
        dst: Ident,
    }
}

impl Instruction {
    pub fn get_dst(&self) -> Option<&Ident> {
        match self {
            Instruction::Binary { dst, .. } |
            Instruction::AddPtr { dst, .. } |
            Instruction::Unary { dst, .. } |
            Instruction::Copy { dst, .. } |
            Instruction::GetAddress { dst, .. } |
            Instruction::Load { dst, .. } |
            Instruction::CopyToOffset { dst, .. } |
            Instruction::CopyFromOffset { dst, .. } |
            Instruction::FunctionCall { dst: Some(dst), .. } => Some(dst),

            Instruction::Store { .. } | // it has dst_ptr but won't worry about that...
            Instruction::FunctionCall { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BTerminator {
    pub id: InstrID,
    pub term: Terminator,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Return(Option<Val>),
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
    pub fn get_successors(&self) -> (BlockID, Option<BlockID>) {
        match self {
            Terminator::Return(_) => (BlockID::End, None),
            Terminator::Jump { target } => (BlockID::Generic(*target), None),
            Terminator::JumpCond { target, fail, .. } => (BlockID::Generic(*target), Some(BlockID::Generic(*fail))),
        }
    }

    pub fn get_successors_as_vec(&self) -> Vec<BlockID> {
        let s = self.get_successors();

        let mut v = Vec::with_capacity(if s.1.is_some() { 2 } else { 1 });

        v.push(s.0);
        if let Some(s) = s.1 { v.push(s); }

        v
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Cond {
    Equal,
    NotEqual,
    GreaterThan,
    GreaterThanEqual,
    LessThan,
    LessThanEqual
}

#[derive(Debug, Clone, Copy, PartialEq)]
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

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Unop {
    Complement,
    Negate,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Num(Const),
    Var(Ident),
}

impl Val {
    pub fn get_type(&self, symbol_table: &SymbolTable) -> Type {
        match self {
            Val::Num(c) => c.to_type(),
            Val::Var(v) => symbol_table.get(v).unwrap().ty.clone()
        }
    }
}