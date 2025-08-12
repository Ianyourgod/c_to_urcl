use std::{collections::HashMap, fmt::Display};

use crate::semantic_analysis::type_check::SymbolTable;
pub use crate::Ident;
pub use crate::semantic_analysis::type_check::StaticInit;
pub use crate::ast::{Const, Type};

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

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub top_level: Vec<TopLevel>,
}

impl Program {
    pub fn recalculate_predecessors(&mut self) {
        self.top_level.iter_mut().for_each(|tl| {
            match tl {
                &mut TopLevel::Fn(ref mut f) => f.basic_blocks.recalculate_predecessors(),

                _ => ()
            }
        });
    }
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
    pub basic_blocks: CFG,
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
            preds_map.insert(*id, vec![]);
        }

        for (id, block) in &self.blocks {
            block.get_successors().into_iter().for_each(|s| {
                preds_map.get_mut(&s).unwrap().push(*id);
            })
        }

        for (id, preds) in preds_map.into_iter() {
            self.blocks.get_mut(&id).unwrap().set_predacessors(preds);
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BasicBlock {
    Start {
        successors: Vec<BlockID>,
    },
    End {
        predecessors: Vec<BlockID>,
    },
    Generic(GenericBlock)
}

impl BasicBlock {
    pub fn get_successors(&self) -> Vec<BlockID> {
        match self {
            BasicBlock::Generic(g) => g.terminator.get_successors(),
            BasicBlock::Start { successors } => successors.clone(),
            BasicBlock::End { .. } => vec![]
        }
    }

    pub fn get_predecessors(&self) -> Vec<BlockID> {
        match self {
            BasicBlock::End { predecessors } => predecessors.clone(),
            BasicBlock::Start { .. } => vec![],
            BasicBlock::Generic(b) => b.predecessors.clone(),
        }
    }

    pub fn set_predacessors(&mut self, preds: Vec<BlockID>) {
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
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
    pub predecessors: Vec<BlockID>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum BlockID {
    Generic(GenericBlockID),
    Start,
    End
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
    pub fn get_successors(&self) -> Vec<BlockID> {
        match self {
            Terminator::Return(_) => vec![BlockID::End],
            Terminator::Jump { target } => vec![BlockID::Generic(*target)],
            Terminator::JumpCond { target, fail, .. } => vec![BlockID::Generic(*target), BlockID::Generic(*fail)],
        }
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