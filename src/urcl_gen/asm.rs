#![allow(unused)]

use std::fmt::Display;
use crate::mir::mir_def::Ident;

#[derive(Debug, Clone)]
pub struct Program<V>
where 
    V: Display
{
    pub header_info: HeaderInfo,
    pub functions: Vec<Function<V>>,
}

impl<V> Display for Program<V>
where
    V: Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut out = format!(
            "{}\n\nCAL .main\nOUT %NUMB $1\nHLT\n",
            self.header_info
        );

        for func in &self.functions {
            out.push_str(&func.to_string());
        }

        f.write_str(&out)
    }
}

#[derive(Debug, Clone)]
pub struct Function<V>
where
    V: Display
{
    pub name: Ident,
    pub instructions: Vec<Instr<V>>,
}

impl<V> Display for Function<V>
where
    V: Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut output = format!(".{}\n", self.name);
        for instr in &self.instructions {
            output.push_str(&format!("\t{}\n", instr));
        }
        f.write_str(&output)
    }
}

#[derive(Debug, Clone)]
pub enum Instr<V>
where
    V: Display
{
    Binary {
        binop: Binop,
        src1: V,
        src2: V,
        dst: V,
    },
    Unary {
        unop: Unop,
        src: V,
        dst: V,
    },
    Mov {
        src: V,
        dst: V,
    },
    Lod {
        src: Reg,
        dst: Reg,
    },
    Str {
        src: V,
        dst: Reg,
    },
    Jmp {
        label: u32,
    },
    Branch {
        label: u32,
        src1: V,
        src2: V,
        cond: Cond,
    },
    Label(u32),
    Push(V),
    Pop(Reg),
    Ret,
}

#[derive(Debug, Clone, Copy)]
pub enum Cond {
    SLessThan,
    SGreaterThan,
    SLessEqual,
    SGreaterEqual,
    Equal,
    NotEqual,
}

impl Display for Cond {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Cond::Equal => "BRE",
            Cond::NotEqual => "BNE",
            Cond::SLessThan => "SBRL",
            Cond::SGreaterThan => "SBRG",
            Cond::SLessEqual => "SBLE",
            Cond::SGreaterEqual => "SBGE",
        };

        f.write_str(s)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Xor,
    LeftShift,
    RightShift,
}

#[derive(Debug, Clone, Copy)]
pub enum Unop {
    BitwiseNot,
    Negate,
}

impl Display for Unop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Unop::BitwiseNot => "NOT",
            Unop::Negate => "NEG"
        };

        f.write_str(s)
    }
}

impl Display for Binop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Binop::Add => "ADD",
            Binop::Sub => "SUB",
            Binop::Mul => "MLT",
            Binop::Div => "DIV",
            Binop::And => "AND",
            Binop::Or => "OR",
            Binop::Xor => "XOR",
            Binop::LeftShift => "BSL",
            Binop::RightShift => "BSR",
        };

        f.write_str(s)
    }
}

impl<V> Display for Instr<V>
where
    V: Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Instr::Binary { binop, src1, src2, dst } => {
                format!("{binop} {dst} {src1} {src2}")
            },
            Instr::Unary { unop, src, dst } => {
                format!("{unop}, {dst} {src}")
            }
            Instr::Mov { src, dst } => {
                format!("MOV {dst} {src}")
            },
            Instr::Lod { src, dst } => {
                format!("LOD {dst} {src}")
            },
            Instr::Str { src, dst } => {
                format!("STR {dst} {src}")
            }
            Instr::Push(val) => {
                format!("PSH {val}")
            },
            Instr::Pop(reg) => {
                format!("POP {reg}")
            },
            Instr::Ret => {
                format!("RET")
            },
            Instr::Label(label) => {
                format!(".lbl.{}.", label)
            },
            Instr::Jmp { label } => {
                format!("JMP .lbl.{}.", label)
            },
            Instr::Branch { label, src1, src2, cond } => {
                format!("{cond} .lbl.{label}. {src1} {src2}")
            }
        };

        f.write_str(&s)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Val {
    Imm(i32),
    Reg(Reg),
}

impl Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Val::Imm(n) => n.to_string(),
            Val::Reg(r) => r.to_string(),
        };

        f.write_str(&s)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Reg(u8);

impl Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!("${}", self.0))
    }
}

impl Reg {
    pub fn new(n: u8) -> Self {
        Self(n)
    }

    pub fn val(n: u8) -> Val {
        Val::Reg(Self::new(n))
    }

    pub fn pval(n: u8) -> PVal {
        PVal::Reg(Self::new(n))
    }
}

#[derive(Debug, Clone)]
pub enum PVal {
    Imm(i32),
    Reg(Reg),
    Var(Ident),
}

impl Display for PVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            PVal::Imm(n) => n.to_string(),
            PVal::Reg(r) => r.to_string(),
            PVal::Var(s) => (**s).clone(),
        };

        f.write_str(&s)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct HeaderInfo {
    pub bits: u8,
    pub min_reg: u8,
    pub min_heap: u32,
    pub min_stack: u32,
    pub von_neumann: bool,
}

impl HeaderInfo {
    pub fn default() -> Self {
        Self {
            bits: 8,
            min_reg: 8,
            min_heap: 16,
            min_stack: 8,
            von_neumann: false
        }
    }
}

impl Display for HeaderInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = format!(
            "BITS == {}\nMINREG {}\nMINHEAP {}\nRUN {}\nMINSTACK {}",
            self.bits,
            self.min_reg,
            self.min_heap,
            if self.von_neumann { "RAM" } else { "ROM" },
            self.min_stack
        );

        f.write_str(&s)
    }
}