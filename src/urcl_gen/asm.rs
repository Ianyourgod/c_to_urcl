#![allow(unused)]

use std::fmt::Display;
use crate::Ident;

pub use crate::mir::mir_def::{GenericBlockID, StaticInit};
use crate::urcl_gen::cpu_definitions::{HeaderInfo, CPUDefinition};

#[derive(Debug, Clone)]
pub struct Program<'a, V, CPU>
where 
    V: Display,
    CPU: CPUDefinition
{
    pub cpu: &'a CPU,
    pub top_level_items: Vec<TopLevel<V>>,
}

impl<V, CPU: CPUDefinition> Display for Program<'_, V, CPU>
where
    V: Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let print_num = 
"SBGE ..COMP_BLT_IN..PRINT_NUM..P_N $1 0
OUT %TEXT 45
..COMP_BLT_IN..PRINT_NUM..P_N
ABS $2 $1
OUT %NUMB $2
HLT
";

        let header_info = self.cpu.get_header_info();

        let mut out = format!(
            "{header_info}\n\nMOV $2 SP\nCAL .main\n{print_num}"
        );

        for func in &self.top_level_items {
            out.push_str(&func.to_string());
        }

        f.write_str(&out)
    }
}

#[derive(Debug, Clone)]
pub enum TopLevel<V>
where 
    V: Display
{
    Fn(Function<V>),
    StaticVar {
        name: Ident,
        global: bool,
        init: Vec<StaticInit>,
    },
    StaticConst {
        name: Ident,
        init: StaticInit,
    },
}

impl<V> Display for TopLevel<V>
where 
    V: Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TopLevel::Fn(func) => func.fmt(f),
            TopLevel::StaticVar { name, global: _global, init } => {
                f.write_str(".")?;
                f.write_str(name.as_str())?;
                f.write_str("\n\tDW [")?;
                init.iter().for_each(|i|{
                    f.write_str(&i.to_string());
                    f.write_str(", ");
                });
                f.write_str("]\n")
            },
            TopLevel::StaticConst { name, init } => {
                f.write_str(".")?;
                f.write_str(name.as_str())?;
                f.write_str("\n\tDW [")?;
                f.write_str(&init.to_string())?;
                f.write_str("]\n")
            }
        }
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
    LLod {
        src: V,
        dst: V,
        offset: V,
    },
    LStr {
        src: V,
        offset: V,
        dst: V,
    },
    Jmp {
        label: GenericBlockID,
    },
    Branch {
        label: GenericBlockID,
        src1: V,
        src2: V,
        cond: Cond,
    },
    Lea {
        src: V,
        dst: V,
    },
    Cpy {
        src: V,
        dst: V,
    },
    Comment(String),
    Label(GenericBlockID),
    Push(V),
    Pop(V),
    Call(Ident),
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
    LessThan,
    GreaterThan,
    LessEqual,
    GreaterEqual,
}

impl Cond {
    pub fn to_string_branch(&self) -> String {
        match self {
            Cond::Equal => "BRE",
            Cond::NotEqual => "BNE",
            Cond::SLessThan => "SBRL",
            Cond::SGreaterThan => "SBRG",
            Cond::SLessEqual => "SBLE",
            Cond::SGreaterEqual => "SBGE",
            Cond::LessThan => "BRL",
            Cond::LessEqual => "BLE",
            Cond::GreaterThan => "BRG",
            Cond::GreaterEqual => "BGE",
        }.to_string()
    }

    pub fn to_string_set(&self) -> String {
        match self {
            Cond::Equal => "SETE",
            Cond::NotEqual => "SETNE",
            Cond::SGreaterThan => "SSETG",
            Cond::SGreaterEqual => "SSETGE",
            Cond::SLessThan => "SSETL",
            Cond::SLessEqual => "SSETLE",
            Cond::LessThan => "SETL",
            Cond::LessEqual => "SETLE",
            Cond::GreaterThan => "SETG",
            Cond::GreaterEqual => "SETGE"
        }.to_string()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    SDiv,
    Div,
    Mod,
    And,
    Or,
    Xor,
    LeftShift,
    RightShift,
    Set(Cond),
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
            Binop::SDiv => "SDIV",
            Binop::Div => "DIV",
            Binop::Mod => "MOD",
            Binop::And => "AND",
            Binop::Or => "OR",
            Binop::Xor => "XOR",
            Binop::LeftShift => "BSL",
            Binop::RightShift => "BSR",
            Binop::Set(c) => &c.to_string_set()
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
            Instr::LLod { src, dst, offset } => {
                format!("LLOD {dst} {src} {offset}")
            },
            Instr::LStr { src, dst, offset } => {
                format!("LSTR {dst} {offset} {src}")
            }
            Instr::Push(val) => {
                format!("PSH {val}")
            },
            Instr::Pop(val) => {
                format!("POP {val}")
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
                let cond = cond.to_string_branch();
                format!("{cond} .lbl.{label}. {src1} {src2}")
            },
            Instr::Call(name) => {
                format!("CAL .{name}")
            },
            Instr::Cpy { src, dst } => {
                format!("CPY {dst} {src}")
            }


            Instr::Lea { src, dst } => {
                format!("__LEA {dst} {src}")
            },

            Instr::Comment(contents) => {
                format!("// {contents}")
            }
        };

        f.write_str(&s)
    }
}

#[derive(Debug, Clone)]
pub enum Val {
    Imm(i32), // this is i32 so that we can have i16 and u16 fine in here
    Reg(Reg),
    Label(Ident),
}

impl Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Val::Imm(n) => &n.to_string(),
            Val::Reg(r) => &r.to_string(),
            Val::Label(l) => &(".".to_string() + l.as_str())
        };

        f.write_str(&s)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Reg {
    Normal(u8),
    SP,
}

impl Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Reg::Normal(n) => &format!("${n}"),
            Reg::SP => "SP"
        };

        f.write_str(s)
    }
}

impl Reg {
    pub fn new(n: u8) -> Self {
        Self::Normal(n)
    }

    pub fn val(n: u8) -> Val {
        Val::Reg(Self::new(n))
    }

    pub fn pval(n: u8) -> PVal {
        PVal::Reg(Self::new(n))
    }

    pub fn sp() -> Self { Self::SP }

    pub fn sp_val() -> Val { Val::Reg(Self::sp()) }
    pub fn sp_pval() -> PVal { PVal::Reg(Self::sp()) }

    pub fn bp<T:CPUDefinition>(cpu:&T) -> Self { Self::Normal(cpu.get_base_ptr()) }

    pub fn bp_val<T:CPUDefinition>(cpu:&T) -> Val { Val::Reg(Self::bp(cpu)) }
    pub fn bp_pval<T:CPUDefinition>(cpu:&T) -> PVal { PVal::Reg(Self::bp(cpu)) }
}

#[derive(Debug, Clone)]
pub enum PVal {
    Imm(i32), // this is i32 so that we can have i16 and u16 fine in here
    Reg(Reg),
    Var(Ident),
    Label(Ident),
}

impl Display for PVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            PVal::Imm(n) => &n.to_string(),
            PVal::Reg(r) => &r.to_string(),
            PVal::Var(s) => s.as_str(),
            PVal::Label(l) => &(".".to_string() + l.as_str()),
        };

        f.write_str(&s)
    }
}