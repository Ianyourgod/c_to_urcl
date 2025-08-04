#![allow(unused)]

use std::fmt::Display;
use crate::Ident;

pub use crate::mir::mir_def::{GenericBlockID, StaticInit};

#[derive(Debug, Clone)]
pub struct Program<V>
where 
    V: Display
{
    pub header_info: HeaderInfo,
    pub top_level_items: Vec<TopLevel<V>>,
}

impl<V> Display for Program<V>
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

        let header_info = self.header_info;

        let mut out = format!(
            "{header_info}\n\nIMM $2 0\nIMM $3 0\nCAL .main\n{print_num}"
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
        init: StaticInit,
    }
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
                f.write_str("\n\tDW ")?;
                f.write_str(&init.to_string())?;
                f.write_str("\n")
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


            Instr::Lea { src, dst } => {
                format!("__LEA {dst} {src} // I SHOULD BE DELETED BY RP PASS!!!!")
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

    pub fn bp() -> Self { Self::Normal(2) }

    pub fn bp_val() -> Val { Val::Reg(Self::bp()) }
    pub fn bp_pval() -> PVal { PVal::Reg(Self::bp()) }
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

    pub fn iris() -> Self {
        Self {
            bits: 16,
            min_reg: 26,
            min_heap: 4096,
            min_stack: 16, // idk the stack size of iris... TODO! find the actual stack size
            von_neumann: false // idk if iris can do von neumann but we're just gonna put this as false for now
        }
    }

    pub fn generic_16bit() -> Self {
        Self {
            bits: 16,
            min_reg: 8,
            min_heap: 256, // since *our* stack is on the *heap*, we need some stuff
            min_stack: 16, // ummmm we're just gonna say 16
            von_neumann: false,
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