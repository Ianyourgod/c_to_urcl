use std::fmt::Display;

use crate::mir::mir_def;

impl Display for mir_def::Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for tl in self.top_level.iter() {
            match tl {
                mir_def::TopLevel::Fn(func) => func.fmt(f),
                mir_def::TopLevel::Const { name, ty, init } => {
                    f.write_str(&format!(".{} - {:?} = {:?}", name, ty, init))
                },
                mir_def::TopLevel::Var(v) => {
                    f.write_str(&format!(".{} - {:?} = {:?}", v.name, v.ty, v.init))
                }
            }?
        }

        Ok(())
    }
}

// TODO! lookup types in symbol table
impl Display for mir_def::Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)?;
        f.write_str("(")?;
        for param in self.params.iter() {
            f.write_str(&param)?;
        }
        f.write_str("):")?;
        self.basic_blocks.fmt(f)
    }
}

impl Display for mir_def::CFG {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let start = self.blocks.get(&mir_def::BlockID::Start).unwrap().get_successors();

        if start.len() > 0 {
            let mut start = start;
            let start = start.pop().unwrap();

            f.write_str("\n\tJMP ")?;
            f.write_str(&format!("{:?}\n", start))?;
        }

        for block in self.blocks.values() {
            match block {
                mir_def::BasicBlock::Generic(block) => block.fmt(f)?,
                _ => ()
            }
        }

        Ok(())
    }
}

impl Display for mir_def::GenericBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\t")?;
        self.id.fmt(f)?;
        f.write_str(":\n")?;
        for inst in self.instructions.iter() {
            f.write_str("\t\t")?;
            inst.instr.fmt(f)?;
            f.write_str("\n")?;
        }
        f.write_str("\t\t")?;
        self.terminator.term.fmt(f)?;
        f.write_str("\n")?;
        Ok(())
    }
}

impl Display for mir_def::Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            mir_def::Instruction::Copy { src, dst } => {
                f.write_str("COPY ")?;
                src.fmt(f)?;
                f.write_str(" -> ")?;
                dst.fmt(f)
            },
            mir_def::Instruction::Binary { op, src1, src2, dst } => {
                op.fmt(f)?;
                f.write_str(" ")?;
                src1.fmt(f)?;
                f.write_str(" ")?;
                src2.fmt(f)?;
                f.write_str(" -> ")?;
                dst.fmt(f)
            },
            mir_def::Instruction::Unary { op, src, dst } => {
                op.fmt(f)?;
                f.write_str(" ")?;
                src.fmt(f)?;
                f.write_str(" -> ")?;
                dst.fmt(f)
            },
            mir_def::Instruction::AddPtr { ptr, idx, scale, dst } => {
                f.write_str("ADDPTR ")?;
                ptr.fmt(f)?;
                f.write_str("[")?;
                idx.fmt(f)?;
                f.write_str(&format!(" + {scale}"))?;
                f.write_str("] -> ")?;
                dst.fmt(f)
            },
            mir_def::Instruction::CopyFromOffset { src, offset, dst } => {
                src.fmt(f)?;
                f.write_str(&format!("[{offset}] -> "))?;
                dst.fmt(f)
            },
            mir_def::Instruction::CopyToOffset { src, offset, dst } => {
                src.fmt(f)?;
                f.write_str(" -> ")?;
                dst.fmt(f)?;
                f.write_str(&format!("[{offset}]"))
            },
            mir_def::Instruction::GetAddress { src, dst } => {
                f.write_str("&")?;
                src.fmt(f)?;
                f.write_str(" -> ")?;
                dst.fmt(f)
            },
            mir_def::Instruction::Load { src_ptr, dst } => {
                f.write_str("*")?;
                src_ptr.fmt(f)?;
                f.write_str(" -> ")?;
                dst.fmt(f)
            },
            mir_def::Instruction::Store { src, dst_ptr } => {
                f.write_str("*")?;
                dst_ptr.fmt(f)?;
                f.write_str(" = ")?;
                src.fmt(f)
            },
            mir_def::Instruction::FunctionCall { name, args, dst } => {
                f.write_str(&name)?;
                f.write_str("(")?;
                for arg in args.iter() {
                    arg.fmt(f)?;
                    f.write_str(", ")?;
                }
                f.write_str(")")?;
                if let Some(dst) = dst {
                    f.write_str(" -> ")?;
                    dst.fmt(f)?;
                }

                Ok(())
            }
        }
    }
}

impl Display for mir_def::Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            mir_def::Val::Num(n) => f.write_str(&(n.clone().as_i32().to_string())),
            mir_def::Val::Var(v) => f.write_str(&v)
        }
    }
}

impl Display for mir_def::Binop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            mir_def::Binop::Add => "ADD",
            mir_def::Binop::Sub => "SUB",
            mir_def::Binop::Mul => "MUL",
            mir_def::Binop::Div => "DIV",
            mir_def::Binop::Mod => "MOD",
            mir_def::Binop::BitwiseAnd => "AND",
            mir_def::Binop::BitwiseOr => "OR",
            mir_def::Binop::BitwiseXor => "XOR",
            mir_def::Binop::LeftShift => "SHL",
            mir_def::Binop::RightShift => "SHR",
            mir_def::Binop::Equal => "EQ",
            mir_def::Binop::NotEqual => "NEQ",
            mir_def::Binop::GreaterThan => "GT",
            mir_def::Binop::GreaterEqual => "GTE",
            mir_def::Binop::LessThan => "LT",
            mir_def::Binop::LessEqual => "LTE",
        })
    }
}

impl Display for mir_def::Unop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            mir_def::Unop::Negate => "NEG",
            mir_def::Unop::Complement => "NOT",
        })
    }
}

impl Display for mir_def::Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            mir_def::Terminator::Jump { target } => {
                f.write_str("JMP ")?;
                target.fmt(f)
            },
            mir_def::Terminator::JumpCond { target, fail, src1, src2, cond } => {
                f.write_str("BRH ")?;
                cond.fmt(f)?;
                f.write_str(" ")?;
                target.fmt(f)?;
                f.write_str(" ")?;
                src1.fmt(f)?;
                f.write_str(" ")?;
                src2.fmt(f)?;
                f.write_str(" ELSE ")?;
                fail.fmt(f)
            },
            mir_def::Terminator::Return(v) => {
                f.write_str("RETURN ")?;
                if let Some(v) = v { v.fmt(f)?; }
                Ok(())
            }
        }
    }
}

impl Display for mir_def::Cond {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            mir_def::Cond::Equal => "EQ",
            mir_def::Cond::NotEqual => "NEQ",
            mir_def::Cond::GreaterThan => "GT",
            mir_def::Cond::GreaterThanEqual => "GTE",
            mir_def::Cond::LessThan => "LT",
            mir_def::Cond::LessThanEqual => "LTE",
        })
    }
}