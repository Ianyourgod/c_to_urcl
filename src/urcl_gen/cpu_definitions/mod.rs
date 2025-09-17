use std::fmt::Display;

use crate::urcl_gen::asm;

#[derive(Debug, Clone, Copy)]
pub struct HeaderInfo {
    pub bits: u8,
    pub min_reg: u8,
    pub min_heap: u32,
    pub min_stack: u32,
    pub von_neumann: bool,
}

impl HeaderInfo {
    #[allow(unused)]
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
            min_stack: 256, // idk the stack size of iris... TODO! find the actual stack size
            von_neumann: false // idk if iris can do von neumann but we're just gonna put this as false for now
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

pub trait CPUDefinition {
    fn get_header_info(&self) -> HeaderInfo;
    fn get_base_ptr(&self) -> asm::Reg;
    fn get_param_regs(&self) -> Vec<asm::Reg>;
    fn get_caller_saved(&self) -> Vec<asm::Reg>;
    // Always include bp and sp
    #[allow(unused)]
    fn get_callee_saved(&self) -> Vec<asm::Reg>;
    fn get_temp_regs(&self) -> (asm::Reg, asm::Reg, asm::Reg);
    fn get_temp_dst_reg(&self) -> asm::Reg;
    fn get_gen_use_regs(&self) -> Vec<asm::Reg>;
    fn get_ret_reg(&self) -> asm::Reg;
}

pub struct IRIS;

#[inline]
fn _rg(n: u8) -> asm::Reg {
    asm::Reg::Normal(n)
}

impl CPUDefinition for IRIS {
    fn get_header_info(&self) -> HeaderInfo {
        HeaderInfo::iris()
    }

    // random, not defined anywhere else
    fn get_base_ptr(&self) -> asm::Reg {
        _rg(2)
    }

    fn get_param_regs(&self) -> Vec<asm::Reg> {
        vec![_rg(3), _rg(4), _rg(5), _rg(6)]
    }

    fn get_caller_saved(&self) -> Vec<asm::Reg> {
        vec![
            _rg(3), _rg(4), _rg(5), _rg(6),
            _rg(7), _rg(8), _rg(9),
            _rg(16), _rg(17), _rg(18), _rg(19), _rg(20), _rg(21), _rg(22), _rg(23), _rg(24), _rg(25), _rg(26)
        ]
    }

    fn get_callee_saved(&self) -> Vec<asm::Reg> {
        vec![
            self.get_base_ptr(),
            asm::Reg::SP,
            _rg(10), _rg(11), _rg(12), _rg(13), _rg(14), _rg(15)
        ]
    }

    fn get_temp_regs(&self) -> (asm::Reg, asm::Reg, asm::Reg) {
        (_rg(7), _rg(8), _rg(9))
    }

    fn get_temp_dst_reg(&self) -> asm::Reg {
        _rg(7)
    }

    fn get_gen_use_regs(&self) -> Vec<asm::Reg> {
        vec![
            asm::Reg::Normal(1),
            asm::Reg::Normal(3),
            asm::Reg::Normal(4),
            asm::Reg::Normal(5),
            asm::Reg::Normal(6),
            asm::Reg::Normal(10),
            asm::Reg::Normal(11),
            asm::Reg::Normal(12),
            asm::Reg::Normal(13),
            asm::Reg::Normal(14),
            asm::Reg::Normal(15),
            asm::Reg::Normal(16),
            asm::Reg::Normal(17),
            asm::Reg::Normal(18),
            asm::Reg::Normal(19),
            asm::Reg::Normal(20),
            asm::Reg::Normal(21),
            asm::Reg::Normal(22),
            asm::Reg::Normal(23),
            asm::Reg::Normal(24),
            asm::Reg::Normal(25),
            asm::Reg::Normal(26),
            
        ]
    }

    fn get_ret_reg(&self) -> asm::Reg {
        asm::Reg::Normal(1)
    }
}

impl IRIS {
    pub fn new() -> Self {
        Self
    }
}