use std::fmt::Display;

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
    fn get_base_ptr(&self) -> u8;
}

pub struct IRIS;

impl CPUDefinition for IRIS {
    fn get_header_info(&self) -> HeaderInfo {
        HeaderInfo::iris()
    }

    // random, not defined anywhere else
    fn get_base_ptr(&self) -> u8 {
        2
    }
}

impl IRIS {
    pub fn new() -> Self {
        Self
    }
}