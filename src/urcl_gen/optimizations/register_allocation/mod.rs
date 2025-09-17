pub mod cfg;

use std::collections::{HashMap, HashSet};

use crate::{semantic_analysis::type_check::{SymbolTable, TypeTable}, urcl_gen::{asm, convert::ConvInfo, cpu_definitions::CPUDefinition}};

type Instrs = Vec<asm::Instr<asm::PVal>>;

pub fn allocate_registers<CPU: CPUDefinition>(instructions: Instrs, cpu: &CPU, statics_and_aliased: &HashSet<asm::Ident>, conv_info: &ConvInfo, fn_name: &asm::Ident, symbol_table: &SymbolTable, type_table: &TypeTable) -> (Instrs, HashSet<asm::Reg>) {
    let mut i_graph = InterferenceGraph::new(&instructions, statics_and_aliased, cpu, conv_info, fn_name, symbol_table, type_table);

    i_graph.color();

    let (reg_map, callee_saved) = create_register_map(i_graph, cpu);

    (replace_pseudos(instructions, reg_map), callee_saved)
}

type RegisterMap = HashMap<asm::Ident, asm::Reg>;

fn create_register_map<CPU: CPUDefinition>(graph: InterferenceGraph<CPU>, cpu: &CPU) -> (RegisterMap, HashSet<asm::Reg>) {
    let mut color_map = HashMap::new();

    for node in graph.graph.values() {
        match node.id {
            cfg::Reg::P(_) => continue,
            cfg::Reg::R(r) => {
                color_map.insert(node.color.unwrap(), r);
            }
        }
    }

    let mut register_map = RegisterMap::new();
    let mut callee_saved_regs = HashSet::new();

    let callee_saved = cpu.get_callee_saved();

    for node in graph.graph.values() {
        match node.id {
            cfg::Reg::R(_) => continue,

            cfg::Reg::P(ref p) => {
                if let Some(c) = node.color {
                    let reg = color_map.get(&c).unwrap();
                    register_map.insert(p.clone(), *reg);

                    if callee_saved.contains(reg) {
                        callee_saved_regs.insert(*reg);
                    }
                }
            }
        }
    }

    (register_map, callee_saved_regs)
}

struct InterferenceGraph<'a, CPU: CPUDefinition> {
    graph: HashMap<cfg::Reg, Node>,
    cpu: &'a CPU
}

struct Node {
    id: cfg::Reg,
    neighbors: Vec<cfg::Reg>,
    spill_cost: f64,
    color: Option<u32>,
    pruned: bool,
}

impl Node {
    pub fn new(
        id: cfg::Reg,
        neighbors: Vec<cfg::Reg>,
        spill_cost: f64,
        color: Option<u32>,
        pruned: bool
    ) -> Self {
        Self {
            id,
            neighbors,
            spill_cost,
            color,
            pruned
        }
    }
}

impl<'a, CPU: CPUDefinition> InterferenceGraph<'a, CPU> {
    pub fn new(instructions: &Instrs, statics_and_aliased: &HashSet<asm::Ident>, cpu: &'a CPU, conv_info: &ConvInfo, fn_name: &asm::Ident, symbol_table: &SymbolTable, type_table: &TypeTable) -> Self {
        let mut ig = Self::build(instructions, cpu, statics_and_aliased, symbol_table, type_table);

        ig.add_spill_costs(instructions);

        let cfg = cfg::CFG::construct_from_instrs(instructions, cpu, conv_info, fn_name);

        ig.add_edges(cfg);

        ig
    }

    fn default(cpu: &'a CPU) -> Self {
        Self {
            graph: HashMap::new(),
            cpu
        }
    }

    fn build(instructions: &Instrs, cpu: &'a CPU, statics_and_aliased: &HashSet<asm::Ident>, symbol_table: &SymbolTable, type_table: &TypeTable) -> Self {
        // add all the registers
        let mut graph = Self::default(cpu);

        let gen_use = cpu.get_gen_use_regs();

        let all_regs = gen_use.clone();
        for reg in gen_use {
            let all_regs = all_regs.clone().into_iter()
                .filter_map(|r| {
                    if reg == r {
                        return None;
                    }

                    Some(cfg::Reg::R(r))
                })
                .collect();

            graph.graph.insert(cfg::Reg::R(reg), Node::new(
                cfg::Reg::R(reg),
                all_regs,
                0.0,
                None,
                false,
            ));
        }

        graph.add_pseudos(instructions, statics_and_aliased, symbol_table, type_table);

        graph
    }

    fn add_pseudos(&mut self, instructions: &Instrs, statics_and_aliased: &HashSet<asm::Ident>, symbol_table: &SymbolTable, type_table: &TypeTable) {
        let s = symbol_table;
        let t = type_table;

        for instr in instructions.iter() {
            match instr {
                asm::Instr::Branch { src1, src2, .. } |
                asm::Instr::Cpy { src: src1, dst: src2 } |
                asm::Instr::Lea { src: src1, dst: src2 } |
                asm::Instr::Unary { src: src1, dst: src2, .. } |
                asm::Instr::Mov { src: src1, dst: src2 } => {
                    self.add_op(src1, statics_and_aliased, s, t);
                    self.add_op(src2, statics_and_aliased, s, t);
                },
                asm::Instr::LStr { src: src1, offset: src2, dst: src3 } |
                asm::Instr::LLod { src: src1, dst: src2, offset: src3 } |
                asm::Instr::Binary { src1, src2, dst: src3, .. } => {
                    self.add_op(src1, statics_and_aliased, s, t);
                    self.add_op(src2, statics_and_aliased, s, t);
                    self.add_op(src3, statics_and_aliased, s, t);
                },
                asm::Instr::Push(src) |
                asm::Instr::Pop(src) => {
                    self.add_op(src, statics_and_aliased, s, t);
                }


                asm::Instr::Ret |
                asm::Instr::Label(_) |
                asm::Instr::Call(_) |
                asm::Instr::Comment(_) |
                asm::Instr::Jmp { .. } => ()
            }
        }
    }

    fn add_op(&mut self, val: &asm::PVal, statics_and_aliased: &HashSet<asm::Ident>, symbol_table: &SymbolTable, type_table: &TypeTable) {
        match val {
            asm::PVal::Var(v) if !statics_and_aliased.contains(v) => {
                if let Some(e) = symbol_table.get(v) && e.ty.size(type_table) == 1 {

                }

                self.graph.insert(cfg::Reg::P(v.clone()), Node::new(
                    cfg::Reg::P(v.clone()),
                    Vec::new(),
                    0.0,
                    None,
                    false
                ));
            },
            _ => ()
        }
    }

    fn add_spill_costs(&mut self, instructions: &Instrs) {
        // TODO! identify loops. use loop depth as an inference for how often an instruction gets executed
        

        // count appearances of each pseudo
        let mut appearances = HashMap::new();
        
        fn add_appear_p<'b>(appearances: &mut HashMap<&'b asm::Ident, u64>, r: &'b asm::Ident) {
            let e = appearances.entry(r).or_insert(0);

            *e += 1;
        }

        fn add_appear<'b>(appearances: &mut HashMap<&'b asm::Ident, u64>, r: &'b asm::PVal) {
            match r {
                asm::PVal::Var(v) => add_appear_p(appearances, v),
                _ => ()
            }
        }
        
        for instr in instructions {
            match instr {
                asm::Instr::LLod { src: src1, dst: src2, offset: dst } |
                asm::Instr::LStr { src: src1, dst: src2, offset: dst } |
                asm::Instr::Binary { src1, src2, dst, .. } => {
                    add_appear(&mut appearances, src1);
                    add_appear(&mut appearances, src2);
                    add_appear(&mut appearances, dst);
                },
                asm::Instr::Branch { src1: src, src2: dst, .. } |
                asm::Instr::Lea { src, dst } |
                asm::Instr::Unary { src, dst, .. } |
                asm::Instr::Cpy { src, dst } |
                asm::Instr::Mov { src, dst } => {
                    add_appear(&mut appearances, src);
                    add_appear(&mut appearances, dst);
                },
                asm::Instr::Push(src) |
                asm::Instr::Pop(src) => {
                    add_appear(&mut appearances, src);
                }

                asm::Instr::Call(_) |
                asm::Instr::Jmp { .. } | asm::Instr::Label(_) |
                asm::Instr::Comment(_) | asm::Instr::Ret => ()
            }
        }

        for node in self.graph.values_mut() {
            let p = match node.id {
                cfg::Reg::P(ref p) => p,
                cfg::Reg::R(_) => {
                    node.spill_cost = f64::INFINITY;
                    continue;
                }
            };

            let ap = *appearances.get(p).unwrap_or(&0);

            node.spill_cost = ap as f64;
        }
    }

    fn color(&mut self) {
        let remaining = self.graph.values().filter(|n| {
            !n.pruned
        }).collect::<Vec<_>>();

        if remaining.is_empty() {
            return;
        }

        let k = self.cpu.get_gen_use_regs().len();

        let chosen_node = remaining.into_iter().find(|node| {
            let deg = node.neighbors.iter().filter(|n| {
                !self.graph.get(n).unwrap().pruned
            }).collect::<Vec<_>>().len();

            deg < k
        }).map(|n|n);

        let remaining = self.graph.values().filter(|n| {
            !n.pruned
        }).collect::<Vec<_>>();

        let chosen_node = chosen_node.unwrap_or_else(|| {
            let mut best_metric = f64::INFINITY;

            let mut current_chosen = None;

            for node in remaining.iter() {
                let deg = node.neighbors.iter().filter(|n| {
                    !self.graph.get(n).unwrap().pruned
                }).collect::<Vec<_>>().len();

                let spill_metric = node.spill_cost / deg as f64;

                if spill_metric < best_metric {
                    current_chosen = Some(&node.id);
                    best_metric = spill_metric;
                }
            }

            if let Some(c) = current_chosen {
                self.graph.get(c).unwrap()
            } else {
                unreachable!()
            }
        });

        let ch_id = chosen_node.id.clone();

        let chosen_node = self.graph.get_mut(&ch_id).unwrap();

        (*chosen_node).pruned = true;

        self.color();

        let chosen_node = self.graph.get(&ch_id).unwrap();

        let mut colors = (0..k).map(|i|Some(i)).collect::<Vec<_>>();

        for n in chosen_node.neighbors.iter() {
            let n = self.graph.get(&n).unwrap();

            if let Some(c) = n.color {
                *colors.get_mut(c as usize).unwrap() = None;
            }
        }

        let chosen_node = self.graph.get_mut(&ch_id).unwrap();

        if let Some(c) = colors.iter().rev().find_map(|c|*c) {
            if let cfg::Reg::R(r) = chosen_node.id && self.cpu.get_callee_saved().contains(&r) {
                chosen_node.color = Some(c as u32);
            } else {
                let c = colors.iter().find_map(|c|*c).unwrap();
                chosen_node.color = Some(c as u32);
            }
        }
    }

    fn add_edges(&mut self, cfg: cfg::CFG<CPU>) {
        for node in cfg.blocks.iter() {
            let id = node.get_id();

            let node = match node {
                cfg::BasicBlock::End { .. } | cfg::BasicBlock::Start { .. } => continue,
                cfg::BasicBlock::Generic(g) => g
            };

            for (i, instr) in node.instructions.iter().enumerate() {
                let (_, updated) = cfg.find_used_and_updated(instr);

                let live_regs = cfg.get_instr_annotation(&(id, i)).unwrap();

                for r in live_regs {
                    if let asm::Instr::Mov { src, .. } = instr && Some(r) == cfg::CFG::<CPU>::pval_to_r(src).as_ref() {
                        continue;
                    }

                    for u in updated.iter() {
                        if r != u && self.graph.contains_key(&u) && self.graph.contains_key(r) {
                            self.add_edge(r, u);
                        }
                    }
                }
            }
        }
    }

    fn add_edge(&mut self, l: &cfg::Reg, r: &cfg::Reg) {
        let ln = self.graph.get_mut(l).unwrap();
        
        ln.neighbors.push(r.clone());

        let rn = self.graph.get_mut(r).unwrap();

        rn.neighbors.push(l.clone());
    }
}

fn replace_pseudos(instructions: Instrs, register_map: RegisterMap) -> Instrs {
    instructions.into_iter().filter_map(|instr| {
        Some(match instr {
            asm::Instr::Cpy { src, dst } => {
                let src = replace_op(src, &register_map);
                let dst = replace_op(dst, &register_map);
                
                if src == dst {
                    return None;
                }

                asm::Instr::Cpy { src, dst }
            },
            asm::Instr::Mov { src, dst } => {
                let src = replace_op(src, &register_map);
                let dst = replace_op(dst, &register_map);
                
                if src == dst {
                    return None;
                }

                asm::Instr::Mov { src, dst }
            },
            asm::Instr::Binary { binop, src1, src2, dst } => {
                let src1 = replace_op(src1, &register_map);
                let src2 = replace_op(src2, &register_map);
                let dst = replace_op(dst, &register_map);

                asm::Instr::Binary { binop, src1, src2, dst }
            },
            asm::Instr::Unary { unop, src, dst } => {
                let src = replace_op(src, &register_map);
                let dst = replace_op(dst, &register_map);

                asm::Instr::Unary { unop, src, dst }
            },
            asm::Instr::Branch { label, src1, src2, cond } => {
                let src1 = replace_op(src1, &register_map);
                let src2 = replace_op(src2, &register_map);

                asm::Instr::Branch { label, src1, src2, cond }
            },
            asm::Instr::LLod { src, dst, offset } => {
                let src = replace_op(src, &register_map);
                let dst = replace_op(dst, &register_map);

                asm::Instr::LLod { src, dst, offset }
            },
            asm::Instr::LStr { src, dst, offset } => {
                let src = replace_op(src, &register_map);
                let dst = replace_op(dst, &register_map);

                asm::Instr::LStr { src, dst, offset }
            },
            asm::Instr::Lea { src, dst } => {
                let src = replace_op(src, &register_map);
                let dst = replace_op(dst, &register_map);

                asm::Instr::Lea { src, dst }
            },
            asm::Instr::Push(src) => {
                let src = replace_op(src, &register_map);

                asm::Instr::Push(src)
            },
            asm::Instr::Pop(dst) => {
                let dst = replace_op(dst, &register_map);

                asm::Instr::Pop(dst)
            },

            asm::Instr::Ret |
            asm::Instr::Jmp { .. } |
            asm::Instr::Comment(_) |
            asm::Instr::Label(_) |
            asm::Instr::Call(_) => instr
        })
    }).collect()
}

fn replace_op(op: asm::PVal, register_map: &RegisterMap) -> asm::PVal {
    match op {
        asm::PVal::Var(v) => {
            if let Some(r) = register_map.get(&v) {
                asm::PVal::Reg(*r)
            } else {
                asm::PVal::Var(v)
            }
        },
        asm::PVal::Imm(_) | asm::PVal::Label(_) | asm::PVal::Reg(_) => op
    }
}