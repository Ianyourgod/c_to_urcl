use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::mir::mir_def;
use crate::ast::{self, TypedExpr};
use crate::semantic_analysis::type_check::{IdentifierAttrs, InitialValue, SwitchCases, SymbolTable, SymbolTableEntry, TypeTable};

#[derive(Debug)]
pub struct Generator<'s> {
    tmp_count: u64,
    instr_id: u64,
    symbol_table: &'s mut SymbolTable,
    type_table: &'s TypeTable,
    switch_cases: SwitchCases,
}

impl<'s> Generator<'s> {
    pub fn new(symbol_table: &'s mut SymbolTable, type_table: &'s TypeTable, switch_cases: SwitchCases) -> Self {
        Self {
            tmp_count: 0,
            instr_id: 0,
            symbol_table,
            type_table,
            switch_cases,
        }
    }

    pub fn generate(mut self, ast: ast::Program<TypedExpr>) -> (mir_def::Program, u64, u64) {
        let mut top_level: Vec<mir_def::TopLevel> = Vec::new();
        
        for f in ast.top_level_items {
            let f = if let ast::Declaration::Fn(f) = f { f } else { continue; };

            if let Some(f) = self.generate_function(f) {
                top_level.push(mir_def::TopLevel::Fn(f));
            }
        }

        // now traverse the symbol table
        for (name, entry) in &self.symbol_table.table {
            match entry.attrs {
                IdentifierAttrs::Static { ref init, global } => {
                    match init {
                        InitialValue::Initial(n) => { top_level.push(mir_def::TopLevel::Var(mir_def::StaticVariable {
                            name: name.clone(),
                            global,
                            init: n.clone(),
                            ty: entry.ty.clone(),
                        })); },
                        InitialValue::Tentative => { top_level.push(mir_def::TopLevel::Var(mir_def::StaticVariable {
                            name: name.clone(),
                            global,
                            init: match entry.ty {
                                mir_def::Type::Void       |
                                mir_def::Type::Fn { .. } => unreachable!(),

                                mir_def::Type::Int => vec![mir_def::StaticInit::IntInit(0)],
                                mir_def::Type::Enum(_) |
                                mir_def::Type::Pointer(_) |
                                mir_def::Type::UInt => vec![mir_def::StaticInit::UIntInit(0)],
                                mir_def::Type::Char => vec![mir_def::StaticInit::CharInit(0)],
                                mir_def::Type::UChar => vec![mir_def::StaticInit::UCharInit(0)],
                                mir_def::Type::Array(ref inner_ty, len) => {
                                    (0..len).into_iter().flat_map(|_| {
                                        let size = inner_ty.size(self.type_table);
                                        std::iter::repeat(mir_def::StaticInit::ZeroInit).take(size as usize)
                                    }).collect()
                                },
                                mir_def::Type::Union(ref name) |
                                mir_def::Type::Struct(ref name) => {
                                    let decl = self.type_table.entries.get(name).unwrap();
                                    decl.members.values().flat_map(|member| {
                                        let size = member.ty.size(self.type_table);
                                        std::iter::repeat_n(mir_def::StaticInit::ZeroInit, size as usize)
                                    }).collect()
                                }
                            },
                            ty: entry.ty.clone(),
                        })); },
                        InitialValue::NoInit => continue,
                    }
                },
                IdentifierAttrs::Constant { ref init } => {
                    top_level.push(mir_def::TopLevel::Const {
                        name: name.clone(),
                        ty: entry.ty.clone(),
                        init: init.clone()
                    });
                },
                _ => continue,
            }
        }

        (mir_def::Program { 
            top_level
        }, self.instr_id, self.tmp_count)
    }

    fn generate_function(&mut self, function: ast::FunctionDecl<TypedExpr>) -> Option<mir_def::Function> {
        let mut tmp_tmp_count = self.tmp_count;
        let mut tmp_instr_id = self.instr_id;
        let fn_gen = FunctionGenerator::new(&mut tmp_tmp_count, &mut tmp_instr_id, self.type_table, &mut self.switch_cases);

        let f = fn_gen.generate(self.symbol_table, function);

        self.tmp_count = tmp_tmp_count;
        self.instr_id = tmp_instr_id;

        f
    }
}

#[derive(Debug, Clone)]
enum ExprResult {
    Plain(mir_def::Val),
    DerefedPtr(mir_def::Val),
    SubObject {
        base: mir_def::Ident,
        offset: u16,
    }
}

struct FunctionGenerator<'l> {
    tmp_count: &'l mut u64,
    instr_id: &'l mut u64,
    cfg: mir_def::CFG,
    current_block: mir_def::GenericBlock,
    type_table: &'l TypeTable,
    switch_cases: &'l mut SwitchCases,
}

impl<'l> FunctionGenerator<'l> {
    pub fn new(tmp_count: &'l mut u64, instr_id: &'l mut u64, type_table: &'l TypeTable, switch_cases: &'l mut SwitchCases) -> Self {
        let mut cfg = mir_def::CFG {
            blocks: HashMap::new()
        };

        *tmp_count += 1;
        let n = *tmp_count;
        let id = mir_def::GenericBlockID::Generic(n);

        let start_successors = HashSet::from([mir_def::BlockID::Generic(id)]);
        cfg.blocks.insert(mir_def::BlockID::Start, mir_def::BasicBlock::Start { successors: start_successors });
        cfg.blocks.insert(mir_def::BlockID::End, mir_def::BasicBlock::End { predecessors: HashSet::new() });

        let term_id = *instr_id;
        *instr_id += 1;

        Self {
            tmp_count,
            instr_id,
            cfg,
            current_block: Self::temp_block_ns(id, term_id),
            type_table,
            switch_cases,
        }
    }

    fn temp_block_ns(id: mir_def::GenericBlockID, instr_id: u64) -> mir_def::GenericBlock {
        let terminator = mir_def::BTerminator {
            id: instr_id,
            term: mir_def::Terminator::Return(Some(mir_def::Val::Num(mir_def::Const::Int(0))))
        };

        mir_def::GenericBlock {
            id,
            instructions: Vec::new(),
            terminator,
            predecessors: HashSet::new()
        }
    }

    pub fn generate(mut self, symbol_table: &mut SymbolTable, function: ast::FunctionDecl<TypedExpr>) -> Option<mir_def::Function> {
        function.block.map(|block| {
            self.generate_block(block, symbol_table);

            self.new_block();

            let entry = symbol_table.get(&function.name).unwrap();
            let global = if let IdentifierAttrs::Fn { global, .. } = entry.attrs { global } else { unreachable!() };
            
            mir_def::Function {
                name: function.name,
                global,
                params: function.params.into_iter().map(|(_,n)|n).collect(),
                basic_blocks: self.cfg
            }
        })
    }

    fn generate_block(&mut self, block: ast::Block<TypedExpr>, symbol_table: &mut SymbolTable) {
        for stmt in block.statements {
            match stmt {
                ast::BlockItem::Declaration(decl) => {
                    self.generate_declaration(decl, symbol_table);
                },
                ast::BlockItem::Statement(stmt) => {
                    self.generate_statement(stmt, symbol_table);
                }
            }
        }
    }

    fn generate_declaration(&mut self, decl: ast::Declaration<TypedExpr>, symbol_table: &mut SymbolTable) {
        match decl {
            ast::Declaration::Var(v) => self.generate_var_decl(v, symbol_table),
            ast::Declaration::Struct(_) |
            ast::Declaration::Union(_) |
            ast::Declaration::Enum(_) |
            ast::Declaration::Fn(_) => ()
        }
    }

    fn generate_initializer(&mut self, write_to: mir_def::Ident, init: ast::Initializer<TypedExpr>, target_type: ast::Type, symbol_table: &mut SymbolTable) {
        match (init, &target_type) {
            (ast::Initializer::Fields(_), _) => unreachable!(),


            (ast::Initializer::Single(TypedExpr{expr:ast::DefaultExpr::String(s),ty:_}), _) => {
                let mut current_offset = 0;
                s.chars().into_iter().for_each(|c| {
                    let n = c as i16;
                    self.push_instr(mir_def::Instruction::CopyToOffset {
                        src: mir_def::Val::Num(mir_def::Const::Char(n)),
                        offset: current_offset,
                        dst: write_to.clone()
                    });

                    current_offset += 1;
                });
                self.push_instr(mir_def::Instruction::CopyToOffset {
                    src: mir_def::Val::Num(mir_def::Const::Char(0)),
                    offset: current_offset,
                    dst: write_to.clone()
                });
            },
            (ast::Initializer::Single(expr), _) => {
                let v = self.generate_expr_and_convert(expr, symbol_table);
                self.push_instr(mir_def::Instruction::Copy {
                    src: v,
                    dst: write_to
                });
            },
            (ast::Initializer::Compound(inits), ast::Type::Union(_)) => {
                // we only do the last one
                let expr = self.compound_init_flatten(ast::Initializer::Compound(inits)).pop().unwrap();

                let val = self.generate_expr_and_convert(expr, symbol_table);

                let tmp_ptr = self.gen_tmp_var(ast::Type::Pointer(Box::new(target_type)), symbol_table);

                self.push_instr(mir_def::Instruction::GetAddress { src: write_to, dst: tmp_ptr.clone() });

                self.push_instr(mir_def::Instruction::Store {
                    src: val,
                    dst_ptr: mir_def::Val::Var(tmp_ptr)
                })
            }
            (ast::Initializer::Compound(inits), _) => {
                let exprs = self.compound_init_flatten(ast::Initializer::Compound(inits));

                let mut current_offset = 0;
                exprs.into_iter().for_each(|expr| {
                    // this works for structs since we have no padding
                    let size = expr.ty.size(self.type_table);

                    let v = self.generate_expr_and_convert(expr, symbol_table);

                    self.push_instr(mir_def::Instruction::CopyToOffset {
                        src: v,
                        offset: current_offset,
                        dst: write_to.clone()
                    });

                    current_offset += size as i16;
                });
            } 
        }
    }

    fn generate_var_decl(&mut self, decl: ast::VarDeclaration<TypedExpr>, symbol_table: &mut SymbolTable) {
        if decl.storage_class.is_some() {
            return;
        }

        if let Some(init) = decl.expr {
            self.generate_initializer(decl.name, init, decl.ty, symbol_table);
        }
    }

    fn compound_init_flatten(&self, init: ast::Initializer<TypedExpr>) -> Vec<TypedExpr> {
        match init {
            ast::Initializer::Compound(inits) => {
                inits.into_iter().flat_map(|i|self.compound_init_flatten(i)).collect()
            },
            ast::Initializer::Single(i) => vec![i],

            ast::Initializer::Fields(_) => unreachable!(),
        }
    }

    fn set_terminator(&mut self, term: mir_def::Terminator) {
        self.current_block.terminator = mir_def::BTerminator {
            id: self.gen_instr_id(),
            term
        };
    }

    fn generate_statement(&mut self, stmt: ast::Statement<TypedExpr>, symbol_table: &mut SymbolTable) {
        match stmt {
            ast::Statement::Return(expr) => {
                let expr = expr.map(|expr|self.generate_expr_and_convert(expr, symbol_table));
                self.set_terminator(mir_def::Terminator::Return(expr));
                self.new_block();
            },
            ast::Statement::Expr(expr) => {
                self.generate_expr_and_convert(expr, symbol_table);
            },
            ast::Statement::If(cond, box (then, else_stmt)) => {
                let cond = self.generate_expr_and_convert(cond, symbol_table);

                let cond_true_label = self.gen_block_id();
                let cond_false_label = self.gen_block_id();

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: cond_false_label,
                    fail: cond_true_label,
                    src1: cond,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::Equal
                });

                self.new_block_w_id(cond_true_label);

                self.generate_statement(then, symbol_table);

                if let Some(else_stmt) = else_stmt {
                    let end_label = self.gen_block_id();
                    self.set_terminator(mir_def::Terminator::Jump { target: end_label });
                    self.new_block_w_id(cond_false_label);
                    self.generate_statement(else_stmt, symbol_table);
                    self.set_terminator(mir_def::Terminator::Jump { target: end_label });
                    self.new_block_w_id(end_label);

                } else {
                    self.set_terminator(mir_def::Terminator::Jump { target: cond_false_label });
                    self.new_block_w_id(cond_false_label);
                }
            },
            ast::Statement::Block(block) => {
                self.generate_block(block, symbol_table);
            },
            ast::Statement::While(cond, box stmt, label) => {
                let continue_label = self.gen_loop_block_id(label, false);
                let break_label = self.gen_loop_block_id(label, true);
                self.set_terminator(mir_def::Terminator::Jump { target: continue_label });
                self.new_block_w_id(continue_label);

                let cond = self.generate_expr_and_convert(cond, symbol_table);

                let loop_label = self.gen_block_id();

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: break_label,
                    fail: loop_label,
                    src1: cond,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::Equal
                });

                self.new_block_w_id(loop_label);

                self.generate_statement(stmt, symbol_table);

                self.set_terminator(mir_def::Terminator::Jump { target: continue_label });

                self.new_block_w_id(break_label);
            },
            ast::Statement::DoWhile(cond, box stmt, label) => {
                let continue_label = self.gen_loop_block_id(label, false);
                let break_label = self.gen_loop_block_id(label, true);

                let loop_label = self.gen_block_id();
                self.set_terminator(mir_def::Terminator::Jump { target: loop_label });
                self.new_block_w_id(loop_label);

                self.generate_statement(stmt, symbol_table);

                self.set_terminator(mir_def::Terminator::Jump { target: continue_label });

                self.new_block_w_id(continue_label);

                let cond = self.generate_expr_and_convert(cond, symbol_table);

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: break_label,
                    fail: loop_label,
                    src1: cond,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::Equal
                });

                self.new_block_w_id(break_label);
            },
            ast::Statement::For { init, cond, post, box body, label } => {
                match init {
                    ast::ForInit::Decl(decl) => self.generate_var_decl(decl, symbol_table),
                    ast::ForInit::Expr(expr) => { self.generate_expr_and_convert(expr, symbol_table); },
                    ast::ForInit::None => ()
                }

                let start_label = self.gen_block_id();

                self.set_terminator(mir_def::Terminator::Jump { target: start_label });

                self.new_block_w_id(start_label);

                let continue_label = self.gen_loop_block_id(label, false);
                let break_label = self.gen_loop_block_id(label, true);

                if let Some(cond) = cond {
                    let cond = self.generate_expr_and_convert(cond, symbol_table);

                    let new_block = self.gen_block_id();

                    self.set_terminator(mir_def::Terminator::JumpCond {
                        target: break_label,
                        fail: new_block,
                        src1: cond,
                        src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                        cond: mir_def::Cond::Equal
                    });

                    self.new_block_w_id(new_block);
                }

                self.generate_statement(body, symbol_table);

                self.set_terminator(mir_def::Terminator::Jump { target: continue_label });

                self.new_block_w_id(continue_label);

                if let Some(post) = post { self.generate_expr_and_convert(post, symbol_table); }

                self.set_terminator(mir_def::Terminator::Jump { target: start_label });

                self.new_block_w_id(break_label);
            },
            ast::Statement::Switch(expr, block, label) => {
                let sc = self.switch_cases.remove(&label).unwrap();

                let val = self.generate_expr_and_convert(expr, symbol_table);

                let break_label = self.gen_loop_block_id(label, true);

                for (num, label) in sc.0 {
                    let label = self.gen_loop_block_id(label, false);

                    let next = self.gen_block_id();

                    self.set_terminator(mir_def::Terminator::JumpCond {
                        target: label,
                        fail: next,
                        src1: val.clone(),
                        src2: mir_def::Val::Num(num),
                        cond: mir_def::Cond::Equal
                    });

                    self.new_block_w_id(next);
                }

                let default_label = sc.1.map(|l|self.gen_loop_block_id(l, false));

                self.set_terminator(mir_def::Terminator::Jump { target: default_label.unwrap_or(break_label) });

                self.generate_block(block, symbol_table);

                self.set_terminator(mir_def::Terminator::Jump { target: break_label });

                self.new_block_w_id(break_label);
            },
            ast::Statement::Case(_, _, label) => {
                let label = self.gen_loop_block_id(label, false);

                self.set_terminator(mir_def::Terminator::Jump { target: label });

                self.new_block_w_id(label);
            },
            ast::Statement::Default(_, label) => {
                let label = self.gen_loop_block_id(label, false);

                self.set_terminator(mir_def::Terminator::Jump { target: label });

                self.new_block_w_id(label);
            }


            ast::Statement::Break(label) => {
                let label = self.gen_loop_block_id(label, true);
                self.set_terminator(mir_def::Terminator::Jump { target: label });
                self.new_block();
            },
            ast::Statement::Continue(label) => {
                let label = self.gen_loop_block_id(label, false);
                self.set_terminator(mir_def::Terminator::Jump { target: label });
                self.new_block();
            },
        }
    }

    fn new_block(&mut self) {
        let id_n = self.gen_block_id();
        self.new_block_w_id(id_n);
    }

    fn new_block_w_id(&mut self, id: mir_def::GenericBlockID) {
        let instr_id = self.gen_instr_id();
        let block = std::mem::replace(
            &mut self.current_block,
            Self::temp_block_ns(id, instr_id)
        );

        self.cfg.blocks.insert(
            mir_def::BlockID::Generic(block.id),
            mir_def::BasicBlock::Generic(block)
        );
    }

    fn gen_tmp_name(&mut self) -> mir_def::Ident {
        *self.tmp_count += 1;
        Rc::new(format!("tmp.{}.", self.tmp_count))
    }

    fn gen_tmp_var(&mut self, ty: mir_def::Type, symbol_table: &mut SymbolTable) -> mir_def::Ident {
        let name = self.gen_tmp_name();
        symbol_table.insert(name.clone(), SymbolTableEntry::new(ty, IdentifierAttrs::Local));
        name
    }

    fn gen_block_id(&mut self) -> mir_def::GenericBlockID {
        *self.tmp_count += 1;
        mir_def::GenericBlockID::Generic(*self.tmp_count)
    }

    fn gen_loop_block_id(&mut self, loop_id: u64, is_break: bool) -> mir_def::GenericBlockID {
        if is_break {
            mir_def::GenericBlockID::LoopBreak(loop_id)
        } else {
            mir_def::GenericBlockID::LoopContinue(loop_id)
        }
    }

    fn push_instr(&mut self, instr: mir_def::Instruction) {
        let id = self.gen_instr_id();
        let instr = mir_def::BInstruction {
            id,
            instr
        };
        self.current_block.instructions.push(instr)
    }

    fn gen_instr_id(&mut self) -> mir_def::InstrID {
        *self.instr_id += 1;
        *self.instr_id
    }

    fn generate_expr_and_convert(&mut self, expr: ast::TypedExpr, symbol_table: &mut SymbolTable) -> mir_def::Val {
        let ty = expr.ty.clone();
        
        let res = self.generate_expr(expr, symbol_table);

        self.convert_expr_res(res, ty, symbol_table)
    }

    fn convert_expr_res(&mut self, expr_res: ExprResult, ty: mir_def::Type, symbol_table: &mut SymbolTable) -> mir_def::Val {
        match expr_res {
            ExprResult::Plain(v) => v,
            ExprResult::DerefedPtr(ptr) => {
                let dst = self.gen_tmp_var(ty, symbol_table);
                self.push_instr(mir_def::Instruction::Load {
                    src_ptr: ptr,
                    dst: dst.clone()
                });
                mir_def::Val::Var(dst)
            },
            ExprResult::SubObject { base, offset } => {
                let dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::CopyFromOffset {
                    src: base,
                    offset: offset as i16,
                    dst: dst.clone()
                });

                mir_def::Val::Var(dst)
            }
        }
    }

    fn generate_expr(&mut self, expr: ast::TypedExpr, symbol_table: &mut SymbolTable) -> ExprResult {
        let ty = expr.ty;
        match expr.expr {
            ast::DefaultExpr::Constant(n) => ExprResult::Plain(mir_def::Val::Num(n)),
            ast::DefaultExpr::Binary(ast::BinOp::Assign(ast::AssignType::Normal), box (left, val)) => {
                let writing_to = self.generate_expr(left, symbol_table);
                let val = self.generate_expr_and_convert(val, symbol_table);

                match writing_to.clone() {
                    ExprResult::DerefedPtr(ptr) => {
                        self.push_instr(
                            mir_def::Instruction::Store { src: val.clone(), dst_ptr: ptr }
                        );

                        writing_to
                    },
                    ExprResult::Plain(dst) => {
                        let dst = match dst {
                            mir_def::Val::Var(v) => v,
                            mir_def::Val::Num(_) => unreachable!(),
                        };

                        self.push_instr(mir_def::Instruction::Copy { src: val.clone(), dst });

                        ExprResult::Plain(val)
                    },
                    ExprResult::SubObject { base, offset } => {
                        self.push_instr(mir_def::Instruction::CopyToOffset {
                            src: val.clone(),
                            offset: offset as i16,
                            dst: base
                        });

                        ExprResult::Plain(val)
                    }
                }
            },
            ast::DefaultExpr::Binary(ast::BinOp::Assign(assign_type), box (lval, val)) => {
                let dst = self.generate_expr(lval, symbol_table);
                
                let var_val = self.convert_expr_res(dst.clone(), ty.clone(), symbol_table);
                let val = self.generate_expr_and_convert(val, symbol_table);

                let tmp_dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::Binary {
                    op: match assign_type {
                        ast::AssignType::Add => mir_def::Binop::Add,
                        ast::AssignType::Sub => mir_def::Binop::Sub,
                        ast::AssignType::Mul => mir_def::Binop::Mul,
                        ast::AssignType::Div => mir_def::Binop::Div,
                        ast::AssignType::Mod => mir_def::Binop::Mod,
                        ast::AssignType::LeftShift => mir_def::Binop::LeftShift,
                        ast::AssignType::RightShift => mir_def::Binop::RightShift,
                        ast::AssignType::BitwiseAnd => mir_def::Binop::BitwiseAnd,
                        ast::AssignType::BitwiseOr => mir_def::Binop::BitwiseOr,
                        ast::AssignType::BitwiseXor => mir_def::Binop::BitwiseXor,

                        ast::AssignType::Normal => unreachable!()
                    },
                    src1: var_val,
                    src2: val,
                    dst: tmp_dst.clone()
                });

                let tmp_dst = mir_def::Val::Var(tmp_dst);

                match dst {
                    ExprResult::Plain(mir_def::Val::Var(v)) => {
                        self.push_instr(mir_def::Instruction::Copy {
                            src: tmp_dst.clone(),
                            dst: v
                        });

                        ExprResult::Plain(tmp_dst)
                    },
                    ExprResult::Plain(_) => unreachable!(),

                    ExprResult::DerefedPtr(v) => {
                        self.push_instr(mir_def::Instruction::Store {
                            src: tmp_dst.clone(),
                            dst_ptr: v
                        });

                        ExprResult::Plain(tmp_dst)
                    },
                    ExprResult::SubObject { base, offset } => {
                        self.push_instr(mir_def::Instruction::CopyToOffset {
                            src: tmp_dst.clone(),
                            offset: offset as i16,
                            dst: base
                        });

                        ExprResult::Plain(tmp_dst)
                    }
                }
            },
            ast::DefaultExpr::Var(v) => ExprResult::Plain(mir_def::Val::Var(v)),

            ast::DefaultExpr::Binary(ast::BinOp::Add, box (right,left @ TypedExpr{expr:_,ty:ast::Type::Pointer(_)}))  |
            ast::DefaultExpr::Binary(ast::BinOp::Add, box (left @ TypedExpr{expr:_,ty:ast::Type::Pointer(_)},right)) => {
                let inner_ty = left.ty.refed_ptr_ty().unwrap();
                
                let scale = inner_ty.size(self.type_table) as i16;
                let ptr = self.generate_expr_and_convert(left, symbol_table);
                let idx = self.generate_expr_and_convert(right, symbol_table);

                let dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::AddPtr {
                    ptr,
                    idx,
                    scale,
                    dst: dst.clone()
                });

                ExprResult::Plain(mir_def::Val::Var(dst))
            },

            ast::DefaultExpr::Binary(ast::BinOp::Sub, box (left @ TypedExpr{expr:_,ty:ast::Type::Pointer(_)},right @ TypedExpr{expr:_,ty:ast::Type::Pointer(_)})) => {
                let inner_ty = left.ty.refed_ptr_ty().unwrap();
                
                let scale = inner_ty.size(self.type_table) as i16;
                let src1 = self.generate_expr_and_convert(left, symbol_table);
                let src2 = self.generate_expr_and_convert(right, symbol_table);

                let dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::Binary {
                    op: mir_def::Binop::Sub,
                    src1,
                    src2,
                    dst: dst.clone()
                });

                self.push_instr(mir_def::Instruction::Binary {
                    op: mir_def::Binop::Div,
                    src1: mir_def::Val::Var(dst.clone()),
                    src2: mir_def::Val::Num(mir_def::Const::Int(scale)),
                    dst: dst.clone()
                });

                ExprResult::Plain(mir_def::Val::Var(dst))
            },
            ast::DefaultExpr::Binary(ast::BinOp::Sub, box (left @ TypedExpr{expr:_,ty:ast::Type::Pointer(_)},right)) => {
                let inner_ty = left.ty.refed_ptr_ty().unwrap();
                
                let scale = -(inner_ty.size(self.type_table) as i16);
                let ptr = self.generate_expr_and_convert(left, symbol_table);
                let idx = self.generate_expr_and_convert(right, symbol_table);

                let dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::AddPtr {
                    ptr,
                    idx,
                    scale,
                    dst: dst.clone()
                });

                ExprResult::Plain(mir_def::Val::Var(dst))
            },

            ast::DefaultExpr::Binary(ast::BinOp::And, box (left, right)) => {
                let false_id = self.gen_block_id();
                let first_true_id = self.gen_block_id();
                let true_id = self.gen_block_id();

                let left = self.generate_expr_and_convert(left, symbol_table);

                let res = self.gen_tmp_var(ast::Type::Int, symbol_table);

                self.push_instr(mir_def::Instruction::Copy { src: mir_def::Val::Num(mir_def::Const::Int(0)), dst: res.clone() });

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: first_true_id,
                    fail: false_id,
                    src1: left,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::NotEqual
                });

                self.new_block_w_id(first_true_id);

                let right = self.generate_expr_and_convert(right, symbol_table);

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: true_id,
                    fail: false_id,
                    src1: right,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::NotEqual
                });

                self.new_block_w_id(true_id);

                self.push_instr(mir_def::Instruction::Copy { src: mir_def::Val::Num(mir_def::Const::Int(1)), dst: res.clone() });

                self.set_terminator(mir_def::Terminator::Jump { target: false_id });

                self.new_block_w_id(false_id);

                ExprResult::Plain(mir_def::Val::Var(res))
            },
            ast::DefaultExpr::Binary(ast::BinOp::Or, box (left, right)) => {
                let false_id = self.gen_block_id();
                let first_false_id = self.gen_block_id();
                let true_id = self.gen_block_id();

                let ty = mir_def::Type::Int;

                let left = self.generate_expr_and_convert(left, symbol_table);

                let res = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::Copy { src: mir_def::Val::Num(mir_def::Const::Int(1)), dst: res.clone() });

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: first_false_id,
                    fail: true_id,
                    src1: left,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::Equal
                });

                self.new_block_w_id(first_false_id);

                let right = self.generate_expr_and_convert(right, symbol_table);

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: false_id,
                    fail: true_id,
                    src1: right,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::Equal
                });

                self.new_block_w_id(false_id);

                self.push_instr(mir_def::Instruction::Copy { src: mir_def::Val::Num(mir_def::Const::Int(0)), dst: res.clone() });

                self.set_terminator(mir_def::Terminator::Jump { target: true_id });

                self.new_block_w_id(true_id);

                ExprResult::Plain(mir_def::Val::Var(res))
            },
            ast::DefaultExpr::Binary(op, box (left, right)) => {
                let op = match op {
                    ast::BinOp::Add => mir_def::Binop::Add,
                    ast::BinOp::Sub => mir_def::Binop::Sub,
                    ast::BinOp::Mul => mir_def::Binop::Mul,
                    ast::BinOp::Div => mir_def::Binop::Div,
                    ast::BinOp::Mod => mir_def::Binop::Mod,
                    ast::BinOp::BitwiseAnd => mir_def::Binop::BitwiseAnd,
                    ast::BinOp::BitwiseXor => mir_def::Binop::BitwiseXor,
                    ast::BinOp::BitwiseOr => mir_def::Binop::BitwiseOr,
                    ast::BinOp::LeftShift => mir_def::Binop::LeftShift,
                    ast::BinOp::RightShift => mir_def::Binop::RightShift,
                    ast::BinOp::Equal => mir_def::Binop::Equal,
                    ast::BinOp::NotEqual => mir_def::Binop::NotEqual,
                    ast::BinOp::LessThan => mir_def::Binop::LessThan,
                    ast::BinOp::LessThanEqual => mir_def::Binop::LessEqual,
                    ast::BinOp::GreaterThan => mir_def::Binop::GreaterThan,
                    ast::BinOp::GreaterThanEqual => mir_def::Binop::GreaterEqual,

                    ast::BinOp::Assign(_) |
                    ast::BinOp::And | ast::BinOp::Or => unreachable!()
                };

                let left = self.generate_expr_and_convert(left, symbol_table);
                let right = self.generate_expr_and_convert(right, symbol_table);

                let tmp_name = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::Binary {
                    op,
                    src1: left,
                    src2: right,
                    dst: tmp_name.clone()
                });

                ExprResult::Plain(mir_def::Val::Var(tmp_name))
            },
            ast::DefaultExpr::Unary(ast::UnOp::Not, box inner) => {
                let res = self.gen_tmp_var(ty, symbol_table);

                let inner = self.generate_expr_and_convert(inner, symbol_table);

                self.push_instr(mir_def::Instruction::Copy { src: mir_def::Val::Num(mir_def::Const::Int(0)), dst: res.clone() });

                let set_true = self.gen_block_id();
                let f = self.gen_block_id();

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: set_true,
                    fail: f,
                    src1: inner,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::Equal
                });

                self.new_block_w_id(set_true);

                self.push_instr(mir_def::Instruction::Copy { src: mir_def::Val::Num(mir_def::Const::Int(1)), dst: res.clone() });

                self.set_terminator(mir_def::Terminator::Jump { target: f });

                self.new_block_w_id(f);

                ExprResult::Plain(mir_def::Val::Var(res))
            },
            ast::DefaultExpr::Unary(ast::UnOp::Dereference, box inner) => {
                let ptr = self.generate_expr_and_convert(inner, symbol_table);

                ExprResult::DerefedPtr(ptr)
            },
            ast::DefaultExpr::Unary(ast::UnOp::AddressOf, box inner) => {
                let v = self.generate_expr(inner, symbol_table);

                match v {
                    ExprResult::Plain(mir_def::Val::Var(v)) => {
                        let res = self.gen_tmp_var(ty, symbol_table);

                        self.push_instr(mir_def::Instruction::GetAddress {
                            src: v,
                            dst: res.clone()
                        });

                        ExprResult::Plain(mir_def::Val::Var(res))
                    },
                    ExprResult::Plain(_) => unreachable!(),

                    ExprResult::DerefedPtr(v) => ExprResult::Plain(v),
                    ExprResult::SubObject { base, offset } => {
                        let dst = self.gen_tmp_var(ty, symbol_table);

                        self.push_instr(mir_def::Instruction::GetAddress {
                            src: base,
                            dst: dst.clone()
                        });

                        self.push_instr(mir_def::Instruction::AddPtr {
                            ptr: mir_def::Val::Var(dst.clone()),
                            idx: mir_def::Val::Num(mir_def::Const::UInt(offset)),
                            scale: 1,
                            dst: dst.clone()
                        });

                        ExprResult::Plain(mir_def::Val::Var(dst))
                    },
                }
            },
            ast::DefaultExpr::Unary(op @ (ast::UnOp::Decrement { is_post: false } | ast::UnOp::Increment { is_post: false }), box inner) => {
                let inner = self.generate_expr(inner, symbol_table);

                let num = if let ast::UnOp::Decrement { .. } = op { -1 } else  { 1 };

                match inner {
                    ExprResult::Plain(mir_def::Val::Var(v)) => {
                        self.push_instr(mir_def::Instruction::Binary {
                            op: mir_def::Binop::Add,
                            src1: mir_def::Val::Var(v.clone()),
                            src2: mir_def::Val::Num(mir_def::Const::Int(num)),
                            dst: v.clone()
                        });

                        ExprResult::Plain(mir_def::Val::Var(v))
                    },
                    ExprResult::Plain(_) => unreachable!(),

                    ExprResult::DerefedPtr(ptr) => {
                        let tmp_v = self.gen_tmp_var(ty, symbol_table);

                        self.push_instr(mir_def::Instruction::Load {
                            src_ptr: ptr.clone(),
                            dst: tmp_v.clone()
                        });

                        self.push_instr(mir_def::Instruction::Binary {
                            op: mir_def::Binop::Add,
                            src1: mir_def::Val::Var(tmp_v.clone()),
                            src2: mir_def::Val::Num(mir_def::Const::Int(num)),
                            dst: tmp_v.clone()
                        });

                        self.push_instr(mir_def::Instruction::Store {
                            src: mir_def::Val::Var(tmp_v.clone()),
                            dst_ptr: ptr
                        });

                        ExprResult::Plain(mir_def::Val::Var(tmp_v))
                    },

                    ExprResult::SubObject { base, offset } => {
                        let tmp_v = self.gen_tmp_var(ty, symbol_table);

                        self.push_instr(mir_def::Instruction::CopyFromOffset {
                            src: base.clone(),
                            offset: offset as i16,
                            dst: tmp_v.clone()
                        });

                        self.push_instr(mir_def::Instruction::Binary {
                            op: mir_def::Binop::Add,
                            src1: mir_def::Val::Var(tmp_v.clone()),
                            src2: mir_def::Val::Num(mir_def::Const::Int(num)),
                            dst: tmp_v.clone()
                        });

                        self.push_instr(mir_def::Instruction::CopyToOffset {
                            src: mir_def::Val::Var(tmp_v.clone()),
                            offset: offset as i16,
                            dst: base
                        });

                        ExprResult::Plain(mir_def::Val::Var(tmp_v))
                    }
                }
            },
            ast::DefaultExpr::Unary(op @ (ast::UnOp::Decrement { is_post: true } | ast::UnOp::Increment { is_post: true }), box inner) => {
                let inner_ptr_ty = inner.ty.refed_ptr_ty().cloned();
                
                let dst = self.gen_tmp_var(inner.ty.clone(), symbol_table);
                
                let inner = self.generate_expr(inner, symbol_table);

                let num = if let ast::UnOp::Decrement { .. } = op { -1 } else  { 1 };
                let num = mir_def::Val::Num(mir_def::Const::Int(num));

                match inner {
                    ExprResult::Plain(mir_def::Val::Var(v)) => {
                        self.push_instr(mir_def::Instruction::Copy {
                            src: mir_def::Val::Var(v.clone()),
                            dst: dst.clone()
                        });

                        if let Some(inner_ty) = inner_ptr_ty {
                            self.push_instr(mir_def::Instruction::AddPtr {
                                ptr: mir_def::Val::Var(v.clone()),
                                idx: num,
                                scale: inner_ty.size(self.type_table) as i16,
                                dst: v.clone()
                            });
                        } else {
                            self.push_instr(mir_def::Instruction::Binary {
                                op: mir_def::Binop::Add,
                                src1: mir_def::Val::Var(v.clone()),
                                src2: num,
                                dst: v.clone()
                            });
                        }
                    },
                    ExprResult::Plain(_) => unreachable!(),

                    ExprResult::DerefedPtr(ptr) => {
                        let tmp_v = self.gen_tmp_var(ty, symbol_table);

                        self.push_instr(mir_def::Instruction::Load {
                            src_ptr: ptr.clone(),
                            dst: tmp_v.clone()
                        });

                        self.push_instr(mir_def::Instruction::Copy {
                            src: mir_def::Val::Var(tmp_v.clone()),
                            dst: dst.clone()
                        });

                        if let Some(inner_ty) = inner_ptr_ty {
                            self.push_instr(mir_def::Instruction::AddPtr {
                                ptr: mir_def::Val::Var(tmp_v.clone()),
                                idx: num,
                                scale: inner_ty.size(self.type_table) as i16,
                                dst: tmp_v.clone()
                            });
                        } else {
                            self.push_instr(mir_def::Instruction::Binary {
                                op: mir_def::Binop::Add,
                                src1: mir_def::Val::Var(tmp_v.clone()),
                                src2: num,
                                dst: tmp_v.clone()
                            });
                        }

                        self.push_instr(mir_def::Instruction::Store {
                            src: mir_def::Val::Var(tmp_v.clone()),
                            dst_ptr: ptr
                        });
                    },

                    ExprResult::SubObject { base, offset } => {
                        let tmp_v = self.gen_tmp_var(ty, symbol_table);

                        self.push_instr(mir_def::Instruction::CopyFromOffset {
                            src: base.clone(),
                            offset: offset as i16,
                            dst: tmp_v.clone()
                        });

                        self.push_instr(mir_def::Instruction::Copy {
                            src: mir_def::Val::Var(tmp_v.clone()),
                            dst: dst.clone()
                        });

                        self.push_instr(mir_def::Instruction::Binary {
                            op: mir_def::Binop::Add,
                            src1: mir_def::Val::Var(tmp_v.clone()),
                            src2: num,
                            dst: tmp_v.clone()
                        });

                        self.push_instr(mir_def::Instruction::CopyToOffset {
                            src: mir_def::Val::Var(tmp_v.clone()),
                            offset: offset as i16,
                            dst: base
                        });
                    }
                }

                ExprResult::Plain(mir_def::Val::Var(dst))
            },
            ast::DefaultExpr::Unary(unop, box inner) => {
                let op = match unop {
                    ast::UnOp::Complement => mir_def::Unop::Complement,
                    ast::UnOp::Negate => mir_def::Unop::Negate,

                    ast::UnOp::Increment { .. } |
                    ast::UnOp::Decrement { .. } |
                    ast::UnOp::AddressOf |
                    ast::UnOp::Dereference |
                    ast::UnOp::Not => unreachable!(),
                };

                let src = self.generate_expr_and_convert(inner, symbol_table);

                let tmp_name = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::Unary {
                    op,
                    src,
                    dst: tmp_name.clone()
                });

                ExprResult::Plain(mir_def::Val::Var(tmp_name))
            },
            ast::DefaultExpr::Ternary(box (cond, then_expr, else_expr)) => {
                let is_void = then_expr.ty.is_void();
                
                let cond = self.generate_expr_and_convert(cond, symbol_table);

                let ret = self.gen_tmp_var(ty, symbol_table);

                let true_label = self.gen_block_id();
                let false_label = self.gen_block_id();
                let end_label = self.gen_block_id();

                self.set_terminator(mir_def::Terminator::JumpCond {
                    target: false_label,
                    fail: true_label,
                    src1: cond,
                    src2: mir_def::Val::Num(mir_def::Const::Int(0)),
                    cond: mir_def::Cond::Equal
                });

                self.new_block_w_id(true_label);

                if is_void {
                    self.generate_expr_and_convert(then_expr, symbol_table);
                    
                    self.set_terminator(mir_def::Terminator::Jump { target: end_label });

                    self.new_block_w_id(false_label);

                    self.generate_expr_and_convert(else_expr, symbol_table);

                    self.set_terminator(mir_def::Terminator::Jump { target: end_label });

                    self.new_block_w_id(end_label);

                    return ExprResult::Plain(mir_def::Val::Var(Rc::new("I_SHOULD_NOT_BE_USED!!!!!!!".into())))
                }

                let v = self.generate_expr_and_convert(then_expr, symbol_table);
                self.push_instr(mir_def::Instruction::Copy {
                    src: v,
                    dst: ret.clone()
                });

                self.set_terminator(mir_def::Terminator::Jump { target: end_label });

                self.new_block_w_id(false_label);

                let v = self.generate_expr_and_convert(else_expr, symbol_table);
                self.push_instr(mir_def::Instruction::Copy {
                    src: v,
                    dst: ret.clone()
                });

                self.set_terminator(mir_def::Terminator::Jump { target: end_label });

                self.new_block_w_id(end_label);

                ExprResult::Plain(mir_def::Val::Var(ret))
            },
            ast::DefaultExpr::FunctionCall(name, exprs) => {
                let void_ty = if let ast::Type::Fn { ref ret_ty,.. } = symbol_table.get(&name).unwrap().ty { ret_ty.is_void() } else { unreachable!() };

                let args = exprs.into_iter().map(|e|self.generate_expr_and_convert(e, symbol_table)).collect();

                let dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::FunctionCall { name, args, dst: if void_ty { None } else { Some(dst.clone()) } });

                ExprResult::Plain(mir_def::Val::Var(dst))
            },
            ast::DefaultExpr::Cast(ast::Type::Void, expr) => {
                let expr = self.generate_expr_and_convert(*expr, symbol_table);

                ExprResult::Plain(expr)
            },
            ast::DefaultExpr::Cast(t, expr) => {
                let expr_ty = &expr.ty;
                if t == *expr_ty {
                    return self.generate_expr(*expr, symbol_table);
                }

                let v = self.generate_expr_and_convert(*expr, symbol_table);

                let dst = self.gen_tmp_var(t.clone(), symbol_table);

                self.push_instr(mir_def::Instruction::Copy { src: v, dst: dst.clone() });

                ExprResult::Plain(mir_def::Val::Var(dst))
            },
            ast::DefaultExpr::Subscript(box (left, right)) => {
                let inner_ty = left.ty.refed_ptr_ty().unwrap();
                
                let scale = inner_ty.size(self.type_table) as i16;
                let ptr = self.generate_expr_and_convert(left, symbol_table);
                let idx = self.generate_expr_and_convert(right, symbol_table);

                let dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::AddPtr {
                    ptr,
                    idx,
                    scale,
                    dst: dst.clone()
                });

                ExprResult::DerefedPtr(mir_def::Val::Var(dst))
            },
            ast::DefaultExpr::String(string) => {
                let num = *self.tmp_count;
                let str_name = format!(".str.mir.{num}.");
                let str_name = Rc::new(str_name);
                let str_len = string.len();
                symbol_table.insert(str_name.clone(), SymbolTableEntry::new(
                    ast::Type::Array(Box::new(ast::Type::Char), (str_len+1) as u16),
                    IdentifierAttrs::Constant {
                        init: mir_def::StaticInit::String { val: string, null_terminated: true }
                    }
                ));
                ExprResult::Plain(mir_def::Val::Var(str_name))
            },
            ast::DefaultExpr::SizeOfT(ty) => {
                ExprResult::Plain(mir_def::Val::Num(mir_def::Const::UInt(ty.size(self.type_table))))
            },
            ast::DefaultExpr::SizeOf(inner) => {
                let ty = inner.ty;
                ExprResult::Plain(mir_def::Val::Num(mir_def::Const::UInt(ty.size(self.type_table))))
            },
            ast::DefaultExpr::MemberAccess(box inner, item) => {
                let struct_name = if let ast::Type::Struct(name) | ast::Type::Union(name) = &inner.ty { name } else { unreachable!() };
                let entry = self.type_table.entries.get(struct_name).unwrap();
                let member = entry.members.get(&item).unwrap();
                let offset = member.offset;

                let inner = self.generate_expr(inner, symbol_table);

                match inner {
                    ExprResult::Plain(mir_def::Val::Var(base)) => ExprResult::SubObject {
                        base,
                        offset
                    },
                    ExprResult::Plain(_) => unreachable!(),
                    ExprResult::DerefedPtr(ptr) => {
                        let dst = self.gen_tmp_var(member.ty.clone(), symbol_table);

                        self.push_instr(mir_def::Instruction::AddPtr {
                            ptr,
                            idx: mir_def::Val::Num(mir_def::Const::UInt(offset)),
                            scale: 1,
                            dst: dst.clone()
                        });

                        ExprResult::DerefedPtr(mir_def::Val::Var(dst))
                    },
                    ExprResult::SubObject { base, offset: old_offset } => ExprResult::SubObject {
                        base,
                        offset: old_offset + offset
                    },
                }
            },
            ast::DefaultExpr::PtrMemberAccess(box inner, item) => {
                let struct_name = if let ast::Type::Pointer(box ast::Type::Struct(name)) | ast::Type::Pointer(box ast::Type::Union(name)) = &inner.ty { name } else { unreachable!() };
                let entry = self.type_table.entries.get(struct_name).unwrap();
                let member = entry.members.get(&item).unwrap();
                let offset = member.offset;

                let inner = self.generate_expr_and_convert(inner, symbol_table);

                let dst = self.gen_tmp_var(ty, symbol_table);

                self.push_instr(mir_def::Instruction::AddPtr {
                    ptr: inner,
                    idx: mir_def::Val::Num(mir_def::Const::UInt(offset)),
                    scale: 1,
                    dst: dst.clone()
                });

                ExprResult::DerefedPtr(mir_def::Val::Var(dst))
            },
            ast::DefaultExpr::CompoundLiteral(ty, box init) => {
                let dst = self.gen_tmp_var(ty.clone(), symbol_table);
                
                self.generate_initializer(dst.clone(), init, ty, symbol_table);

                ExprResult::Plain(mir_def::Val::Var(dst))
            }
        }
    }
}