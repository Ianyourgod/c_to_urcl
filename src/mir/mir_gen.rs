use std::collections::HashMap;
use std::rc::Rc;

use crate::mir::mir_def;
use crate::ast;

#[derive(Debug, Clone)]
pub struct Generator {
    tmp_count: u32
}

impl Generator {
    pub fn new() -> Self {
        Self {
            tmp_count: 0
        }
    }

    pub fn generate(&mut self, ast: ast::Program) -> mir_def::Program {
        mir_def::Program { 
            functions: 
                ast.functions.into_iter().filter_map(|f| self.generate_function(f)).collect()
        }
    }

    fn generate_function(&mut self, function: ast::FunctionDecl) -> Option<mir_def::Function> {
        let fn_gen = FunctionGenerator::new(self);

        fn_gen.generate(function)
    }
}

struct FunctionGenerator<'l> {
    generator: &'l mut Generator,
    cfg: mir_def::CFG,
    current_block: mir_def::GenericBlock,
}

impl<'l> FunctionGenerator<'l> {
    pub fn new(generator: &'l mut Generator) -> Self {
        let mut cfg = mir_def::CFG {
            blocks: HashMap::new()
        };

        generator.tmp_count += 1;
        let n = generator.tmp_count;
        let id = mir_def::GenericBlockID::Generic(n);

        cfg.blocks.insert(mir_def::BlockID::Start, mir_def::BasicBlock::Start { successors: vec![mir_def::BlockID::Generic(id)] });
        cfg.blocks.insert(mir_def::BlockID::End, mir_def::BasicBlock::End);

        Self {
            generator,
            cfg,
            current_block: Self::temp_block_ns(id)
        }
    }

    fn temp_block_ns(id: mir_def::GenericBlockID) -> mir_def::GenericBlock {
        mir_def::GenericBlock {
            id,
            instructions: Vec::new(),
            terminator: mir_def::Terminator::Return(mir_def::Val::Num(0))
        }
    }

    pub fn generate(mut self, function: ast::FunctionDecl) -> Option<mir_def::Function> {
        function.block.map(|block| {
            self.generate_block(block);

            self.new_block();
            
            mir_def::Function { name: function.name, params: function.params, basic_blocks: self.cfg }
        })
    }

    fn generate_block(&mut self, block: ast::Block) {
        for stmt in block.statements {
            match stmt {
                ast::BlockItem::Declaration(decl) => {
                    self.generate_declaration(decl);
                },
                ast::BlockItem::Statement(stmt) => {
                    self.generate_statement(stmt);
                }
            }
        }
    }

    fn generate_declaration(&mut self, decl: ast::Declaration) {
        match decl {
            ast::Declaration::Var(v) => self.generate_var_decl(v),
            ast::Declaration::Fn(_) => ()
        }
    }

    fn generate_var_decl(&mut self, decl: ast::VarDeclaration) {
        if let Some(expr) = decl.expr {
            let v = self.generate_expr(expr);
            self.current_block.instructions.push(mir_def::Instruction::Copy {
                src: v,
                dst: decl.name
            });
        }
    }

    fn generate_statement(&mut self, stmt: ast::Statement) {
        match stmt {
            ast::Statement::Return(expr) => {
                self.current_block.terminator = mir_def::Terminator::Return(self.generate_expr(expr));
                self.new_block();
            },
            ast::Statement::Expr(expr) => {
                self.generate_expr(expr);
            },
            ast::Statement::If(cond, box (then, else_stmt)) => {
                let cond = self.generate_expr(cond);

                let cond_true_label = self.gen_block_id();
                let cond_false_label = self.gen_block_id();

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: cond_false_label,
                    fail: cond_true_label,
                    src1: cond,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::Equal
                };

                self.new_block_w_id(cond_true_label);

                self.generate_statement(then);

                if let Some(else_stmt) = else_stmt {
                    let end_label = self.gen_block_id();
                    self.current_block.terminator = mir_def::Terminator::Jump { target: end_label };
                    self.new_block_w_id(cond_false_label);
                    self.generate_statement(else_stmt);
                    self.current_block.terminator = mir_def::Terminator::Jump { target: end_label };
                    self.new_block_w_id(end_label);

                } else {
                    self.current_block.terminator = mir_def::Terminator::Jump { target: cond_false_label };
                    self.new_block_w_id(cond_false_label);
                }
            },
            ast::Statement::Block(block) => {
                self.generate_block(block);
            },
            ast::Statement::While(cond, box stmt, label) => {
                let continue_label = self.gen_loop_block_id(label, false);
                let break_label = self.gen_loop_block_id(label, true);
                self.current_block.terminator = mir_def::Terminator::Jump { target: continue_label };
                self.new_block_w_id(continue_label);

                let cond = self.generate_expr(cond);

                let loop_label = self.gen_block_id();

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: break_label,
                    fail: loop_label,
                    src1: cond,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::Equal
                };

                self.new_block_w_id(loop_label);

                self.generate_statement(stmt);

                self.current_block.terminator = mir_def::Terminator::Jump { target: continue_label };

                self.new_block_w_id(break_label);
            },
            ast::Statement::DoWhile(cond, box stmt, label) => {
                let continue_label = self.gen_loop_block_id(label, false);
                let break_label = self.gen_loop_block_id(label, true);

                let loop_label = self.gen_block_id();
                self.current_block.terminator = mir_def::Terminator::Jump { target: loop_label };
                self.new_block_w_id(loop_label);

                self.generate_statement(stmt);

                self.current_block.terminator = mir_def::Terminator::Jump { target: continue_label };

                self.new_block_w_id(continue_label);

                let cond = self.generate_expr(cond);

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: break_label,
                    fail: loop_label,
                    src1: cond,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::Equal
                };

                self.new_block_w_id(break_label);
            },
            ast::Statement::For { init, cond, post, box body, label } => {
                match init {
                    ast::ForInit::Decl(decl) => self.generate_var_decl(decl),
                    ast::ForInit::Expr(expr) => { self.generate_expr(expr); },
                    ast::ForInit::None => ()
                }

                let start_label = self.gen_block_id();

                self.current_block.terminator = mir_def::Terminator::Jump { target: start_label };

                self.new_block_w_id(start_label);

                let continue_label = self.gen_loop_block_id(label, false);
                let break_label = self.gen_loop_block_id(label, true);

                if let Some(cond) = cond {
                    let cond = self.generate_expr(cond);

                    let new_block = self.gen_block_id();

                    self.current_block.terminator = mir_def::Terminator::JumpCond {
                        target: break_label,
                        fail: new_block,
                        src1: cond,
                        src2: mir_def::Val::Num(0),
                        cond: mir_def::Cond::Equal
                    };

                    self.new_block_w_id(new_block);
                }

                self.generate_statement(body);

                self.current_block.terminator = mir_def::Terminator::Jump { target: continue_label };

                self.new_block_w_id(continue_label);

                if let Some(post) = post { self.generate_expr(post); }

                self.current_block.terminator = mir_def::Terminator::Jump { target: start_label };

                self.new_block_w_id(break_label);
            }
            ast::Statement::Break(label) => {
                let label = self.gen_loop_block_id(label, true);
                self.current_block.terminator = mir_def::Terminator::Jump { target: label };
                self.new_block();
            },
            ast::Statement::Continue(label) => {
                let label = self.gen_loop_block_id(label, false);
                self.current_block.terminator = mir_def::Terminator::Jump { target: label };
                self.new_block();
            },
        }
    }

    fn new_block(&mut self) {
        let id_n = self.gen_block_id();
        self.new_block_w_id(id_n);
    }

    fn new_block_w_id(&mut self, id: mir_def::GenericBlockID) {
        let block = std::mem::replace(
            &mut self.current_block,
            Self::temp_block_ns(id)
        );

        self.cfg.blocks.insert(
            mir_def::BlockID::Generic(block.id),
            mir_def::BasicBlock::Generic(block)
        );
    }

    fn gen_tmp_name(&mut self) -> mir_def::Ident {
        self.generator.tmp_count += 1;
        Rc::new(format!("tmp.{}.", self.generator.tmp_count))
    }

    fn gen_block_id(&mut self) -> mir_def::GenericBlockID {
        self.generator.tmp_count += 1;
        mir_def::GenericBlockID::Generic(self.generator.tmp_count)
    }

    fn gen_loop_block_id(&mut self, loop_id: u32, is_break: bool) -> mir_def::GenericBlockID {
        if is_break {
            mir_def::GenericBlockID::LoopBreak(loop_id)
        } else {
            mir_def::GenericBlockID::LoopContinue(loop_id)
        }
    }

    fn generate_expr(&mut self, expr: ast::Expr) -> mir_def::Val {
        match expr {
            ast::Expr::Number(n) => mir_def::Val::Num(n),
            ast::Expr::Binary(ast::BinOp::Assign(ast::AssignType::Normal), box (var, val)) => {
                let var_name = match var { ast::Expr::Var(v) => v, _ => unreachable!() };

                let val = self.generate_expr(val);

                self.current_block.instructions.push(mir_def::Instruction::Copy {
                    src: val,
                    dst: var_name.clone()
                });

                mir_def::Val::Var(var_name)
            },
            ast::Expr::Binary(ast::BinOp::Assign(assign_type), box (var, val)) => {
                let var_name = match &var { ast::Expr::Var(v) => v.clone(), _ => unreachable!() };

                let var_val = self.generate_expr(var);
                let val = self.generate_expr(val);

                self.current_block.instructions.push(mir_def::Instruction::Binary {
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
                    dst: var_name.clone()
                });

                mir_def::Val::Var(var_name)
            },
            ast::Expr::Var(v) => mir_def::Val::Var(v),
            ast::Expr::Binary(ast::BinOp::And, box (left, right)) => {
                let false_id = self.gen_block_id();
                let first_true_id = self.gen_block_id();
                let true_id = self.gen_block_id();

                let left = self.generate_expr(left);

                let res = self.gen_tmp_name();

                self.current_block.instructions.push(mir_def::Instruction::Copy { src: mir_def::Val::Num(0), dst: res.clone() });

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: first_true_id,
                    fail: false_id,
                    src1: left,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::NotEqual
                };

                self.new_block_w_id(first_true_id);

                let right = self.generate_expr(right);

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: true_id,
                    fail: false_id,
                    src1: right,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::NotEqual
                };

                self.new_block_w_id(true_id);

                self.current_block.instructions.push(mir_def::Instruction::Copy { src: mir_def::Val::Num(1), dst: res.clone() });

                self.current_block.terminator = mir_def::Terminator::Jump { target: false_id };

                self.new_block_w_id(false_id);

                mir_def::Val::Var(res)
            },
            ast::Expr::Binary(ast::BinOp::Or, box (left, right)) => {
                let false_id = self.gen_block_id();
                let first_false_id = self.gen_block_id();
                let true_id = self.gen_block_id();

                let left = self.generate_expr(left);

                let res = self.gen_tmp_name();

                self.current_block.instructions.push(mir_def::Instruction::Copy { src: mir_def::Val::Num(1), dst: res.clone() });

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: first_false_id,
                    fail: true_id,
                    src1: left,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::Equal
                };

                self.new_block_w_id(first_false_id);

                let right = self.generate_expr(right);

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: false_id,
                    fail: true_id,
                    src1: right,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::Equal
                };

                self.new_block_w_id(false_id);

                self.current_block.instructions.push(mir_def::Instruction::Copy { src: mir_def::Val::Num(0), dst: res.clone() });

                self.current_block.terminator = mir_def::Terminator::Jump { target: true_id };

                self.new_block_w_id(true_id);

                mir_def::Val::Var(res)
            },
            ast::Expr::Binary(op, box (left, right)) => {
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

                let left = self.generate_expr(left);
                let right = self.generate_expr(right);

                let tmp_name = self.gen_tmp_name();

                self.current_block.instructions.push(mir_def::Instruction::Binary {
                    op,
                    src1: left,
                    src2: right,
                    dst: tmp_name.clone()
                });

                mir_def::Val::Var(tmp_name)
            },
            ast::Expr::Unary(ast::UnOp::Not, box inner) => {
                let res = self.gen_tmp_name();

                let inner = self.generate_expr(inner);

                self.current_block.instructions.push(mir_def::Instruction::Copy { src: mir_def::Val::Num(0), dst: res.clone() });

                let set_true = self.gen_block_id();
                let f = self.gen_block_id();

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: set_true,
                    fail: f,
                    src1: inner,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::Equal
                };

                self.new_block_w_id(set_true);

                self.current_block.instructions.push(mir_def::Instruction::Copy { src: mir_def::Val::Num(1), dst: res.clone() });

                self.current_block.terminator = mir_def::Terminator::Jump { target: f };

                self.new_block_w_id(f);

                mir_def::Val::Var(res)
            },
            ast::Expr::Unary(unop, box inner) => {
                let op = match unop {
                    ast::UnOp::Complement => mir_def::Unop::Complement,
                    ast::UnOp::Negate => mir_def::Unop::Negate,

                    ast::UnOp::Not => unreachable!(),
                };

                let inner = self.generate_expr(inner);

                let tmp_name = self.gen_tmp_name();

                self.current_block.instructions.push(mir_def::Instruction::Unary {
                    op,
                    inner,
                    dst: tmp_name.clone()
                });

                mir_def::Val::Var(tmp_name)
            },
            ast::Expr::Ternary(box (cond, then_expr, else_expr)) => {
                let cond = self.generate_expr(cond);

                let ret = self.gen_tmp_name();

                let true_label = self.gen_block_id();
                let false_label = self.gen_block_id();
                let end_label = self.gen_block_id();

                self.current_block.terminator = mir_def::Terminator::JumpCond {
                    target: false_label,
                    fail: true_label,
                    src1: cond,
                    src2: mir_def::Val::Num(0),
                    cond: mir_def::Cond::Equal
                };

                self.new_block_w_id(true_label);

                let v = self.generate_expr(then_expr);
                self.current_block.instructions.push(mir_def::Instruction::Copy {
                    src: v,
                    dst: ret.clone()
                });

                self.current_block.terminator = mir_def::Terminator::Jump { target: end_label };

                self.new_block_w_id(false_label);

                let v = self.generate_expr(else_expr);
                self.current_block.instructions.push(mir_def::Instruction::Copy {
                    src: v,
                    dst: ret.clone()
                });

                self.current_block.terminator = mir_def::Terminator::Jump { target: end_label };

                self.new_block_w_id(end_label);

                mir_def::Val::Var(ret)
            },
            ast::Expr::FunctionCall(name, exprs) => {
                let args = exprs.into_iter().map(|e|self.generate_expr(e)).collect();

                let dst = self.gen_tmp_name();

                self.current_block.instructions.push(mir_def::Instruction::FunctionCall { name, args, dst: dst.clone() });

                mir_def::Val::Var(dst)
            }
        }
    }
}