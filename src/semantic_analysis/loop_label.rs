use crate::ast;

type Label = (u64, LabelType);

pub struct LoopLabeler {
    label_stack: Vec<Label>,
    label_count: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelType {
    Loop,
    Switch,
}

impl LoopLabeler {
    pub fn new() -> Self {
        Self {
            label_stack: Vec::new(),
            label_count: 1,
        }
    }

    pub fn label(&mut self, program: &mut ast::Program<ast::Expr>) {
        program.top_level_items.iter_mut().for_each(|f|{
            match f {
                &mut ast::Declaration::Fn(ref mut f) => {
                    self.label_function(f);
                },
                &mut ast::Declaration::Struct(_) |
                &mut ast::Declaration::Union(_) |
                &mut ast::Declaration::Enum(_) |
                &mut ast::Declaration::Var(_) => ()
            }
        });
    }

    fn label_function(&mut self, function: &mut ast::FunctionDecl<ast::Expr>) {
        function.block.as_mut().map(|b|self.label_block(b));
    }

    fn label_block(&mut self, block: &mut ast::Block<ast::Expr>) {
        block.statements.iter_mut().for_each(|stmt|{
            if let ast::BlockItem::Statement(stmt) = stmt {
                self.label_stmt(stmt);
            }
        });
    }

    fn new_label_num(&mut self) -> u64 {
        self.label_count += 1;
        self.label_count
    }

    fn new_label(&mut self, label_type: LabelType) -> u64 {
        let label = self.new_label_num();
        self.label_stack.push((label, label_type));
        return label;
    }

    fn new_loop_label(&mut self) -> u64 {
        self.new_label(LabelType::Loop)
    }

    fn new_switch_label(&mut self) -> u64 {
        self.new_label(LabelType::Switch)
    }

    fn end_loop(&mut self) {
        self.label_stack.pop();
    }

    fn label_stmt(&mut self, stmt: &mut ast::Statement<ast::Expr>) {
        match stmt {
            &mut ast::Statement::While(_, ref mut body, ref mut label) => {
                let l = self.new_loop_label();
                *label = l;
                self.label_stmt(body);
                self.end_loop();
            },
            &mut ast::Statement::DoWhile(_, ref mut body, ref mut label) => {
                let l = self.new_loop_label();
                *label = l;
                self.label_stmt(body);
                self.end_loop();
            }
            &mut ast::Statement::For { ref mut body, ref mut label, .. } => {
                let l = self.new_loop_label();
                *label = l;
                self.label_stmt(body);
                self.end_loop();
            }
            &mut ast::Statement::Switch(_, ref mut body, ref mut label) => {
                let l = self.new_switch_label();
                *label = l;
                self.label_block(body);
                self.end_loop();
            },
            &mut ast::Statement::Case(_, ref mut label, ref mut personal_label) => {
                *label = self.get_last_switch_label().unwrap();
                *personal_label = self.new_label_num();
            },
            &mut ast::Statement::Default(ref mut label, ref mut personal_label) => {
                *label = self.get_last_switch_label().unwrap();
                *personal_label = self.new_label_num();
            },
            &mut ast::Statement::Break(ref mut label) => {
                *label = self.get_last_label().unwrap();
            },
            &mut ast::Statement::Continue(ref mut label) => {
                *label = self.get_last_loop_label().unwrap();
            },

            &mut ast::Statement::Block(ref mut block) => self.label_block(block),
            &mut ast::Statement::If(_, ref mut inner_stuff) => {
                let (then_stmt, else_stmt) = &mut **inner_stuff;

                self.label_stmt(then_stmt);

                if let Some(stmt) = else_stmt {
                    self.label_stmt(stmt);
                }
            }

            &mut ast::Statement::Expr(_) |
            &mut ast::Statement::Return(_) => ()
        }
    }

    fn get_last_label(&self) -> Option<u64> {
        self.label_stack.last().map(|a|a.0)
    }

    fn get_last_label_ty(&self, label_type: LabelType) -> Option<u64> {
        self.label_stack.iter().rev().find(|i|i.1==label_type).map(|a|a.0)
    }

    fn get_last_loop_label(&self) -> Option<u64> {
        self.get_last_label_ty(LabelType::Loop)
    }

    fn get_last_switch_label(&self) -> Option<u64> {
        self.get_last_label_ty(LabelType::Switch)
    }
}