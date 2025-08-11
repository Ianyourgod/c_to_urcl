use crate::ast;

pub struct LoopLabeler {
    label_stack: Vec<u32>,
    label_count: u32,
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

    fn new_label(&mut self) -> u32 {
        let label = self.label_count;
        self.label_stack.push(label);
        self.label_count += 1;
        return label;
    }

    fn end_loop(&mut self) {
        self.label_stack.pop();
    }

    fn label_stmt(&mut self, stmt: &mut ast::Statement<ast::Expr>) {
        match stmt {
            &mut ast::Statement::While(_, ref mut body, ref mut label) => {
                let l = self.new_label();
                *label = l;
                self.label_stmt(body);
                self.end_loop();
            },
            &mut ast::Statement::DoWhile(_, ref mut body, ref mut label) => {
                let l = self.new_label();
                *label = l;
                self.label_stmt(body);
                self.end_loop();
            }
            &mut ast::Statement::For { ref mut body, ref mut label, .. } => {
                let l = self.new_label();
                *label = l;
                self.label_stmt(body);
                self.end_loop();
            }
            &mut ast::Statement::Break(ref mut label) => {
                *label = *self.label_stack.last().unwrap();
            }
            &mut ast::Statement::Continue(ref mut label) => {
                *label = *self.label_stack.last().unwrap();
            }

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
}