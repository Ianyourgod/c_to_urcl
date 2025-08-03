#![allow(unused)]

use std::rc::Rc;

pub use crate::Ident;

#[derive(Debug, Clone)]
pub struct Program<E> {
    pub top_level_items: Vec<Declaration<E>>,
}

impl<E> Program<E> {
    pub fn new(fns: Vec<Declaration<E>>) -> Self {
        Self {
            top_level_items: fns,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionDecl<E> {
    pub name: Ident,
    pub ret_ty: Type,
    pub params: Vec<(Type, Ident)>,
    pub block: Option<Block<E>>,
    pub storage_class: Option<StorageClass>,
}

impl<E> FunctionDecl<E> {
    pub fn new(name: Rc<String>, ret_ty: Type, params: Vec<(Type, Ident)>, block: Option<Block<E>>, storage_class: Option<StorageClass>) -> Self {
        Self {
            name: name,
            ret_ty,
            params,
            block,
            storage_class
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block<E> {
    pub statements: Vec<BlockItem<E>>
}

impl<E> Block<E> {
    pub fn new(statements: Vec<BlockItem<E>>) -> Self {
        Self {
            statements
        }
    }
}

#[derive(Debug, Clone)]
pub enum Declaration<E> {
    Var(VarDeclaration<E>),
    Fn(FunctionDecl<E>)
}

#[derive(Debug, Clone)]
pub enum BlockItem<E> {
    Statement(Statement<E>),
    Declaration(Declaration<E>),
}

#[derive(Debug, Clone)]
pub enum Statement<E> {
    Return(E),
    Expr(E),
    If(E, Box<(Statement<E>, Option<Statement<E>>)>),
    Block(Block<E>),
    While(E, Box<Statement<E>>, u32),
    DoWhile(E, Box<Statement<E>>, u32),
    For {
        init: ForInit<E>,
        cond: Option<E>,
        post: Option<E>,
        body: Box<Statement<E>>,
        label: u32,
    },
    Break(u32),
    Continue(u32),
}

#[derive(Debug, Clone)]
pub enum ForInit<E> {
    Decl(VarDeclaration<E>),
    Expr(E),
    None,
}

#[derive(Debug, Clone)]
pub struct VarDeclaration<E> {
    pub name: Ident,
    pub ty: Type,
    pub expr: Option<E>,
    pub storage_class: Option<StorageClass>,
}

impl<E> VarDeclaration<E> {
    pub fn new(name: Ident, ty: Type, expr: Option<E>, storage_class: Option<StorageClass>) -> Self {
        Self { name, ty, expr, storage_class }
    }
}

//trait ExprTy: std::fmt::Debug + Clone {}

#[derive(Debug, Clone)]
pub struct TypedExpr {
    pub expr: DefaultExpr<TypedExpr>,
    pub ty: Type,
}

impl TypedExpr {
    pub fn new(expr: DefaultExpr<TypedExpr>, ty: Type) -> Self {
        Self {
            expr,
            ty
        }
    }
}

//impl<TypedExpr: std::fmt::Debug + Clone> ExprTy for TypedExpr {}

#[derive(Debug, Clone)]
pub enum DefaultExpr<E> {
    Number(Const),
    Binary(BinOp, Box<(E, E)>),
    Unary(UnOp, Box<E>),
    Var(Ident),
    Ternary(Box<(E, E, E)>),
    FunctionCall(Ident, Vec<E>),
    Cast(Type, Box<E>),
}

#[derive(Debug, Clone)]
pub struct Expr(pub DefaultExpr<Expr>);

impl Expr {
    pub fn new(e: DefaultExpr<Expr>) -> Self {
        Self(e)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Complement,
    Negate,
    Not,
    Dereference,
    AddressOf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanEqual,
    GreaterThanEqual,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    LeftShift,
    RightShift,
    Assign(AssignType),
}

impl BinOp {
    pub fn is_arithmetic(&self) -> bool {
        match self {
            BinOp::Add | BinOp::Sub |
            BinOp::Mul | BinOp::Div |
            BinOp::Mod             => true,

            _ => false
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignType {
    Normal,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    LeftShift,
    RightShift,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Int,
    UInt,
    Fn {
        params: Vec<Type>,
        ret_ty: Box<Type>,
    },
    Pointer(Box<Type>),
}

impl Type {
    pub fn from_specifiers(specifiers: Vec<Specifier>) -> Self {
        specifiers.iter().enumerate().for_each(|(i, s1)| {
            specifiers.iter().skip(i+1).for_each(|s2| {
                if s1 == s2 {
                    panic!("Type list cannot contain 2 of the same specifier");
                }
            });
        });

        if specifiers.len() == 0 {
            panic!("Must have a type specifier");
        }

        if specifiers.contains(&Specifier::Signed) && specifiers.contains(&Specifier::Unsigned) {
            panic!("Type cannot be both signed and unsigned");
        }

        if specifiers.contains(&Specifier::Unsigned) {
            return Self::UInt;
        }

        return Self::Int;
    }

    pub fn get_common_type<'a>(&'a self, other: &'a Type) -> &'a Type {
        if self == other { return self; }

        if self.is_signed() { return other; }
        else                { return self;  }
    }

    pub fn is_signed(&self) -> bool {
        match self {
            Type::Pointer(_) |
            Type::Fn { .. } |
            Type::UInt     => false,

            Type::Int => true
        }
    }

    pub fn is_arithmetic(&self) -> bool {
        match self {
            Type::Int | Type::UInt => true,

            Type::Fn { .. } |
            Type::Pointer(_) => false,
        }
    }

    pub fn is_pointer_type(&self) -> bool {
        if let Type::Pointer(_) = self { true } else { false }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageClass {
    Static,
    Extern,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Specifier {
    Static,
    Extern,
    Int,
    Unsigned,
    Signed,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Const {
    Int(i16),
    UInt(u16),
}

impl Const {
    pub fn to_type(&self) -> Type {
        match self {
            Self::Int(_) => Type::Int,
            Self::UInt(_) => Type::UInt
        }
    }
}



#[derive(Debug, Clone)]
pub enum Declarator {
    Ident(Ident),
    Pointer(Box<Declarator>),
    Fn(Vec<ParamInfo>, Box<Declarator>),
}

impl Declarator {
    pub fn process(self, base_type: Type) -> (Ident, Type, Vec<Ident>) {
        match self {
            Declarator::Ident(n) => (n, base_type, Vec::new()),
            Declarator::Pointer(d) => d.process(Type::Pointer(Box::new(base_type))),
            Declarator::Fn(params, d) => {
                match *d {
                    Declarator::Ident(name) => {
                        let (names, types): (Vec<_>, Vec<_>) = params.into_iter().map(|param| {
                            let (name, t, _) = param.declarator.process(param.ty);
                            if let Type::Fn { .. } = t {
                                panic!("Function pointers are not yet supported");
                            }
                            (name, t)
                        }).unzip();

                        (name, Type::Fn { params: types, ret_ty: Box::new(base_type) }, names)
                    },
                    _ => panic!("Ummm this should be the top level...")
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParamInfo {
    pub ty: Type,
    pub declarator: Declarator
}

impl ParamInfo {
    pub fn new(ty: Type, declarator: Declarator) -> Self {
        Self {
            ty,
            declarator
        }
    }
}

#[derive(Debug, Clone)]
pub enum AbstractDeclarator {
    Pointer(Box<AbstractDeclarator>),
    Base,
}

impl AbstractDeclarator {
    pub fn process(self, base_type: Type) -> Type {
        match self {
            AbstractDeclarator::Pointer(box p) => {
                p.process(Type::Pointer(Box::new(base_type)))
            },
            AbstractDeclarator::Base => base_type
        }
    }
}