#![allow(unused)]

use std::rc::Rc;

use crate::semantic_analysis::type_check::TypeTable;
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
pub struct StructDeclaration {
    pub name: Ident,
    pub members: Vec<MemberDeclaration>,
}

impl StructDeclaration {
    pub fn new(name: Ident, members: Vec<MemberDeclaration>) -> Self {
        Self {
            name,
            members
        }
    }
}

#[derive(Debug, Clone)]
pub struct UnionDeclaration {
    pub name: Ident,
    pub members: Vec<MemberDeclaration>,
}

impl UnionDeclaration {
    pub fn new(name: Ident, members: Vec<MemberDeclaration>) -> Self {
        Self {
            name,
            members
        }
    }
}

#[derive(Debug, Clone)]
pub struct MemberDeclaration {
    pub name: Ident,
    pub ty: Type,
}

impl MemberDeclaration {
    pub fn new(name: Ident, ty: Type) -> Self {
        Self {
            name,
            ty
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
    Fn(FunctionDecl<E>),
    Struct(StructDeclaration),
    Union(UnionDeclaration),
}

#[derive(Debug, Clone)]
pub enum BlockItem<E> {
    Statement(Statement<E>),
    Declaration(Declaration<E>),
}

#[derive(Debug, Clone)]
pub enum Statement<E> {
    Return(Option<E>),
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
    pub expr: Option<Initializer<E>>,
    pub storage_class: Option<StorageClass>,
}

impl<E> VarDeclaration<E> {
    pub fn new(name: Ident, ty: Type, expr: Option<Initializer<E>>, storage_class: Option<StorageClass>) -> Self {
        Self { name, ty, expr, storage_class }
    }
}

#[derive(Debug, Clone)]
pub enum Initializer<E> {
    Single(E),
    Compound(Vec<Initializer<E>>),
    Fields(Vec<(Ident, Initializer<E>)>),
}

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
    Constant(Const),
    Binary(BinOp, Box<(E, E)>),
    Unary(UnOp, Box<E>),
    Var(Ident),
    Ternary(Box<(E, E, E)>),
    FunctionCall(Ident, Vec<E>),
    Cast(Type, Box<E>),
    Subscript(Box<(E, E)>), // lowkey this could be a binop but its not parsed like that so i dont feel like doing it
    String(String),
    SizeOf(Box<E>),
    SizeOfT(Type),
    MemberAccess(Box<E>, Ident),
    PtrMemberAccess(Box<E>, Ident),
    CompoundLiteral(Type, Box<Initializer<E>>),
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
    Increment { is_post: bool },
    Decrement { is_post: bool },
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
    Array(Box<Type>, u16),
    Char,
    UChar,
    Void,
    Struct(Ident),
    Union(Ident),
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

        if specifiers.iter().any(|t|matches!(t, Specifier::Struct(_))) {
            if specifiers.len() > 1 {
                panic!("Cannot have struct specifier and other specifiers");
            }

            let struct_tag = if let Specifier::Struct(t) = specifiers.get(0).unwrap() { t } else { unreachable!() };

            return Self::Struct(struct_tag.clone());
        }

        if specifiers.iter().any(|t|matches!(t, Specifier::Union(_))) {
            if specifiers.len() > 1 {
                panic!("Cannot have struct specifier and other specifiers");
            }

            let union_tag = if let Specifier::Union(t) = specifiers.get(0).unwrap() { t } else { unreachable!() };

            return Self::Union(union_tag.clone());
        }

        if specifiers.contains(&Specifier::Void) {
            if specifiers.len() > 1 {
                panic!("Void cannot have any modifiers");
            }

            return Self::Void;
        }

        if specifiers.contains(&Specifier::Signed) && specifiers.contains(&Specifier::Unsigned) {
            panic!("Type cannot be both signed and unsigned");
        }

        if specifiers.contains(&Specifier::Char) {
            // default is signed

            if specifiers.len() == 1 || (specifiers.len() == 2 && specifiers.contains(&Specifier::Signed)) {
                return Self::Char;
            }

            if specifiers.len() == 2 && specifiers.contains(&Specifier::Unsigned) {
                return Self::UChar;
            }

            panic!("Invalid type specifier");
        }

        if specifiers.contains(&Specifier::Unsigned) {
            return Self::UInt;
        }

        if specifiers.contains(&Specifier::Int) {
            return Self::Int;
        }

        panic!("Unknown specifier combo");
    }

    pub fn get_common_type(&self, other: &Type) -> Type {
        let left_ty = self;
        let right_ty = other;
        
        let left_ty = if left_ty.is_char_ty() { &Type::Int } else { left_ty };
        let right_ty = if right_ty.is_char_ty() { &Type::Int } else { right_ty };
        
        if left_ty == right_ty { return left_ty.clone(); }

        if left_ty.is_signed() { return right_ty.clone(); }
        else                   {  return left_ty.clone(); }
    }

    pub fn is_char_ty(&self) -> bool {
        matches!(self, Type::Char | Type::UChar)
    }

    pub fn is_signed(&self) -> bool {
        match self {
            Type::Pointer(_) |
            Type::Void |
            Type::Fn { .. } |
            Type::Array(_, _) |
            Type::UChar |
            Type::Struct(_) |
            Type::Union(_) |
            Type::UInt => false,

            Type::Char |
            Type::Int => true
        }
    }

    pub fn is_arithmetic(&self) -> bool {
        match self {
            Type::Char | Type::UChar |
            Type::Int  | Type::UInt => true,

            Type::Fn { .. } |
            Type::Array(_, _) |
            Type::Void |
            Type::Struct(_) |
            Type::Union(_) |
            Type::Pointer(_) => false,
        }
    }

    pub fn is_pointer_type(&self) -> bool {
        matches!(self, Type::Pointer(_))
    }

    pub fn refed_ptr_ty<'a>(&'a self) -> Option<&'a Type> {
        match self {
            Type::Pointer(t) => Some(t.as_ref()),
            _ => None
        }
    }

    pub fn is_void_ptr(&self) -> bool {
        matches!(self, Self::Pointer(box Self::Void))
    }

    pub fn is_scalar(&self) -> bool {
        match self {
            Self::Void |
            Self::Array(_, _) |
            Self::Struct(_) |
            Self::Union(_) |
            Self::Fn { .. } => false,

            _ => true,
        }
    }

    pub fn is_complete(&self, type_table: &TypeTable) -> bool {
        if let Type::Array(inner_ty, _) = self {
            return inner_ty.is_complete(type_table);
        }
        
        if matches!(self, Self::Void) { return false; }
        
        if let Type::Struct(name) | Type::Union(name) = self {
            return type_table.entries.contains_key(name)
        }

        return true;
    }

    pub fn is_pointer_to_complete(&self, type_table: &TypeTable) -> bool {
        match self {
            Self::Pointer(inner) => inner.is_complete(type_table),
            _ => false,
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self, Self::Void)
    }

    pub fn is_fn(&self) -> bool {
        matches!(self, Self::Fn { .. })
    }

    pub fn size(&self, type_table: &TypeTable) -> u16 {
        match self {
            &Type::UInt |
            &Type::Pointer(_) |
            &Type::Char |
            &Type::UChar |
            &Type::Int => 1,

            &Type::Array(ref inner_ty, len) => {
                let inner_size = inner_ty.size(type_table);
                inner_size * len
            },
            &Type::Union(ref name) |
            &Type::Struct(ref name) => {
                type_table.entries.get(name).unwrap().size
            }

            &Type::Fn { .. } => unreachable!(),
            &Type::Void => unreachable!()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageClass {
    Static,
    Extern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Specifier {
    Static,
    Extern,
    Int,
    Unsigned,
    Signed,
    Char,
    Void,
    Struct(Ident),
    Union(Ident),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Const {
    Int(i16),
    UInt(u16),
    Char(i16),
    UChar(u16),
}

impl Const {
    pub fn to_type(&self) -> Type {
        match self {
            Self::Int(_) => Type::Int,
            Self::UInt(_) => Type::UInt,
            Self::Char(_) => Type::Char,
            Self::UChar(_) => Type::UChar,
        }
    }
}



#[derive(Debug, Clone)]
pub enum Declarator {
    Ident(Ident),
    Pointer(Box<Declarator>),
    Fn(Vec<ParamInfo>, Box<Declarator>),
    Array(Box<Declarator>, u16),
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
                            if matches!(t, Type::Fn { .. }) {
                                panic!("Function pointers are not yet supported");
                            }
                            (name, t)
                        }).unzip();

                        (name, Type::Fn { params: types, ret_ty: Box::new(base_type) }, names)
                    },
                    _ => panic!("Ummm this should be the top level...")
                }
            },
            Declarator::Array(i, len) => i.process(Type::Array(Box::new(base_type), len))
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
    Array(Box<AbstractDeclarator>, u16),
    Base,
}

impl AbstractDeclarator {
    pub fn process(self, base_type: Type) -> Type {
        match self {
            AbstractDeclarator::Pointer(box p) => {
                p.process(Type::Pointer(Box::new(base_type)))
            },
            AbstractDeclarator::Array(box i, len) => {
                i.process(Type::Array(Box::new(base_type), len))
            }
            AbstractDeclarator::Base => base_type
        }
    }
}