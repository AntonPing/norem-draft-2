use super::lexer::Span;
use crate::utils::ident::Ident;

#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub enum LitVal {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    Unit,
}

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd)]
pub enum LitType {
    TyInt,
    TyFloat,
    TyBool,
    TyChar,
    TyUnit,
}

impl LitVal {
    pub fn get_lit_type(&self) -> LitType {
        match self {
            LitVal::Int(_) => LitType::TyInt,
            LitVal::Float(_) => LitType::TyFloat,
            LitVal::Bool(_) => LitType::TyBool,
            LitVal::Char(_) => LitType::TyChar,
            LitVal::Unit => LitType::TyUnit,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimOpr {
    IAdd,
    ISub,
    IMul,
    Move,
}

impl PrimOpr {
    pub fn get_arity(&self) -> usize {
        match self {
            PrimOpr::IAdd => 2,
            PrimOpr::ISub => 2,
            PrimOpr::IMul => 2,
            PrimOpr::Move => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Lit { lit: LitType },
    Func { pars: Vec<Type>, res: Box<Type> },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Lit {
        lit: LitVal,
        span: Span,
    },
    Var {
        ident: Ident,
        span: Span,
    },
    Prim {
        prim: PrimOpr,
        args: Vec<Expr>,
        span: Span,
    },
    Func {
        pars: Vec<Ident>,
        body: Box<Expr>,
        span: Span,
    },
    App {
        func: Box<Expr>,
        args: Vec<Expr>,
        span: Span,
    },
    Ifte {
        cond: Box<Expr>,
        trbr: Box<Expr>,
        flbr: Box<Expr>,
        span: Span,
    },
    Stmt {
        stmt: Box<Stmt>,
        cont: Box<Expr>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
    Let {
        ident: Ident,
        typ: Option<Type>,
        expr: Expr,
        span: Span,
    },
    Do {
        expr: Expr,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum Decl {
    Func {
        func: Ident,
        pars: Vec<(Ident, Type)>,
        res: Type,
        span1: Span,
        body: Expr,
        span2: Span,
    },
}

impl Expr {
    pub fn get_span(&self) -> &Span {
        match self {
            Expr::Lit { span, .. } => span,
            Expr::Var { span, .. } => span,
            Expr::Prim { span, .. } => span,
            Expr::Func { span, .. } => span,
            Expr::App { span, .. } => span,
            Expr::Ifte { span, .. } => span,
            Expr::Stmt { span, .. } => span,
        }
    }
}

impl Stmt {
    pub fn get_span(&self) -> &Span {
        match self {
            Stmt::Let { span, .. } => span,
            Stmt::Do { span, .. } => span,
        }
    }
}

impl Decl {
    pub fn get_span(&self) -> &Span {
        match self {
            Decl::Func { span2, .. } => span2,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Module {
    pub name: Ident,
    pub decls: Vec<Decl>,
}
