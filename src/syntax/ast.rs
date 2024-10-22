use super::lexer::Span;
use super::prim::Prim;
use crate::utils::ident::Ident;
use crate::utils::intern::InternStr;

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

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Lit {
        lit: LitType,
        span: Span,
    },
    Var {
        ident: Ident,
        span: Span,
    },
    Cons {
        cons: Ident,
        args: Vec<Type>,
        span: Span,
    },
    Func {
        pars: Vec<Type>,
        res: Box<Type>,
        span: Span,
    },
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
        prim: Prim,
        args: Vec<Expr>,
        span: Span,
    },
    Cons {
        cons: Ident,
        flds: Vec<Labeled<Expr>>,
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
    Case {
        expr: Box<Expr>,
        rules: Vec<Rule>,
        span: Span,
    },
    Field {
        expr: Box<Expr>,
        field: InternStr,
        cons_info: Option<Ident>,
        span: Span,
    },
    NewRef {
        expr: Box<Expr>,
        span: Span,
    },
    RefGet {
        expr: Box<Expr>,
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
    RefSet {
        lhs: Expr,
        rhs: Expr,
        span: Span,
    },
    Assign {
        lhs: Expr,
        rhs: Expr,
        span: Span,
    },
    While {
        cond: Expr,
        body: Expr,
        span: Span,
    },
    Do {
        expr: Expr,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Labeled<T> {
    pub label: InternStr,
    pub data: T,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Rule {
    pub patn: Pattern,
    pub body: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Var {
        ident: Ident,
        span: Span,
    },
    Lit {
        lit: LitVal,
        span: Span,
    },
    Cons {
        cons: Ident,
        patns: Vec<Labeled<Pattern>>,
        as_ident: Option<Ident>,
        span: Span,
    },
    Wild {
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Varient {
    pub cons: Ident,
    pub flds: Vec<Labeled<(bool, Type)>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FuncSign {
    pub func: Ident,
    pub polys: Vec<Ident>,
    pub pars: Vec<(Ident, Type)>,
    pub res: Type,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Decl {
    Func {
        sign: FuncSign,
        body: Expr,
        span: Span,
    },
    Data {
        ident: Ident,
        polys: Vec<Ident>,
        vars: Vec<Varient>,
        span: Span,
    },
}

impl Expr {
    pub fn get_span(&self) -> &Span {
        match self {
            Expr::Lit { span, .. } => span,
            Expr::Var { span, .. } => span,
            Expr::Prim { span, .. } => span,
            Expr::Cons { span, .. } => span,
            Expr::Func { span, .. } => span,
            Expr::App { span, .. } => span,
            Expr::Ifte { span, .. } => span,
            Expr::Case { span, .. } => span,
            Expr::Field { span, .. } => span,
            Expr::NewRef { span, .. } => span,
            Expr::RefGet { span, .. } => span,
            Expr::Stmt { span, .. } => span,
        }
    }
}

impl Stmt {
    pub fn get_span(&self) -> &Span {
        match self {
            Stmt::Let { span, .. } => span,
            Stmt::RefSet { span, .. } => span,
            Stmt::Assign { span, .. } => span,
            Stmt::While { span, .. } => span,
            Stmt::Do { span, .. } => span,
        }
    }
}

impl Decl {
    pub fn get_span(&self) -> &Span {
        match self {
            Decl::Func { span, .. } => span,
            Decl::Data { span, .. } => span,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Module {
    pub name: Ident,
    pub decls: Vec<Decl>,
}
