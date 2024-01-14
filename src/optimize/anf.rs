use crate::syntax::ast;
use crate::utils::ident::Ident;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Atom {
    Var(Ident),
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    Unit,
}

impl Atom {
    pub fn is_var(&self) -> bool {
        match self {
            Atom::Var(_) => true,
            _ => false,
        }
    }
    pub fn is_lit(&self) -> bool {
        match self {
            Atom::Int(_) => true,
            Atom::Float(_) => true,
            Atom::Bool(_) => true,
            Atom::Char(_) => true,
            Atom::Unit => true,
            _ => false,
        }
    }
    pub fn unwrap_var(self) -> Ident {
        match self {
            Atom::Var(x) => x,
            _ => panic!("Failed to unwrap variable!"),
        }
    }
}

impl From<ast::LitVal> for Atom {
    fn from(lit: ast::LitVal) -> Self {
        match lit {
            ast::LitVal::Int(x) => Atom::Int(x),
            ast::LitVal::Float(x) => Atom::Float(x),
            ast::LitVal::Bool(x) => Atom::Bool(x),
            ast::LitVal::Char(x) => Atom::Char(x),
            ast::LitVal::Unit => Atom::Unit,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimOpr {
    IAdd,
    ISub,
    IMul,
    Move,
    Record,
    Select,
}

impl PrimOpr {
    pub fn get_arity(&self) -> Option<usize> {
        match self {
            PrimOpr::IAdd => Some(2),
            PrimOpr::ISub => Some(2),
            PrimOpr::IMul => Some(2),
            PrimOpr::Move => Some(1),
            PrimOpr::Record => None,
            PrimOpr::Select => Some(2),
        }
    }
}

impl From<ast::PrimOpr> for PrimOpr {
    fn from(lit: ast::PrimOpr) -> Self {
        match lit {
            ast::PrimOpr::IAdd => PrimOpr::IAdd,
            ast::PrimOpr::ISub => PrimOpr::IAdd,
            ast::PrimOpr::IMul => PrimOpr::IAdd,
            ast::PrimOpr::Move => PrimOpr::Move,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub func: Ident,
    pub pars: Vec<Ident>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Decls {
        decls: Vec<Decl>,
        cont: Box<Expr>,
    },
    Prim {
        bind: Ident,
        prim: PrimOpr,
        args: Vec<Atom>,
        cont: Box<Expr>,
    },
    Call {
        bind: Ident,
        func: Atom,
        args: Vec<Atom>,
        cont: Box<Expr>,
    },
    Retn {
        res: Atom,
    },
}