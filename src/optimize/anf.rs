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
    ICmpLs,
    ICmpEq,
    ICmpGr,
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
            PrimOpr::ICmpLs => Some(2),
            PrimOpr::ICmpEq => Some(2),
            PrimOpr::ICmpGr => Some(2),
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
            ast::PrimOpr::ISub => PrimOpr::ISub,
            ast::PrimOpr::IMul => PrimOpr::IMul,
            ast::PrimOpr::ICmpLs => PrimOpr::ICmpLs,
            ast::PrimOpr::ICmpEq => PrimOpr::ICmpEq,
            ast::PrimOpr::ICmpGr => PrimOpr::ICmpGr,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BrchOpr {
    Ifte,
    Switch,
}

impl BrchOpr {
    pub fn get_arity(&self) -> Option<usize> {
        match self {
            BrchOpr::Ifte => Some(1),
            BrchOpr::Switch => Some(1),
        }
    }
    pub fn get_cont_arity(&self) -> Option<usize> {
        match self {
            BrchOpr::Ifte => Some(2),
            BrchOpr::Switch => None,
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
    Brch {
        prim: BrchOpr,
        args: Vec<Atom>,
        conts: Vec<Expr>,
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

#[derive(Clone, Debug)]
pub struct Module {
    pub name: Ident,
    pub decls: Vec<Decl>,
}
