use crate::syntax::ast;
use crate::syntax::prim::Prim;
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
    pub fn unwrap_int(self) -> i64 {
        match self {
            Atom::Int(x) => x,
            _ => panic!("Failed to unwrap integer!"),
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
pub enum IfCond {
    BTrue,
    BFalse,
    ICmpGr,
    ICmpEq,
    ICmpLs,
}

impl IfCond {
    pub fn get_arity(&self) -> Option<usize> {
        match self {
            IfCond::BTrue => Some(1),
            IfCond::BFalse => Some(1),
            IfCond::ICmpGr => Some(2),
            IfCond::ICmpEq => Some(2),
            IfCond::ICmpLs => Some(2),
        }
    }
}

#[derive(Clone, Debug)]
pub struct FuncDecl {
    pub func: Ident,
    pub cont: Ident,
    pub pars: Vec<Ident>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub struct ContDecl {
    pub cont: Ident,
    pub pars: Vec<Ident>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Expr {
    Decls {
        funcs: Vec<FuncDecl>,
        conts: Vec<ContDecl>,
        body: Box<Expr>,
    },
    Prim {
        bind: Ident,
        prim: Prim,
        args: Vec<Atom>,
        rest: Box<Expr>,
    },
    Record {
        bind: Ident,
        args: Vec<(bool, Atom)>,
        rest: Box<Expr>,
    },
    Select {
        bind: Ident,
        rec: Atom,
        idx: usize,
        rest: Box<Expr>,
    },
    Update {
        rec: Atom,
        idx: usize,
        arg: Atom,
        rest: Box<Expr>,
    },
    Call {
        func: Ident,
        cont: Ident,
        args: Vec<Atom>,
    },
    Jump {
        cont: Ident,
        args: Vec<Atom>,
    },
    Ifte {
        cond: IfCond,
        args: Vec<Atom>,
        trbr: Box<Expr>,
        flbr: Box<Expr>,
    },
    Switch {
        arg: Atom,
        brchs: Vec<(usize, Expr)>,
        dflt: Option<Box<Expr>>,
    },
    Retn {
        res: Atom,
    },
}

#[derive(Clone, Debug)]
pub struct Module {
    pub name: Ident,
    pub decls: Vec<FuncDecl>,
}
