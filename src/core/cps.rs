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
pub enum PrimOpr {
    // arithmetic
    IAdd,
    ISub,
    IMul,
    // comparision
    ICmpLs,
    ICmpEq,
    ICmpGr,
    // move
    Move,
    // memory operation
    Alloc,
    Load,
    Store,
    // print and scan
    IPrint,
    IScan,
    FPrint,
    FScan,
    CPrint,
    CScan,
}

impl PrimOpr {
    pub fn get_arity(&self) -> usize {
        match self {
            PrimOpr::IAdd => 2,
            PrimOpr::ISub => 2,
            PrimOpr::IMul => 2,
            PrimOpr::ICmpLs => 2,
            PrimOpr::ICmpEq => 2,
            PrimOpr::ICmpGr => 2,
            PrimOpr::Move => 1,
            PrimOpr::Alloc => 1,
            PrimOpr::Load => 2,
            PrimOpr::Store => 3,
            PrimOpr::IPrint => 1,
            PrimOpr::IScan => 0,
            PrimOpr::FPrint => 1,
            PrimOpr::FScan => 0,
            PrimOpr::CPrint => 1,
            PrimOpr::CScan => 0,
        }
    }
    pub fn is_pure(&self) -> bool {
        match self {
            PrimOpr::IAdd => true,
            PrimOpr::ISub => true,
            PrimOpr::IMul => true,
            PrimOpr::ICmpLs => true,
            PrimOpr::ICmpEq => true,
            PrimOpr::ICmpGr => true,
            PrimOpr::Move => true,
            PrimOpr::Alloc => false,
            PrimOpr::Load => false,
            PrimOpr::Store => false,
            PrimOpr::IPrint => false,
            PrimOpr::IScan => false,
            PrimOpr::FPrint => false,
            PrimOpr::FScan => false,
            PrimOpr::CPrint => false,
            PrimOpr::CScan => false,
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
            ast::PrimOpr::IPrint => PrimOpr::IPrint,
            ast::PrimOpr::IScan => PrimOpr::IScan,
            ast::PrimOpr::FPrint => PrimOpr::FPrint,
            ast::PrimOpr::FScan => PrimOpr::FScan,
            ast::PrimOpr::CPrint => PrimOpr::CPrint,
            ast::PrimOpr::CScan => PrimOpr::CScan,
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
        prim: PrimOpr,
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
