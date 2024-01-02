use super::anf::*;
use crate::utils::padding::{DEDT, INDT, NWLN};
use itertools::Itertools;
use std::fmt;

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Var(x) => x.fmt(f),
            Atom::Int(x) => x.fmt(f),
            Atom::Float(x) => x.fmt(f),
            Atom::Bool(x) => x.fmt(f),
            Atom::Char(x) => x.fmt(f),
            Atom::Unit => "()".fmt(f),
        }
    }
}

impl fmt::Display for PrimOpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimOpr::IAdd => "@iadd".fmt(f),
            PrimOpr::ISub => "@isub".fmt(f),
            PrimOpr::IMul => "@imul".fmt(f),
            PrimOpr::Move => "@move".fmt(f),
            PrimOpr::Record => "@record".fmt(f),
            PrimOpr::Select => "@select".fmt(f),
        }
    }
}

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Decl { func, pars, body } = self;
        let pars = pars.iter().format(&", ");
        write!(
            f,
            "fn {func}({pars}) begin{INDT}{NWLN}{body}{DEDT}{NWLN}end"
        )
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Decls { decls, cont } => {
                write!(f, "decl{INDT}")?;
                for decl in decls {
                    write!(f, "{NWLN}{decl}")?;
                }
                write!(f, "{DEDT}{NWLN}in{INDT}{NWLN}{cont}{DEDT}{NWLN}end")?;
                Ok(())
            }
            Expr::Prim {
                bind,
                prim,
                args,
                cont,
            } => {
                let args = args.iter().format(&", ");
                write!(f, "let {bind} = {prim}({args});{NWLN}{cont}")
            }
            Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                let args = args.iter().format(&", ");
                write!(f, "let {bind} = {func}({args});{NWLN}{cont}")
            }
            Expr::Retn { res } => {
                write!(f, "return {res};")
            }
        }
    }
}
