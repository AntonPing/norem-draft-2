use super::cps::*;
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
            PrimOpr::ICmpLs => "@icmpls".fmt(f),
            PrimOpr::ICmpEq => "@icmpeq".fmt(f),
            PrimOpr::ICmpGr => "@icmpgr".fmt(f),
            PrimOpr::Move => "@move".fmt(f),
            PrimOpr::Alloc => "@alloc".fmt(f),
            PrimOpr::Load => "@load".fmt(f),
            PrimOpr::Store => "@store".fmt(f),
        }
    }
}

impl fmt::Display for IfCond {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IfCond::BTrue => "btrue".fmt(f),
            IfCond::BFalse => "bfalse".fmt(f),
            IfCond::ICmpGr => "icmpgr".fmt(f),
            IfCond::ICmpEq => "icmpeq".fmt(f),
            IfCond::ICmpLs => "icmpls".fmt(f),
        }
    }
}

impl fmt::Display for FuncDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let FuncDecl {
            func,
            cont,
            pars,
            body,
        } = self;
        let pars = [cont].into_iter().chain(pars.iter()).format(&", ");
        write!(f, "func {func}({pars}):")?;
        write!(f, "{INDT}{NWLN}{body}{DEDT}")?;
        Ok(())
    }
}

impl fmt::Display for ContDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ContDecl { cont, pars, body } = self;
        let pars = pars.iter().format(&", ");
        write!(f, "cont {cont}({pars}):")?;
        write!(f, "{INDT}{NWLN}{body}{DEDT}")?;
        Ok(())
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Decls { funcs, conts, body } => {
                write!(f, "decls{INDT}")?;
                for func in funcs {
                    write!(f, "{NWLN}{func}")?;
                }
                for cont in conts {
                    write!(f, "{NWLN}{cont}")?;
                }
                write!(f, "{DEDT}{NWLN}in{INDT}{NWLN}{body}{DEDT}{NWLN}end")?;
                Ok(())
            }
            Expr::Prim {
                bind,
                prim,
                args,
                rest,
            } => {
                let args = args.iter().format(&", ");
                write!(f, "let {bind} = {prim}({args});{NWLN}{rest}")
            }
            Expr::Record { bind, args, rest } => {
                let args = args
                    .iter()
                    .map(|(is_mut, arg)| {
                        if *is_mut {
                            format!("mut {}", arg)
                        } else {
                            format!("{}", arg)
                        }
                    })
                    .format(", ");
                write!(f, "record {bind} = {{ {args} }};{NWLN}{rest}")
            }
            Expr::Select {
                bind,
                rec,
                idx,
                rest,
            } => {
                write!(f, "select {bind} = {rec}[{idx}];{NWLN}{rest}")
            }
            Expr::Update {
                rec,
                idx,
                arg,
                rest,
            } => {
                write!(f, "update {rec}[{idx}] = {arg};{NWLN}{rest}")
            }
            Expr::Call { func, cont, args } => {
                let cont = Atom::Var(*cont);
                let args = [&cont].into_iter().chain(args.iter()).format(&", ");
                write!(f, "call {func}({args});")
            }
            Expr::Jump { cont, args } => {
                let args = args.iter().format(&", ");
                write!(f, "jump {cont}({args});")
            }
            Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            } => {
                let args = args.iter().format(&", ");
                write!(f, "if {cond}({args})")?;
                write!(f, "{NWLN}then{INDT}{NWLN}{trbr}{DEDT}")?;
                write!(f, "{NWLN}else{INDT}{NWLN}{flbr}{DEDT}")?;
                Ok(())
            }
            Expr::Switch { arg, brchs, dflt } => {
                write!(f, "switch {arg} of")?;
                for (i, brch) in brchs {
                    write!(f, "{NWLN}case {i}:{INDT}{NWLN}{brch}{DEDT}")?;
                }
                if let Some(dflt) = dflt {
                    write!(f, "{NWLN}default:{INDT}{NWLN}{dflt}{DEDT}")?;
                }
                write!(f, "{NWLN}end")?;
                Ok(())
            }
            Expr::Retn { res } => {
                write!(f, "return {res};")
            }
        }
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Module { name, decls } = self;
        write!(f, "module {} where", name)?;
        for decl in decls {
            write!(f, "{NWLN}{}{NWLN}", decl)?;
        }
        Ok(())
    }
}
