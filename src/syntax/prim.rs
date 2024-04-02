use std::fmt;
use std::str::FromStr;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prim {
    // arithmethics
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

impl Prim {
    pub fn get_arity(&self) -> usize {
        match self {
            Prim::IAdd => 2,
            Prim::ISub => 2,
            Prim::IMul => 2,
            Prim::ICmpLs => 2,
            Prim::ICmpEq => 2,
            Prim::ICmpGr => 2,
            Prim::Move => 1,
            Prim::Alloc => 1,
            Prim::Load => 2,
            Prim::Store => 3,
            Prim::IPrint => 1,
            Prim::IScan => 0,
            Prim::FPrint => 1,
            Prim::FScan => 0,
            Prim::CPrint => 1,
            Prim::CScan => 0,
        }
    }

    pub fn is_pure(&self) -> bool {
        match self {
            Prim::IAdd => true,
            Prim::ISub => true,
            Prim::IMul => true,
            Prim::ICmpLs => true,
            Prim::ICmpEq => true,
            Prim::ICmpGr => true,
            Prim::Move => true,
            Prim::Alloc => false,
            Prim::Load => false,
            Prim::Store => false,
            Prim::IPrint => false,
            Prim::IScan => false,
            Prim::FPrint => false,
            Prim::FScan => false,
            Prim::CPrint => false,
            Prim::CScan => false,
        }
    }
}

impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Prim::IAdd => "@iadd".fmt(f),
            Prim::ISub => "@isub".fmt(f),
            Prim::IMul => "@imul".fmt(f),
            Prim::ICmpLs => "@icmpls".fmt(f),
            Prim::ICmpEq => "@icmpeq".fmt(f),
            Prim::ICmpGr => "@icmpgr".fmt(f),
            Prim::Move => "@move".fmt(f),
            Prim::Alloc => "@alloc".fmt(f),
            Prim::Load => "@load".fmt(f),
            Prim::Store => "@store".fmt(f),
            Prim::IPrint => "@iprint".fmt(f),
            Prim::IScan => "@iscan".fmt(f),
            Prim::FPrint => "@fprint".fmt(f),
            Prim::FScan => "@fscan".fmt(f),
            Prim::CPrint => "@cprint".fmt(f),
            Prim::CScan => "@cscan".fmt(f),
        }
    }
}

impl FromStr for Prim {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "@iadd" => Ok(Prim::IAdd),
            "@isub" => Ok(Prim::ISub),
            "@imul" => Ok(Prim::IMul),
            "@icmpls" => Ok(Prim::ICmpLs),
            "@icmpeq" => Ok(Prim::ICmpEq),
            "@icmpgr" => Ok(Prim::ICmpGr),
            "@imove" => Ok(Prim::Move),
            "@alloc" => Ok(Prim::Alloc),
            "@load" => Ok(Prim::Load),
            "@store" => Ok(Prim::Store),
            "@iprint" => Ok(Prim::IPrint),
            "@iscan" => Ok(Prim::IScan),
            "@fprint" => Ok(Prim::FPrint),
            "@fscan" => Ok(Prim::FScan),
            "@cprint" => Ok(Prim::CPrint),
            "@cscan" => Ok(Prim::CScan),
            _ => Err(()),
        }
    }
}
