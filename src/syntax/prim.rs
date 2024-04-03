use std::fmt;
use std::str::FromStr;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Compare {
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Ne,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Prim {
    // arithmethics
    IAdd,
    ISub,
    IMul,
    IDiv,
    IRem,
    INeg,
    FAdd,
    FSub,
    FMul,
    FDiv,
    FNeg,
    // boolean
    BAnd,
    BOr,
    BNot,
    // comparision
    ICmp(Compare),
    FCmp(Compare),
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
            Prim::IDiv => 2,
            Prim::IRem => 2,
            Prim::INeg => 1,
            Prim::FAdd => 2,
            Prim::FSub => 2,
            Prim::FMul => 2,
            Prim::FDiv => 2,
            Prim::FNeg => 1,
            Prim::BAnd => 2,
            Prim::BOr => 2,
            Prim::BNot => 1,
            Prim::ICmp(_) => 2,
            Prim::FCmp(_) => 2,
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
            Prim::IDiv => true,
            Prim::IRem => true,
            Prim::INeg => true,
            Prim::FAdd => true,
            Prim::FSub => true,
            Prim::FMul => true,
            Prim::FDiv => true,
            Prim::FNeg => true,
            Prim::BAnd => true,
            Prim::BOr => true,
            Prim::BNot => true,
            Prim::ICmp(_) => true,
            Prim::FCmp(_) => true,
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

impl fmt::Display for Compare {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Compare::Lt => "lt".fmt(f),
            Compare::Le => "le".fmt(f),
            Compare::Eq => "eq".fmt(f),
            Compare::Ge => "ge".fmt(f),
            Compare::Gt => "gt".fmt(f),
            Compare::Ne => "ne".fmt(f),
        }
    }
}

impl fmt::Display for Prim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Prim::IAdd => "@iadd".fmt(f),
            Prim::ISub => "@isub".fmt(f),
            Prim::IMul => "@imul".fmt(f),
            Prim::IDiv => "@idiv".fmt(f),
            Prim::IRem => "@irem".fmt(f),
            Prim::INeg => "@ineg".fmt(f),
            Prim::FAdd => "@fadd".fmt(f),
            Prim::FSub => "@fsub".fmt(f),
            Prim::FMul => "@fmul".fmt(f),
            Prim::FDiv => "@fdiv".fmt(f),
            Prim::FNeg => "@fneg".fmt(f),
            Prim::BAnd => "@band".fmt(f),
            Prim::BOr => "@bor".fmt(f),
            Prim::BNot => "@bnot".fmt(f),
            Prim::ICmp(Compare::Lt) => "@icmplt".fmt(f),
            Prim::ICmp(Compare::Le) => "@icmple".fmt(f),
            Prim::ICmp(Compare::Eq) => "@icmpeq".fmt(f),
            Prim::ICmp(Compare::Ge) => "@icmpge".fmt(f),
            Prim::ICmp(Compare::Gt) => "@icmpgr".fmt(f),
            Prim::ICmp(Compare::Ne) => "@icmpne".fmt(f),
            Prim::FCmp(Compare::Lt) => "@fcmplt".fmt(f),
            Prim::FCmp(Compare::Le) => "@fcmple".fmt(f),
            Prim::FCmp(Compare::Eq) => "@fcmpeq".fmt(f),
            Prim::FCmp(Compare::Ge) => "@fcmpge".fmt(f),
            Prim::FCmp(Compare::Gt) => "@fcmpgr".fmt(f),
            Prim::FCmp(Compare::Ne) => "@fcmpne".fmt(f),
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
            "@idiv" => Ok(Prim::IDiv),
            "@irem" => Ok(Prim::IRem),
            "@ineg" => Ok(Prim::INeg),
            "@fadd" => Ok(Prim::FAdd),
            "@fsub" => Ok(Prim::FSub),
            "@fmul" => Ok(Prim::FMul),
            "@fdiv" => Ok(Prim::FDiv),
            "@fneg" => Ok(Prim::FNeg),
            "@band" => Ok(Prim::BAnd),
            "@bor" => Ok(Prim::BOr),
            "@bnot" => Ok(Prim::BNot),
            "@icmplt" => Ok(Prim::ICmp(Compare::Lt)),
            "@icmple" => Ok(Prim::ICmp(Compare::Le)),
            "@icmpeq" => Ok(Prim::ICmp(Compare::Eq)),
            "@icmpge" => Ok(Prim::ICmp(Compare::Ge)),
            "@icmpgt" => Ok(Prim::ICmp(Compare::Gt)),
            "@icmpne" => Ok(Prim::ICmp(Compare::Ne)),
            "@fcmplt" => Ok(Prim::FCmp(Compare::Lt)),
            "@fcmple" => Ok(Prim::FCmp(Compare::Le)),
            "@fcmpeq" => Ok(Prim::FCmp(Compare::Eq)),
            "@fcmpge" => Ok(Prim::FCmp(Compare::Ge)),
            "@fcmpgt" => Ok(Prim::FCmp(Compare::Gt)),
            "@fcmpne" => Ok(Prim::FCmp(Compare::Ne)),
            "@move" => Ok(Prim::Move),
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
