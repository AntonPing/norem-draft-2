use std::collections::HashMap;

use crate::utils::ident::Ident;

#[derive(Clone, Debug)]
pub enum Instr {
    LitI(Ident, i64),
    LitF(Ident, f64),
    LitC(Ident, char),
    Move(Ident, Ident),
    Alloc(Ident, Ident),
    Load(Ident, Ident, Ident),
    Store(Ident, Ident, Ident),
    ICmpGr(Ident, Ident, Ident),
    ICmpEq(Ident, Ident, Ident),
    ICmpLs(Ident, Ident, Ident),
    IAdd(Ident, Ident, Ident),
    ISub(Ident, Ident, Ident),
    IMul(Ident, Ident, Ident),
}

#[derive(Clone, Debug)]
pub enum LastInstr {
    TailCall(Ident, Vec<Ident>),
    // Call(bind, func, cont, args)
    Call(Ident, Ident, Ident, Vec<Ident>),
    Return(Ident),
    Jump(Ident),
    BrIf(Ident, Ident, Ident),
}

#[derive(Clone, Debug)]
pub struct BasicBlock {
    pub name: Ident,
    pub codes: Vec<Instr>,
    pub last: Option<LastInstr>,
}

impl BasicBlock {
    pub fn new(name: Ident) -> BasicBlock {
        BasicBlock {
            name,
            codes: Vec::new(),
            last: None,
        }
    }
    pub fn push(&mut self, code: Instr) {
        self.codes.push(code);
    }
    pub fn seal(&mut self, brch: LastInstr) {
        assert!(self.last.is_none());
        self.last = Some(brch);
    }
    pub fn is_sealed(&self) -> bool {
        self.last.is_some()
    }
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: Ident,
    pub pars: Vec<Ident>,
    pub blks: Vec<BasicBlock>,
}

impl Function {
    pub fn new(name: Ident, pars: Vec<Ident>) -> Function {
        Function {
            name,
            pars,
            blks: Vec::new(),
        }
    }

    pub fn push(&mut self, blk: BasicBlock) {
        self.blks.push(blk);
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    pub name: Ident,
    pub funcs: HashMap<Ident, Function>,
}

impl Module {
    pub fn new(name: Ident) -> Module {
        Module {
            name,
            funcs: HashMap::new(),
        }
    }

    pub fn push(&mut self, func: Function) {
        self.funcs.insert(func.name, func);
    }
}