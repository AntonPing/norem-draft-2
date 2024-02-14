use std::collections::HashMap;

use crate::utils::ident::Ident;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Reg(pub usize);

impl std::fmt::Debug for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "r{}", self.0)
    }
}

impl Reg {
    pub fn as_usize(&self) -> usize {
        self.0
    }
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub enum Instr<Addr> {
    Label(Ident),
    LitI(Reg, i64),
    LitF(Reg, f64),
    LitC(Reg, char),
    LitA(Reg, Addr),
    Move(Reg, Reg),
    Bump(usize),
    Alloc(Reg, usize),   // reg = new[len]
    Load(Reg, Reg, Reg), // r1 = r2[r3];
    // LoadI(Reg, Reg, usize),  // r1 = r2[idx];
    Store(Reg, Reg, Reg), // r1[r2] = r3;
    // StoreI(Reg, usize, Reg), // r1[idx] = r3;
    IAdd(Reg, Reg, Reg),
    ISub(Reg, Reg, Reg),
    IMul(Reg, Reg, Reg),
    Push(Reg),
    Pop(Reg),
    Call(Addr),
    CallInd(Reg),
    Ret(Reg),
    Nop,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub func: Ident,
    pub max_reg: usize,
    pub code: Vec<Instr<Ident>>,
}

pub struct Module {
    pub name: Ident,
    pub blks: HashMap<Ident, Block>,
}

impl std::fmt::Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "block {}({})\n", self.func, self.max_reg)?;
        for (i, ins) in self.code.iter().enumerate() {
            write!(f, "    {}:\t{:?}\n", i, ins)?;
        }
        Ok(())
    }
}

impl std::fmt::Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "module {} where", self.name)?;
        for (_, blk) in self.blks.iter() {
            write!(f, "{}\n", blk)?;
        }
        Ok(())
    }
}
