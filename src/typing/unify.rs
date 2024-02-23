use crate::syntax::ast::{LitType, Type};
use crate::utils::ident::Ident;
use std::ops::Deref;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnifyType {
    Lit(LitType),
    Func(Vec<UnifyType>, Box<UnifyType>),
    Var(Ident),
    Cell(usize),
}

impl From<&Type> for UnifyType {
    fn from(value: &Type) -> Self {
        match value {
            Type::Lit { lit } => UnifyType::Lit(*lit),
            Type::Var { ident } => UnifyType::Var(*ident),
            Type::Func { pars, res } => {
                let pars = pars.iter().map(|par| par.into()).collect();
                let res = Box::new(res.deref().into());
                UnifyType::Func(pars, res)
            }
        }
    }
}

type UnifyResult = Result<(), String>;

pub struct UnifySolver {
    arena: Vec<Option<UnifyType>>,
}

impl UnifySolver {
    pub fn new() -> UnifySolver {
        UnifySolver { arena: Vec::new() }
    }

    pub fn new_cell(&mut self) -> UnifyType {
        self.arena.push(None);
        UnifyType::Cell(self.arena.len() - 1)
    }

    pub fn unify(&mut self, typ1: &UnifyType, typ2: &UnifyType) -> UnifyResult {
        match (typ1, typ2) {
            (UnifyType::Lit(lit1), UnifyType::Lit(lit2)) if lit1 == lit2 => Ok(()),
            (UnifyType::Var(ident1), UnifyType::Var(ident2)) if ident1 == ident2 => Ok(()),
            (UnifyType::Func(pars1, res1), UnifyType::Func(pars2, res2)) => {
                if pars1.len() != pars2.len() {
                    return Err(
                        "Can't unify two functions with different parameter length!".to_string()
                    );
                }
                for (par1, par2) in pars1.iter().zip(pars2.iter()) {
                    self.unify(par1, par2)?;
                }
                self.unify(res1, res2)?;
                Ok(())
            }
            (UnifyType::Cell(cell), typ) | (typ, UnifyType::Cell(cell)) => self.assign(*cell, typ),
            (_typ1, _typ2) => Err("Unification failed!".to_string()),
        }
    }

    pub fn assign(&mut self, cell: usize, typ: &UnifyType) -> UnifyResult {
        if let Some(typ2) = &self.arena[cell] {
            // avoid clone somehow?
            self.unify(typ, &typ2.clone())
        } else {
            if self.occur_check(cell, typ) {
                Err("Occur check failed in unification!".to_string())
            } else {
                self.arena[cell] = Some(typ.clone());
                Ok(())
            }
        }
    }

    pub fn occur_check(&self, cell: usize, typ: &UnifyType) -> bool {
        match typ {
            UnifyType::Lit(_) => false,
            UnifyType::Var(_) => false,
            UnifyType::Func(pars, res) => pars
                .iter()
                .chain(std::iter::once(res.deref()))
                .all(|x| self.occur_check(cell, x)),
            UnifyType::Cell(cell2) if cell == *cell2 => true,
            UnifyType::Cell(cell2) => {
                if let Some(typ2) = &self.arena[*cell2] {
                    self.occur_check(cell, typ2)
                } else {
                    false
                }
            }
        }
    }

    pub fn merge(&self, typ: &UnifyType) -> UnifyType {
        match typ {
            UnifyType::Func(pars, res) => {
                let pars = pars.iter().map(|par| self.merge(par)).collect();
                let res = Box::new(self.merge(res));
                UnifyType::Func(pars, res)
            }
            UnifyType::Cell(cell) => {
                if self.arena[*cell].is_some() {
                    self.merge(self.arena[*cell].as_ref().unwrap())
                } else {
                    UnifyType::Cell(*cell)
                }
            }
            other => other.clone(),
        }
    }
}
