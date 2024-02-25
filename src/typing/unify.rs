use crate::syntax::ast::{LitType, Type};
use crate::utils::ident::Ident;
use std::collections::HashMap;
use std::ops::Deref;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnifyType {
    Lit(LitType),
    Var(Ident),
    Cons(Ident, Vec<UnifyType>),
    Func(Vec<UnifyType>, Box<UnifyType>),
    Cell(usize),
}

impl From<&Type> for UnifyType {
    fn from(value: &Type) -> Self {
        match value {
            Type::Lit { lit } => UnifyType::Lit(*lit),
            Type::Var { ident } => UnifyType::Var(*ident),
            Type::Cons { cons, args } => {
                let args = args.iter().map(|arg| arg.into()).collect();
                UnifyType::Cons(*cons, args)
            }
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

    pub fn unify_many(&mut self, typs1: &Vec<UnifyType>, typs2: &Vec<UnifyType>) -> UnifyResult {
        if typs1.len() != typs2.len() {
            Err("Can't unify two type vectors with different length!".to_string())
        } else {
            for (typ1, typ2) in typs1.iter().zip(typs2.iter()) {
                self.unify(typ1, typ2)?;
            }
            Ok(())
        }
    }

    pub fn unify(&mut self, typ1: &UnifyType, typ2: &UnifyType) -> UnifyResult {
        match (typ1, typ2) {
            (UnifyType::Lit(lit1), UnifyType::Lit(lit2)) if lit1 == lit2 => Ok(()),
            (UnifyType::Var(ident1), UnifyType::Var(ident2)) if ident1 == ident2 => Ok(()),
            (UnifyType::Cons(cons1, args1), UnifyType::Cons(cons2, args2)) if cons1 == cons2 => {
                self.unify_many(args1, args2)?;
                Ok(())
            }

            (UnifyType::Func(pars1, res1), UnifyType::Func(pars2, res2)) => {
                self.unify_many(pars1, pars2)?;
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
            UnifyType::Cons(_, args) => args.iter().all(|arg| self.occur_check(cell, arg)),
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
            UnifyType::Cons(cons, args) => {
                let args = args.iter().map(|arg| self.merge(arg)).collect();
                UnifyType::Cons(*cons, args)
            }
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

    pub fn instantiate(&mut self, polys: &Vec<Ident>, typ: &UnifyType) -> UnifyType {
        if polys.is_empty() {
            typ.clone()
        } else {
            let map = self.make_instantiate_map(polys);
            substitute(&map, typ)
        }
    }

    pub fn make_instantiate_map(&mut self, polys: &Vec<Ident>) -> HashMap<Ident, usize> {
        polys
            .iter()
            .map(|poly| {
                if let UnifyType::Cell(cell) = self.new_cell() {
                    (*poly, cell)
                } else {
                    unreachable!()
                }
            })
            .collect()
    }
}

pub fn substitute(map: &HashMap<Ident, usize>, typ: &UnifyType) -> UnifyType {
    match typ {
        UnifyType::Lit(lit) => UnifyType::Lit(*lit),
        UnifyType::Var(ident) => {
            if let Some(cell) = map.get(ident) {
                UnifyType::Cell(*cell)
            } else {
                UnifyType::Var(*ident)
            }
        }
        UnifyType::Cons(cons, args) => {
            let args = args.iter().map(|arg| substitute(map, arg)).collect();
            UnifyType::Cons(*cons, args)
        }
        UnifyType::Func(pars, res) => {
            let pars = pars.iter().map(|par| substitute(map, par)).collect();
            let res = Box::new(substitute(map, res));
            UnifyType::Func(pars, res)
        }
        UnifyType::Cell(cell) => UnifyType::Cell(*cell),
    }
}
