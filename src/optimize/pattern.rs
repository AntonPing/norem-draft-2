use crate::syntax::ast::{LitVal, Pattern};
use crate::utils::ident::Ident;
use crate::utils::intern::InternStr;

pub fn get_bind_vars(patn: &Pattern) -> Vec<Ident> {
    fn aux(vec: &mut Vec<Ident>, patn: &Pattern) {
        match patn {
            Pattern::Var { ident, span: _ } => {
                vec.push(*ident);
            }
            Pattern::Lit { .. } => {}
            Pattern::Cons {
                cons: _,
                patns,
                span: _,
            } => {
                for patn in patns {
                    aux(vec, &patn.data)
                }
            }
            Pattern::Wild { .. } => {}
        }
    }
    let mut vec = Vec::new();
    aux(&mut vec, patn);
    vec
}

fn remove_nth<T: Clone>(vec: &Vec<T>, j: usize) -> Vec<T> {
    vec[..j]
        .iter()
        .chain(vec[j + 1..].iter())
        .cloned()
        .collect()
}

fn insert_nth<T: Clone>(vec: &Vec<T>, j: usize, vec2: &Vec<T>) -> Vec<T> {
    vec[..j]
        .iter()
        .chain(vec2.into_iter())
        .chain(vec[j + 1..].iter())
        .cloned()
        .collect()
}

#[derive(Debug, Clone)]
pub struct PatnMatrix {
    pub objs: Vec<Ident>,
    pub matrix: Vec<Vec<Pattern>>,
    pub acts: Vec<Ident>,
}

pub enum ColType {
    Lit,
    Cons,
    Unknown,
}

impl PatnMatrix {
    pub fn is_empty(&self) -> bool {
        self.matrix.is_empty()
    }
    pub fn first_row_aways_match(&self) -> bool {
        assert!(!self.matrix.is_empty());
        self.matrix[0].iter().all(|patn| match patn {
            Pattern::Var { .. } => true,
            Pattern::Lit { .. } => false,
            Pattern::Cons { .. } => false,
            Pattern::Wild { .. } => false,
        })
    }
    pub fn get_row_num(&self) -> usize {
        assert_eq!(self.acts.len(), self.matrix.len());
        self.acts.len()
    }
    pub fn get_col_num(&self) -> usize {
        assert!(self.matrix.iter().all(|row| row.len() == self.objs.len()));
        self.objs.len()
    }
    pub fn get_lit_set(&self, j: usize) -> Vec<LitVal> {
        let mut vec = Vec::new();
        for row in self.matrix.iter() {
            match &row[j] {
                Pattern::Lit { lit, .. } => {
                    vec.push(*lit);
                }
                Pattern::Var { .. } => {}
                Pattern::Cons { .. } => {
                    unreachable!()
                }
                Pattern::Wild { .. } => {}
            }
        }
        vec
    }
    pub fn get_cons_set(&self, j: usize) -> Vec<Ident> {
        let mut vec = Vec::new();
        for row in self.matrix.iter() {
            match &row[j] {
                Pattern::Lit { .. } => {
                    unreachable!()
                }
                Pattern::Var { .. } => {}
                Pattern::Cons { cons, .. } => {
                    vec.push(*cons);
                }
                Pattern::Wild { .. } => {}
            }
        }
        vec
    }

    pub fn get_col_type(&self, j: usize) -> ColType {
        for row in self.matrix.iter() {
            match row[j] {
                Pattern::Var { .. } => {}
                Pattern::Lit { .. } => return ColType::Lit,
                Pattern::Cons { .. } => return ColType::Cons,
                Pattern::Wild { .. } => {}
            }
        }
        ColType::Unknown
    }

    // first row always success
    // return (bindings, act)
    pub fn success(&self) -> (Vec<(Ident, Ident)>, Ident) {
        let bindings = self.matrix[0]
            .iter()
            .zip(self.objs.iter())
            .flat_map(|(patn, obj)| match patn {
                Pattern::Var { ident, .. } => Some((*ident, *obj)),
                Pattern::Lit { .. } => unreachable!(),
                Pattern::Cons { .. } => unreachable!(),
                Pattern::Wild { .. } => None,
            })
            .collect();
        let act = self.acts[0].clone();
        (bindings, act)
    }

    // return (new_mat, bindings)
    pub fn default(&self, j: usize) -> (PatnMatrix, Vec<Ident>) {
        let objs = remove_nth(&self.objs, j);
        let mut hits: Vec<Ident> = Vec::new();
        let (matrix, acts): (Vec<Vec<_>>, Vec<_>) = self
            .matrix
            .iter()
            .zip(self.acts.iter())
            .flat_map(|(row, act)| match &row[j] {
                Pattern::Lit { .. } => unreachable!(),
                Pattern::Var { ident, .. } => {
                    hits.push(*ident);
                    let new_row = remove_nth(row, j);
                    Some((new_row, act.clone()))
                }
                Pattern::Cons { .. } => unreachable!(),
                Pattern::Wild { .. } => {
                    let new_row = remove_nth(row, j);
                    Some((new_row, act.clone()))
                }
            })
            .unzip();
        let new_mat = PatnMatrix { objs, matrix, acts };
        (new_mat, hits)
    }

    // return (new_mat, hits)
    pub fn specialize_lit(&self, j: usize, lit: LitVal) -> (PatnMatrix, Vec<Ident>) {
        let objs = remove_nth(&self.objs, j);
        let mut hits: Vec<Ident> = Vec::new();
        let (matrix, acts): (Vec<Vec<_>>, Vec<_>) = self
            .matrix
            .iter()
            .zip(self.acts.iter())
            .flat_map(|(row, act)| match &row[j] {
                Pattern::Lit { lit: lit2, .. } => {
                    if *lit2 == lit {
                        let new_row = remove_nth(row, j);
                        Some((new_row, act.clone()))
                    } else {
                        None
                    }
                }
                Pattern::Var { ident, .. } => {
                    hits.push(*ident);
                    let new_row = remove_nth(row, j);
                    Some((new_row, act.clone()))
                }
                Pattern::Cons { .. } => {
                    unreachable!()
                }
                Pattern::Wild { .. } => {
                    let new_row = remove_nth(row, j);
                    Some((new_row, act.clone()))
                }
            })
            .unzip();
        let new_mat = PatnMatrix { objs, matrix, acts };
        (new_mat, hits)
    }
    // return (new_mat, hits)
    pub fn specialize_cons(
        &self,
        j: usize,
        cons: &Ident,
        binds: &Vec<(InternStr, Ident)>,
    ) -> (PatnMatrix, Vec<Ident>) {
        let (labels, new_objs): (Vec<InternStr>, Vec<Ident>) = binds.iter().copied().unzip();
        let objs = insert_nth(&self.objs, j, &new_objs);
        let mut hits: Vec<Ident> = Vec::new();
        let (matrix, acts): (Vec<Vec<_>>, Vec<_>) = self
            .matrix
            .iter()
            .zip(self.acts.iter())
            .flat_map(|(row, act)| match &row[j] {
                Pattern::Lit { .. } => {
                    unreachable!()
                }
                Pattern::Var { ident, span } => {
                    hits.push(*ident);
                    let vec = std::iter::repeat(Pattern::Wild { span: span.clone() })
                        .take(binds.len())
                        .collect();
                    let new_row = insert_nth(row, j, &vec);
                    Some((new_row, act.clone()))
                }
                Pattern::Cons {
                    cons: cons2,
                    patns,
                    span,
                } if *cons2 == *cons => {
                    let patns = labels
                        .iter()
                        .map(|label| {
                            if let Some(patn) = patns.iter().find(|patn| patn.label == *label) {
                                patn.data.clone()
                            } else {
                                Pattern::Wild { span: span.clone() }
                            }
                        })
                        .collect();
                    let new_row = insert_nth(row, j, &patns);
                    Some((new_row, *act))
                }
                Pattern::Cons { .. } => None,
                Pattern::Wild { span } => {
                    let vec = std::iter::repeat(Pattern::Wild { span: span.clone() })
                        .take(binds.len())
                        .collect();
                    let new_row = insert_nth(row, j, &vec);
                    Some((new_row, *act))
                }
            })
            .unzip();
        let new_mat = PatnMatrix { objs, matrix, acts };
        (new_mat, hits)
    }
}
