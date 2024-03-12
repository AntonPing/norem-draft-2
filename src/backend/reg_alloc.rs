use std::collections::{HashMap, HashSet};

use super::instr::{Block, Instr, Module, Reg};

pub struct LifetimeScan {
    life_span: HashMap<Reg, (usize, usize)>,
}

impl LifetimeScan {
    fn extend_start(&mut self, var: &Reg, idx: usize) {
        if let Some((s, _)) = self.life_span.get_mut(var) {
            if idx < *s {
                *s = idx;
            }
        } else {
            self.life_span.insert(*var, (idx, idx));
        }
    }

    fn extend_end(&mut self, var: &Reg, idx: usize) {
        if let Some((_, e)) = self.life_span.get_mut(var) {
            if idx > *e {
                *e = idx;
            }
        } else {
            self.life_span.insert(*var, (idx, idx));
        }
    }

    fn extend_span<Addr>(&mut self, ins: &Instr<Addr>, idx: usize) {
        match ins {
            Instr::Label(_) => {}
            Instr::LitI(reg, _)
            | Instr::LitF(reg, _)
            | Instr::LitC(reg, _)
            | Instr::LitA(reg, _) => {
                self.extend_start(&reg, idx);
            }
            Instr::Move(reg1, reg2) => {
                self.extend_start(&reg1, idx);
                self.extend_end(&reg2, idx);
            }
            Instr::Bump(_) => {}
            Instr::Alloc(reg, _) => {
                self.extend_start(&reg, idx);
            }
            Instr::Load(reg1, reg2, reg3) => {
                self.extend_start(&reg1, idx);
                self.extend_end(&reg2, idx);
                self.extend_end(&reg3, idx);
            }
            Instr::Store(reg1, reg2, reg3) => {
                self.extend_end(&reg1, idx);
                self.extend_end(&reg2, idx);
                self.extend_end(&reg3, idx);
            }
            Instr::ICmpGr(reg1, reg2, reg3)
            | Instr::ICmpEq(reg1, reg2, reg3)
            | Instr::ICmpLs(reg1, reg2, reg3)
            | Instr::IAdd(reg1, reg2, reg3)
            | Instr::ISub(reg1, reg2, reg3)
            | Instr::IMul(reg1, reg2, reg3) => {
                self.extend_start(&reg1, idx);
                self.extend_end(&reg2, idx);
                self.extend_end(&reg3, idx);
            }
            Instr::Push(reg) => {
                self.extend_end(&reg, idx);
            }
            Instr::Pop(reg) => {
                self.extend_start(&reg, idx);
            }
            Instr::JmpTr(reg, _) | Instr::JmpFl(reg, _) | Instr::CallInd(reg) => {
                self.extend_end(&reg, idx);
            }
            Instr::Ret(reg) => {
                self.extend_end(&reg, idx);
            }
            Instr::Call(_) | Instr::Jmp(_) | Instr::Nop => {}
        }
    }
}

pub struct RegAlloc {}

impl RegAlloc {
    pub fn run(modl: &mut Module) {
        for (_, blk) in modl.blks.iter_mut() {
            let life = get_life_span(&blk);
            let life_vec = life_span_to_vec(life);
            let (max_reg, reg_map) = reg_alloc(&life_vec);
            blk.max_reg = max_reg;
            reg_rename(blk, &reg_map);
        }
    }
}

fn get_life_span(blk: &Block) -> HashMap<Reg, (usize, usize)> {
    let mut pass = LifetimeScan {
        life_span: HashMap::new(),
    };

    for (idx, ins) in blk.code.iter().enumerate() {
        pass.extend_span(ins, idx);
    }

    pass.life_span
}

fn life_span_to_vec(span: HashMap<Reg, (usize, usize)>) -> Vec<(HashSet<Reg>, HashSet<Reg>)> {
    let mut vec = Vec::new();
    for (reg, (enter, leave)) in span {
        while vec.len() < std::cmp::max(enter, leave) + 1 {
            vec.push((HashSet::new(), HashSet::new()));
        }
        assert!(enter <= leave);
        vec[enter].0.insert(reg);
        vec[leave].1.insert(reg);
    }
    vec
}

fn reg_alloc(vec: &Vec<(HashSet<Reg>, HashSet<Reg>)>) -> (usize, HashMap<Reg, Reg>) {
    let mut reg_map = HashMap::new();
    let mut free_reg = Vec::new();
    let mut max_reg: usize = 0;

    for (enter, leave) in vec.iter() {
        for e_reg in enter {
            assert!(!reg_map.contains_key(e_reg));
            let reg = if free_reg.is_empty() {
                let reg = max_reg;
                max_reg += 1;
                Reg(reg)
            } else {
                free_reg.pop().unwrap()
            };
            reg_map.insert(*e_reg, reg);
        }
        for l_reg in leave {
            assert!(reg_map.contains_key(l_reg));
            let reg = reg_map[l_reg];
            free_reg.push(reg);
        }
    }

    (max_reg, reg_map)
}

fn reg_rename(blk: &mut Block, map: &HashMap<Reg, Reg>) {
    for ins in blk.code.iter_mut() {
        match ins {
            Instr::LitI(reg, _)
            | Instr::LitF(reg, _)
            | Instr::LitC(reg, _)
            | Instr::LitA(reg, _)
            | Instr::Alloc(reg, _)
            | Instr::Push(reg)
            | Instr::Pop(reg)
            | Instr::JmpTr(reg, _)
            | Instr::JmpFl(reg, _)
            | Instr::CallInd(reg)
            | Instr::Ret(reg) => {
                *reg = map[&reg];
            }
            Instr::Move(reg1, reg2) => {
                *reg1 = map[&reg1];
                *reg2 = map[&reg2];
            }
            Instr::Load(reg1, reg2, reg3)
            | Instr::Store(reg1, reg2, reg3)
            | Instr::IAdd(reg1, reg2, reg3)
            | Instr::ISub(reg1, reg2, reg3)
            | Instr::IMul(reg1, reg2, reg3)
            | Instr::ICmpGr(reg1, reg2, reg3)
            | Instr::ICmpEq(reg1, reg2, reg3)
            | Instr::ICmpLs(reg1, reg2, reg3) => {
                *reg1 = map[&reg1];
                *reg2 = map[&reg2];
                *reg3 = map[&reg3];
            }
            Instr::Label(_) | Instr::Bump(_) | Instr::Jmp(_) | Instr::Call(_) | Instr::Nop => {}
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn reg_alloc_test() {
    let s = r#"
module test where
func f(k, x):
    let y = @iadd(x, 1);
    jump k(y);

func main(top):
    decls
        cont k(x):
            return x;
    in
        call f(k, 42);
    end
"#;
    let modl = crate::core::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let mut modl = super::codegen::Codegen::run(&modl);
    println!("{}", modl);
    RegAlloc::run(&mut modl);
    println!("{}", modl);
}