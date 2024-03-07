use super::instr::{Block, Instr, Module, Reg};
use crate::core::cps::{self, Atom, Expr, FuncDecl, PrimOpr};
use crate::utils::ident::Ident;
use std::collections::HashMap;

pub struct Codegen {
    code: Vec<Instr<Ident>>,
    blocks: Vec<Block>,
    max_reg: usize,
    reg_map: HashMap<Ident, Reg>,
    cont_map: HashMap<Ident, Vec<Ident>>,
}
impl Codegen {
    pub fn run(modl: &cps::Module) -> Module {
        let mut pass = Codegen {
            code: Vec::new(),
            blocks: Vec::new(),
            max_reg: 0,
            reg_map: HashMap::new(),
            cont_map: HashMap::new(),
        };

        pass.visit_module(modl);
        let blks = pass.blocks.into_iter().map(|blk| (blk.func, blk)).collect();
        Module {
            name: modl.name,
            blks,
        }
    }

    fn new_reg(&mut self) -> Reg {
        let res = self.max_reg;
        self.max_reg += 1;
        Reg(res)
    }

    fn lookup_var(&self, var: &Ident) -> Result<Reg, Ident> {
        if let Some(res) = self.reg_map.get(&var) {
            Ok(*res)
        } else {
            // if not assigned to a register, it should be a label
            Err(*var)
        }
    }

    fn visit_atom(&mut self, atom: &Atom) -> Reg {
        if let Atom::Var(var) = atom {
            match self.lookup_var(var) {
                Ok(reg) => reg,
                Err(addr) => {
                    let reg = self.new_reg();
                    self.code.push(Instr::LitA(reg, addr));
                    reg
                }
            }
        } else {
            let reg = self.new_reg();
            match atom {
                Atom::Var(_) => unreachable!(),
                Atom::Int(val) => {
                    self.code.push(Instr::LitI(reg, *val));
                }
                Atom::Float(val) => {
                    self.code.push(Instr::LitF(reg, *val));
                }
                Atom::Bool(false) => {
                    self.code.push(Instr::LitI(reg, 0));
                }
                Atom::Bool(true) => {
                    self.code.push(Instr::LitI(reg, 1));
                }
                Atom::Char(val) => {
                    self.code.push(Instr::LitC(reg, *val));
                }
                Atom::Unit => {}
            }
            reg
        }
    }

    fn visit_module(&mut self, modl: &cps::Module) {
        for decl in modl.decls.iter() {
            self.visit_func_decl(&decl)
        }
    }

    fn visit_func_decl(&mut self, decl: &FuncDecl) {
        let FuncDecl {
            func,
            cont,
            pars,
            body,
        } = decl;
        self.max_reg = 0;

        for par in pars.iter() {
            let reg = self.new_reg();
            self.code.push(Instr::Pop(reg));
            self.reg_map.insert(*par, reg);
        }

        self.visit_expr(body, *cont);

        let mut code = Vec::new();
        std::mem::swap(&mut code, &mut self.code);

        let block = Block {
            func: *func,
            max_reg: self.max_reg,
            code,
        };
        self.blocks.push(block);
    }

    fn visit_expr(&mut self, expr: &Expr, cont: Ident) {
        match expr {
            Expr::Decls { funcs, conts, body } => {
                assert!(funcs.is_empty());
                for decl in conts {
                    for par in decl.pars.iter() {
                        let reg = self.new_reg();
                        self.reg_map.insert(*par, reg);
                    }
                    self.cont_map.insert(decl.cont, decl.pars.clone());
                }
                self.visit_expr(body, cont);
                for decl in conts {
                    self.code.push(Instr::Label(decl.cont));
                    self.visit_expr(&decl.body, cont)
                }
            }
            Expr::Prim {
                bind,
                prim,
                args,
                rest,
            } => {
                match (prim, &args[..]) {
                    (PrimOpr::Alloc, [Atom::Int(len)]) => {
                        let ret = self.new_reg();
                        self.code.push(Instr::Alloc(ret, *len as usize));
                        self.reg_map.insert(*bind, ret);
                        self.visit_expr(rest, cont);
                        return;
                    }
                    _ => {}
                }
                let args: Vec<Reg> = args.iter().map(|arg| self.visit_atom(arg)).collect();
                let ret = self.new_reg();
                match (prim, &args[..]) {
                    (PrimOpr::Move, [arg]) => {
                        self.code.push(Instr::Move(ret, *arg));
                    }
                    (PrimOpr::IAdd, [arg1, arg2]) => {
                        self.code.push(Instr::IAdd(ret, *arg1, *arg2));
                    }
                    (PrimOpr::ISub, [arg1, arg2]) => {
                        self.code.push(Instr::ISub(ret, *arg1, *arg2));
                    }
                    (PrimOpr::IMul, [arg1, arg2]) => {
                        self.code.push(Instr::IMul(ret, *arg1, *arg2));
                    }
                    (PrimOpr::ICmpLs, [arg1, arg2]) => {
                        self.code.push(Instr::ICmpLs(ret, *arg1, *arg2));
                    }
                    (PrimOpr::ICmpEq, [arg1, arg2]) => {
                        self.code.push(Instr::ICmpEq(ret, *arg1, *arg2));
                    }
                    (PrimOpr::ICmpGr, [arg1, arg2]) => {
                        self.code.push(Instr::ICmpGr(ret, *arg1, *arg2));
                    }
                    (PrimOpr::Select, [arg1, arg2]) => {
                        self.code.push(Instr::Load(ret, *arg1, *arg2));
                    }
                    (PrimOpr::Record, args) => {
                        self.code.push(Instr::Alloc(ret, args.len()));
                        for (i, arg) in args.iter().enumerate() {
                            let idx = self.visit_atom(&Atom::Int(i as i64));
                            self.code.push(Instr::Store(ret, idx, *arg));
                        }
                    }
                    (PrimOpr::Load, [arg1, arg2]) => {
                        self.code.push(Instr::Load(ret, *arg1, *arg2));
                    }
                    (PrimOpr::Store, [arg1, arg2, arg3]) => {
                        self.code.push(Instr::Store(*arg1, *arg2, *arg3));
                    }
                    _ => unreachable!(),
                }
                self.reg_map.insert(*bind, ret);
                self.visit_expr(rest, cont);
            }
            Expr::Call {
                func,
                cont: cont2,
                args,
            } if cont == *cont2 => {
                for arg in args.iter().rev() {
                    let reg = self.visit_atom(arg);
                    self.code.push(Instr::Push(reg));
                }
                self.code.push(Instr::Jmp(*func));
            }
            Expr::Call { func, cont, args } => {
                for arg in args.iter().rev() {
                    let reg = self.visit_atom(arg);
                    self.code.push(Instr::Push(reg));
                }

                match self.lookup_var(func) {
                    Ok(reg) => {
                        self.code.push(Instr::CallInd(reg));
                    }
                    Err(addr) => {
                        self.code.push(Instr::Call(addr));
                    }
                }

                let pars = &self.cont_map[&cont];
                assert_eq!(pars.len(), 1);
                let res = self.lookup_var(&pars[0]).unwrap();
                self.code.push(Instr::Pop(res));
                self.code.push(Instr::Jmp(*cont));
            }
            Expr::Jump { cont: cont2, args } if cont == *cont2 => {
                assert_eq!(args.len(), 1);
                let reg = self.visit_atom(&args[0]);
                self.code.push(Instr::Ret(reg));
            }
            Expr::Jump { cont, args } => {
                let pars = self.cont_map.get(&cont).unwrap().clone();
                for (par, arg) in pars.iter().zip(args.iter()) {
                    let par = self.lookup_var(par).unwrap();
                    let arg = self.visit_atom(arg);
                    self.code.push(Instr::Move(par, arg));
                }
                self.code.push(Instr::Jmp(*cont));
            }
            Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            } => {
                let args: Vec<Reg> = args.iter().map(|arg| self.visit_atom(arg)).collect();
                let label = Ident::fresh(&"label");
                match (cond, &args[..]) {
                    (cps::IfCond::BTrue, [arg]) => {
                        self.code.push(Instr::JmpFl(*arg, label));
                    }
                    (cps::IfCond::BFalse, [arg]) => {
                        self.code.push(Instr::JmpTr(*arg, label));
                    }
                    (cps::IfCond::ICmpGr, [arg1, arg2]) => {
                        let temp_reg = self.new_reg();
                        self.code.push(Instr::ICmpLs(temp_reg, *arg1, *arg2));
                        self.code.push(Instr::JmpFl(temp_reg, label));
                    }
                    (cps::IfCond::ICmpEq, [arg1, arg2]) => {
                        let temp_reg = self.new_reg();
                        self.code.push(Instr::ICmpEq(temp_reg, *arg1, *arg2));
                        self.code.push(Instr::JmpFl(temp_reg, label));
                    }
                    (cps::IfCond::ICmpLs, [arg1, arg2]) => {
                        let temp_reg = self.new_reg();
                        self.code.push(Instr::ICmpLs(temp_reg, *arg1, *arg2));
                        self.code.push(Instr::JmpFl(temp_reg, label));
                    }
                    (_, _) => {
                        unreachable!()
                    }
                }
                self.visit_expr(trbr, cont);
                self.code.push(Instr::Label(label));
                self.visit_expr(flbr, cont);
            }
            Expr::Switch { arg, brchs, dflt } => {
                fn binary_search(
                    slf: &mut Codegen,
                    temp_reg: Reg,
                    arg: Reg,
                    brchs: &[(usize, Ident, &Expr)],
                ) {
                    assert!(!brchs.is_empty());
                    if brchs.len() == 1 {
                        slf.code.push(Instr::Jmp(brchs[0].1));
                    } else {
                        let mid_len = brchs.len() / 2;
                        let mid_id = brchs[mid_len].0;
                        let label = Ident::fresh(&"branch");
                        slf.code.push(Instr::LitI(temp_reg, mid_id as i64));
                        slf.code.push(Instr::ICmpLs(temp_reg, arg, temp_reg));
                        slf.code.push(Instr::JmpFl(temp_reg, label));
                        binary_search(slf, temp_reg, arg, &brchs[0..mid_len]);
                        slf.code.push(Instr::Label(label));
                        binary_search(slf, temp_reg, arg, &brchs[mid_len..]);
                    }
                }
                let brchs: Vec<(usize, Ident, &Expr)> = brchs
                    .into_iter()
                    .map(|(i, brch)| (*i, Ident::fresh(&"case"), brch))
                    .collect();
                let dflt = dflt.as_ref().map(|dflt| (Ident::fresh(&"default"), dflt));
                let arg = self.visit_atom(arg);
                let temp_reg = self.new_reg();
                binary_search(self, temp_reg, arg, &brchs[..]);
                for (_i, label, brch) in brchs {
                    self.code.push(Instr::Label(label));
                    self.visit_expr(&brch, cont);
                }
                if let Some((label, dflt)) = dflt {
                    self.code.push(Instr::Label(label));
                    self.visit_expr(&dflt, cont);
                }
            }
            Expr::Retn { res } => {
                let reg = self.visit_atom(res);
                self.code.push(Instr::Ret(reg));
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn codegen_test() {
    let s = r#"
module test where
func f(k, x):
    let a = @iadd(x, 1);
    let b = @iadd(a, 1);
    let c = @iadd(b, 1);
    let y = @iadd(c, 1);
    jump k(x);

func main(k):
    call f(k, 42);

"#;
    let modl = crate::core::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let modl = Codegen::run(&modl);
    println!("{}\n", modl);
}
