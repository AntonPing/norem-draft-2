use crate::core::cps::{self, Atom, Expr, FuncDecl};
use crate::syntax::prim::{Compare, Prim};
use crate::utils::ident::Ident;
use std::collections::{HashMap, HashSet};

use super::tac::*;

pub struct Lowering {
    cur_blk: Option<BasicBlock>,
    cur_func: Option<Function>,
    cur_modl: Module,
    addr_set: HashSet<Ident>,
    cont_pars: HashMap<Ident, Vec<Ident>>,
}
impl Lowering {
    pub fn new(name: Ident) -> Lowering {
        Lowering {
            cur_blk: None,
            cur_func: None,
            cur_modl: Module::new(name),
            addr_set: HashSet::new(),
            cont_pars: HashMap::new(),
        }
    }

    pub fn run(modl: &cps::Module) -> Module {
        let mut pass = Lowering::new(modl.name);
        for decl in modl.decls.iter() {
            pass.addr_set.insert(decl.func);
        }
        for decl in modl.decls.iter() {
            pass.visit_func_decl(decl);
        }
        pass.cur_modl
    }

    fn push(&mut self, code: Instr) {
        self.cur_blk.as_mut().unwrap().push(code);
    }

    fn seal(&mut self, last: LastInstr) {
        self.cur_blk.as_mut().unwrap().seal(last);
    }

    fn new_block(&mut self, name: Ident) {
        assert!(self.cur_blk.is_none());
        let blk = BasicBlock::new(name);
        self.cur_blk = Some(blk);
    }

    fn emit_block(&mut self) {
        assert!(self.cur_blk.is_some());
        assert!(self.cur_blk.as_mut().unwrap().is_sealed());
        let blk = self.cur_blk.take().unwrap();
        self.cur_func.as_mut().unwrap().push(blk);
    }

    fn new_func(&mut self, name: Ident, pars: Vec<Ident>) {
        assert!(self.cur_func.is_none());
        let func = Function::new(name, pars);
        self.cur_func = Some(func);
    }

    fn emit_func(&mut self) {
        assert!(self.cur_func.is_some());
        let func = self.cur_func.take().unwrap();
        self.cur_modl.push(func);
    }

    fn visit_atom(&mut self, atom: &cps::Atom) -> Ident {
        match atom {
            Atom::Var(x) => {
                if self.addr_set.contains(x) {
                    let x2 = Ident::fresh(&"x");
                    self.push(Instr::LitA(x2, *x));
                    x2
                } else {
                    *x
                }
            }
            Atom::Int(v) => {
                let x = Ident::fresh(&"x");
                self.push(Instr::LitI(x, *v));
                x
            }
            Atom::Float(v) => {
                let x = Ident::fresh(&"x");
                self.push(Instr::LitF(x, *v));
                x
            }
            Atom::Bool(v) => {
                let x = Ident::fresh(&"x");
                self.push(Instr::LitB(x, *v));
                x
            }
            Atom::Char(v) => {
                let x = Ident::fresh(&"x");
                self.push(Instr::LitC(x, *v));
                x
            }
            Atom::Unit => {
                let x = Ident::fresh(&"x");
                self.push(Instr::LitI(x, 0));
                x
            }
        }
    }

    fn visit_func_decl(&mut self, decl: &FuncDecl) {
        let FuncDecl {
            func,
            cont,
            pars,
            body,
        } = decl;
        self.new_func(*func, pars.clone());
        let entry = Ident::fresh(&"entry");
        self.new_block(entry);
        self.visit_expr(body, *cont);
        self.emit_func();
    }

    fn visit_expr(&mut self, expr: &Expr, cont: Ident) {
        match expr {
            Expr::Decls { funcs, conts, body } => {
                assert!(funcs.is_empty());
                for decl in conts {
                    self.cont_pars.insert(decl.cont, decl.pars.clone());
                }
                self.visit_expr(body, cont);
                for decl in conts {
                    self.new_block(decl.cont);
                    self.visit_expr(&decl.body, cont);
                }
                for decl in conts {
                    self.cont_pars.remove(&decl.cont);
                }
            }
            Expr::Prim {
                bind,
                prim,
                args,
                rest,
            } => {
                assert_eq!(prim.get_arity(), args.len());
                let args: Vec<_> = args.iter().map(|arg| self.visit_atom(arg)).collect();
                match (prim, &args[..]) {
                    (Prim::IAdd, [arg1, arg2]) => {
                        self.push(Instr::IAdd(*bind, *arg1, *arg2));
                    }
                    (Prim::ISub, [arg1, arg2]) => {
                        self.push(Instr::ISub(*bind, *arg1, *arg2));
                    }
                    (Prim::IMul, [arg1, arg2]) => {
                        self.push(Instr::IMul(*bind, *arg1, *arg2));
                    }
                    (Prim::IDiv, [arg1, arg2]) => {
                        self.push(Instr::IDiv(*bind, *arg1, *arg2));
                    }
                    (Prim::IRem, [arg1, arg2]) => {
                        self.push(Instr::IRem(*bind, *arg1, *arg2));
                    }
                    (Prim::INeg, [arg1]) => {
                        self.push(Instr::INeg(*bind, *arg1));
                    }
                    (Prim::FAdd, [arg1, arg2]) => {
                        self.push(Instr::FAdd(*bind, *arg1, *arg2));
                    }
                    (Prim::FSub, [arg1, arg2]) => {
                        self.push(Instr::FSub(*bind, *arg1, *arg2));
                    }
                    (Prim::FMul, [arg1, arg2]) => {
                        self.push(Instr::FMul(*bind, *arg1, *arg2));
                    }
                    (Prim::FDiv, [arg1, arg2]) => {
                        self.push(Instr::FDiv(*bind, *arg1, *arg2));
                    }
                    (Prim::FNeg, [arg1]) => {
                        self.push(Instr::FNeg(*bind, *arg1));
                    }
                    (Prim::ICmp(cmp), [arg1, arg2]) => {
                        self.push(Instr::ICmp(*cmp, *bind, *arg1, *arg2));
                    }
                    (Prim::FCmp(cmp), [arg1, arg2]) => {
                        self.push(Instr::FCmp(*cmp, *bind, *arg1, *arg2));
                    }
                    (Prim::Move, [arg]) => {
                        self.push(Instr::Move(*bind, *arg));
                    }
                    (Prim::Alloc, [arg]) => {
                        self.push(Instr::Alloc(*bind, *arg));
                    }
                    (Prim::Load, [arg1, arg2]) => {
                        self.push(Instr::Load(*bind, *arg1, *arg2));
                    }
                    (Prim::Store, [arg1, arg2, arg3]) => {
                        self.push(Instr::Store(*arg1, *arg2, *arg3));
                    }
                    (Prim::IPrint, [arg]) => {
                        self.push(Instr::IPrint(*arg));
                    }
                    (Prim::IScan, []) => {
                        self.push(Instr::IScan(*bind));
                    }
                    (Prim::FPrint, [arg]) => {
                        self.push(Instr::FPrint(*arg));
                    }
                    (Prim::FScan, []) => {
                        self.push(Instr::FScan(*bind));
                    }
                    (Prim::CPrint, [arg]) => {
                        self.push(Instr::CPrint(*arg));
                    }
                    (Prim::CScan, []) => {
                        self.push(Instr::CScan(*bind));
                    }
                    (Prim::Assert, [arg]) => {
                        self.push(Instr::Assert(*arg));
                    }
                    (prim, _) => {
                        println!("{prim}");
                        unreachable!()
                    }
                }
                self.visit_expr(rest, cont);
            }
            Expr::Record { bind, args, rest } => {
                let r = Ident::fresh(&"r");
                self.push(Instr::LitI(r, args.len() as i64));
                self.push(Instr::Alloc(*bind, r));
                for (i, (_, arg)) in args.iter().enumerate() {
                    let idx = self.visit_atom(&Atom::Int(i as i64));
                    let arg = self.visit_atom(arg);
                    self.push(Instr::Store(*bind, idx, arg));
                }
                self.visit_expr(rest, cont);
            }
            Expr::Select {
                bind,
                rec,
                idx,
                rest,
            } => {
                let rec = self.visit_atom(rec);
                let idx = self.visit_atom(&Atom::Int(*idx as i64));
                self.push(Instr::Load(*bind, rec, idx));
                self.visit_expr(rest, cont);
            }
            Expr::Update {
                rec,
                idx,
                arg,
                rest,
            } => {
                let rec = self.visit_atom(rec);
                let idx = self.visit_atom(&Atom::Int(*idx as i64));
                let arg = self.visit_atom(arg);
                self.push(Instr::Store(rec, idx, arg));
                self.visit_expr(rest, cont);
            }
            Expr::Call {
                func,
                cont: cont2,
                args,
            } if *cont2 == cont => {
                let func = self.visit_atom(&Atom::Var(*func));
                let args: Vec<_> = args.iter().map(|arg| self.visit_atom(arg)).collect();
                self.seal(LastInstr::TailCall(func, args));
                self.emit_block();
            }
            Expr::Call { func, cont, args } => {
                let func = self.visit_atom(&Atom::Var(*func));
                let args: Vec<_> = args.iter().map(|arg| self.visit_atom(arg)).collect();
                assert_eq!(self.cont_pars[cont].len(), 1);
                let bind = self.cont_pars[cont][0];
                self.seal(LastInstr::Call(bind, func, *cont, args));
                self.emit_block();
            }
            Expr::Jump { cont: cont2, args } if *cont2 == cont => {
                assert_eq!(args.len(), 1);
                let var = self.visit_atom(&args[0]);
                self.seal(LastInstr::Return(var));
                self.emit_block();
            }
            Expr::Jump { cont, args } => {
                let args: Vec<_> = args.iter().map(|arg| self.visit_atom(arg)).collect();
                println!("{}", cont);
                let par_arg: Vec<(Ident, Ident)> = self.cont_pars[cont]
                    .iter()
                    .zip(args.iter())
                    .map(|(par, arg)| (*par, *arg))
                    .collect();
                for (par, arg) in par_arg {
                    self.push(Instr::Move(par, arg));
                }
                self.seal(LastInstr::Jump(*cont));
                self.emit_block();
            }
            Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            } => {
                let trbr_label = Ident::fresh(&"trbr");
                let flbr_label = Ident::fresh(&"flbr");
                let args: Vec<_> = args.iter().map(|arg| self.visit_atom(arg)).collect();
                match (cond, &args[..]) {
                    (cps::IfCond::BTrue, [arg]) => {
                        self.seal(LastInstr::BrIf(*arg, trbr_label, flbr_label));
                    }
                    (_, _) => {
                        todo!()
                    }
                }
                self.emit_block();

                self.new_block(trbr_label);
                self.visit_expr(trbr, cont);

                self.new_block(flbr_label);
                self.visit_expr(flbr, cont);
            }
            Expr::Switch { arg, brchs, dflt } => {
                fn binary_search(slf: &mut Lowering, arg: Ident, brchs: &[(usize, Ident, &Expr)]) {
                    assert!(!brchs.is_empty());
                    if brchs.len() == 1 {
                        slf.seal(LastInstr::Jump(brchs[0].1));
                        slf.emit_block();
                    } else {
                        let mid_len = brchs.len() / 2;
                        let mid_id = brchs[mid_len].0;

                        let temp = Ident::fresh(&"temp");
                        let trbr_label = Ident::fresh(&"trbr");
                        let flbr_label = Ident::fresh(&"flbr");

                        slf.push(Instr::LitI(temp, mid_id as i64));
                        slf.push(Instr::ICmp(Compare::Lt, temp, arg, temp));
                        slf.seal(LastInstr::BrIf(temp, trbr_label, flbr_label));
                        slf.emit_block();

                        slf.new_block(trbr_label);
                        binary_search(slf, arg, &brchs[0..mid_len]);

                        slf.new_block(flbr_label);
                        binary_search(slf, arg, &brchs[mid_len..]);
                    }
                }
                let brchs: Vec<(usize, Ident, &Expr)> = brchs
                    .into_iter()
                    .map(|(i, brch)| (*i, Ident::fresh(&"case"), brch))
                    .collect();
                let dflt = dflt.as_ref().map(|dflt| (Ident::fresh(&"default"), dflt));
                let arg = self.visit_atom(arg);

                binary_search(self, arg, &brchs[..]);
                for (_i, label, brch) in brchs {
                    self.new_block(label);
                    self.visit_expr(&brch, cont);
                }
                if let Some((label, dflt)) = dflt {
                    self.new_block(label);
                    self.visit_expr(&dflt, cont);
                }
            }
            Expr::Retn { res: _ } => {
                panic!("no return instruction!");
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn lowering_test() {
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
    let modl = Lowering::run(&modl);
    println!("{:#?}\n", modl);
}
