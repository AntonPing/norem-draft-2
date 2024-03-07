use super::cps::*;
use crate::core::cps::PrimOpr;
use crate::utils::ident::Ident;
use std::collections::{HashMap, HashSet};

pub struct InlineScan {
    // (n, m), where n is occur times, and m is call-site occur times
    // n >= m always
    occur_map: HashMap<Ident, (usize, usize)>,
    inline_mark: HashSet<Ident>,
}

impl InlineScan {
    pub fn run(modl: &Module) -> HashSet<Ident> {
        let mut pass = InlineScan {
            occur_map: HashMap::new(),
            inline_mark: HashSet::new(),
        };
        pass.visit_module(modl);
        pass.inline_mark
    }

    fn visit_atom(&mut self, atom: &Atom) {
        if let Atom::Var(x) = atom {
            let res = self.occur_map.get_mut(x);
            if let Some((n, _m)) = res {
                *n += 1;
            } else {
                self.occur_map.insert(*x, (1, 0));
            }
        }
    }

    fn visit_module(&mut self, modl: &Module) {
        let Module { name: _, decls } = modl;
        for decl in decls {
            self.visit_func_decl(decl);
        }
    }

    fn visit_func_decl(&mut self, decl: &FuncDecl) {
        let FuncDecl {
            func: _,
            cont,
            pars,
            body,
        } = decl;
        self.visit_expr(body);
        pars.iter().for_each(|par| {
            self.occur_map.remove(par);
        });
        self.occur_map.remove(&cont);
    }

    fn visit_cont_decl(&mut self, decl: &ContDecl) {
        let ContDecl {
            cont: _,
            pars,
            body,
        } = decl;
        self.visit_expr(body);
        pars.iter().for_each(|par| {
            self.occur_map.remove(par);
        });
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Decls { funcs, conts, body } => {
                self.visit_expr(body);
                for decl in funcs {
                    self.visit_func_decl(decl)
                }
                for decl in conts {
                    self.visit_cont_decl(decl)
                }
                for decl in funcs {
                    let name = decl.func;
                    let res = self.occur_map.remove(&name);
                    if res == Some((1, 1)) {
                        self.inline_mark.insert(name);
                    }
                }
                for decl in conts {
                    let name = decl.cont;
                    let res = self.occur_map.remove(&name);
                    if res == Some((1, 1)) {
                        self.inline_mark.insert(name);
                    }
                }
            }
            Expr::Prim {
                bind: _,
                prim: _,
                args,
                rest,
            } => {
                self.visit_expr(rest);
                args.iter().for_each(|arg| self.visit_atom(arg));
            }
            Expr::Call { func, cont, args } => {
                self.visit_atom(&Atom::Var(*func));
                self.visit_atom(&Atom::Var(*cont));
                args.iter().for_each(|arg| self.visit_atom(arg));
                let res = self.occur_map.get_mut(&func).unwrap();
                res.1 += 1;
            }
            Expr::Jump { cont, args } => {
                self.visit_atom(&Atom::Var(*cont));
                args.iter().for_each(|arg| self.visit_atom(arg));
                let res = self.occur_map.get_mut(&cont).unwrap();
                res.1 += 1;
            }
            Expr::Ifte {
                cond: _,
                args,
                trbr,
                flbr,
            } => {
                self.visit_expr(trbr);
                self.visit_expr(flbr);
                args.iter().for_each(|arg| self.visit_atom(arg));
            }
            Expr::Switch { arg, brchs, dflt } => {
                brchs.iter().for_each(|(_, brch)| self.visit_expr(brch));
                dflt.as_ref().map(|dflt| self.visit_expr(dflt));
                self.visit_atom(arg);
            }
            Expr::Retn { res } => {
                self.visit_atom(res);
            }
        }
    }
}

pub struct InlinePerform {
    inline_mark: HashSet<Ident>,
    func_map: HashMap<Ident, FuncDecl>,
    cont_map: HashMap<Ident, ContDecl>,
}

impl InlinePerform {
    pub fn run(modl: Module, mark: HashSet<Ident>) -> Module {
        let mut pass = InlinePerform {
            inline_mark: mark,
            func_map: HashMap::new(),
            cont_map: HashMap::new(),
        };
        pass.visit_module(modl)
    }

    fn visit_module(&mut self, modl: Module) -> Module {
        let Module { name, decls } = modl;

        decls.iter().for_each(|decl| {
            if self.inline_mark.contains(&decl.func) {
                self.func_map.insert(decl.func, decl.clone());
            }
        });

        let decls: Vec<FuncDecl> = decls
            .into_iter()
            .map(|decl| self.visit_func_decl(decl))
            .collect();

        Module { name, decls }
    }

    fn visit_func_decl(&mut self, decl: FuncDecl) -> FuncDecl {
        let FuncDecl {
            func,
            cont,
            pars,
            body,
        } = decl;
        let body = self.visit_expr(body);
        FuncDecl {
            func,
            cont,
            pars,
            body,
        }
    }

    fn visit_cont_decl(&mut self, decl: ContDecl) -> ContDecl {
        let ContDecl { cont, pars, body } = decl;
        let body = self.visit_expr(body);
        ContDecl { cont, pars, body }
    }

    fn visit_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Decls { funcs, conts, body } => {
                for decl in funcs.iter() {
                    if self.inline_mark.contains(&decl.func) {
                        self.func_map.insert(decl.func, decl.clone());
                    }
                }
                for decl in conts.iter() {
                    if self.inline_mark.contains(&decl.cont) {
                        self.cont_map.insert(decl.cont, decl.clone());
                    }
                }
                let funcs: Vec<FuncDecl> = funcs
                    .into_iter()
                    .map(|decl| self.visit_func_decl(decl))
                    .collect();
                let conts: Vec<ContDecl> = conts
                    .into_iter()
                    .map(|decl| self.visit_cont_decl(decl))
                    .collect();

                let body = Box::new(self.visit_expr(*body));

                if funcs.is_empty() && conts.is_empty() {
                    *body
                } else {
                    Expr::Decls { funcs, conts, body }
                }
            }
            Expr::Prim {
                bind,
                prim,
                args,
                rest,
            } => {
                let rest = Box::new(self.visit_expr(*rest));
                Expr::Prim {
                    bind,
                    prim,
                    args,
                    rest,
                }
            }
            Expr::Call { func, cont, args } => {
                if let Some(decl) = self.func_map.remove(&func) {
                    let FuncDecl {
                        func: func2,
                        cont: cont2,
                        pars,
                        body,
                    } = decl;
                    assert_eq!(func, func2);
                    assert_eq!(args.len(), pars.len());
                    pars.into_iter().zip(args.into_iter()).fold(
                        // this have to be const-folded!
                        Expr::Prim {
                            bind: cont2,
                            prim: PrimOpr::Move,
                            args: vec![Atom::Var(cont)],
                            rest: Box::new(body),
                        },
                        |rest, (par, arg)| Expr::Prim {
                            bind: par,
                            prim: PrimOpr::Move,
                            args: vec![arg],
                            rest: Box::new(rest),
                        },
                    )
                } else {
                    Expr::Call { func, cont, args }
                }
            }
            Expr::Jump { cont, args } => {
                if let Some(decl) = self.cont_map.remove(&cont) {
                    let ContDecl {
                        cont: cont2,
                        pars,
                        body,
                    } = decl;
                    assert_eq!(cont, cont2);
                    assert_eq!(args.len(), pars.len());
                    pars.into_iter()
                        .zip(args.into_iter())
                        .fold(body, |rest, (par, arg)| Expr::Prim {
                            bind: par,
                            prim: PrimOpr::Move,
                            args: vec![arg],
                            rest: Box::new(rest),
                        })
                } else {
                    Expr::Jump { cont, args }
                }
            }
            Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            } => {
                let trbr = Box::new(self.visit_expr(*trbr));
                let flbr = Box::new(self.visit_expr(*flbr));
                Expr::Ifte {
                    cond,
                    args,
                    trbr,
                    flbr,
                }
            }
            Expr::Switch { arg, brchs, dflt } => {
                let dflt = dflt.map(|dflt| Box::new(self.visit_expr(*dflt)));
                let brchs = brchs
                    .into_iter()
                    .map(|(i, brch)| (i, self.visit_expr(brch)))
                    .collect();
                Expr::Switch { arg, brchs, dflt }
            }
            Expr::Retn { res } => Expr::Retn { res },
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn inline_test() {
    let s = r#"
module Test where
func test(k):
    decls
        func f(k1, x1):
            call g(k1, x1);
        func g(k2, x2):
            let r = @iadd(x2, x2);
            jump k2(r);
    in
        call f(k, 42);
    end
"#;
    let expr = super::parser::parse_module(s).unwrap();
    println!("{}", expr);
    let mark = InlineScan::run(&expr);
    let expr = InlinePerform::run(expr, mark);
    println!("{}", expr);
}
