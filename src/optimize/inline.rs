use super::anf::*;
use crate::optimize::anf::PrimOpr;
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
            self.visit_decl(decl);
        }
    }

    fn visit_decl(&mut self, decl: &Decl) {
        let Decl {
            func: _,
            pars,
            body,
            info: _,
        } = decl;
        self.visit_expr(body);
        pars.iter().for_each(|par| {
            self.occur_map.remove(par);
        });
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Decls { decls, cont } => {
                self.visit_expr(cont);
                for decl in decls {
                    self.visit_decl(decl)
                }
                for decl in decls {
                    let name = decl.func;
                    let res = self.occur_map.remove(&name);
                    if res == Some((1, 1)) {
                        // todo: some other heuristic
                        self.inline_mark.insert(name);
                    }
                }
            }
            Expr::Prim {
                bind,
                prim: _,
                args,
                cont,
            } => {
                self.visit_expr(cont);
                args.iter().for_each(|arg| self.visit_atom(arg));
                self.occur_map.remove(bind);
            }
            Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                self.visit_expr(cont);
                args.iter().for_each(|arg| self.visit_atom(arg));
                if let Atom::Var(func) = func {
                    let res = self.occur_map.get_mut(&func);
                    if let Some((n, m)) = res {
                        *n += 1;
                        *m += 1;
                    } else {
                        self.occur_map.insert(*func, (1, 1));
                    }
                }
                self.occur_map.remove(bind);
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
    map: HashMap<Ident, Decl>,
}

impl InlinePerform {
    pub fn run(modl: Module, mark: HashSet<Ident>) -> Module {
        let mut pass = InlinePerform {
            inline_mark: mark,
            map: HashMap::new(),
        };
        pass.visit_module(modl)
    }

    fn visit_module(&mut self, modl: Module) -> Module {
        let Module { name, decls } = modl;

        decls.iter().for_each(|decl| {
            if self.inline_mark.contains(&decl.func) {
                self.map.insert(decl.func, decl.clone());
            }
        });

        let decls: Vec<Decl> = decls
            .into_iter()
            .map(|decl| self.visit_decl(decl))
            .collect();

        Module { name, decls }
    }

    fn visit_decl(&mut self, decl: Decl) -> Decl {
        let Decl {
            func,
            pars,
            body,
            info,
        } = decl;
        let body = self.visit_expr(body);
        Decl {
            func,
            pars,
            body,
            info,
        }
    }

    fn visit_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Decls { decls, cont } => {
                let decls: Vec<Decl> = decls
                    .into_iter()
                    .map(|decl| {
                        if self.inline_mark.contains(&decl.func) {
                            self.map.insert(decl.func, decl.clone());
                        }
                        decl
                    })
                    .collect();

                let decls: Vec<Decl> = decls
                    .into_iter()
                    .map(|decl| self.visit_decl(decl))
                    .collect();

                let cont = Box::new(self.visit_expr(*cont));

                if decls.is_empty() {
                    *cont
                } else {
                    Expr::Decls { decls, cont }
                }
            }
            Expr::Prim {
                bind,
                prim,
                args,
                cont,
            } => {
                let cont = Box::new(self.visit_expr(*cont));
                Expr::Prim {
                    bind,
                    prim,
                    args,
                    cont,
                }
            }
            Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                let cont = Box::new(self.visit_expr(*cont));
                if let Atom::Var(func) = func {
                    if let Some(decl) = self.map.remove(&func) {
                        return inline_call(decl, bind, func, args, *cont);
                    }
                }
                Expr::Call {
                    bind,
                    func,
                    args,
                    cont,
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

fn continue_with(joins: &mut HashSet<Ident>, expr: Expr, hole: Ident, rest: Expr) -> Expr {
    match expr {
        Expr::Decls { decls, cont } => {
            for decl in decls.iter() {
                if decl.info == CallInfo::JoinPoint {
                    joins.insert(decl.func);
                }
            }
            let decls = decls
                .into_iter()
                .map(|decl| {
                    if decl.info == CallInfo::JoinPoint {
                        let Decl {
                            func,
                            pars,
                            body,
                            info,
                        } = decl;
                        let body = continue_with(joins, body, hole, rest.clone());
                        Decl {
                            func,
                            pars,
                            body,
                            info,
                        }
                    } else {
                        decl
                    }
                })
                .collect();
            let cont = Box::new(continue_with(joins, *cont, hole, rest));
            Expr::Decls { decls, cont }
        }
        Expr::Prim {
            bind,
            prim,
            args,
            cont,
        } => {
            let cont = Box::new(continue_with(joins, *cont, hole, rest));
            Expr::Prim {
                bind,
                prim,
                args,
                cont,
            }
        }
        Expr::Call {
            bind,
            func,
            args,
            cont,
        } => {
            if let Atom::Var(name) = func {
                if joins.contains(&name) {
                    *cont
                } else {
                    let cont = Box::new(continue_with(joins, *cont, hole, rest));
                    Expr::Call {
                        bind,
                        func,
                        args,
                        cont,
                    }
                }
            } else {
                unreachable!()
            }
        }
        Expr::Ifte {
            cond,
            args,
            trbr,
            flbr,
        } => {
            let trbr = Box::new(continue_with(joins, *trbr, hole, rest.clone()));
            let flbr = Box::new(continue_with(joins, *flbr, hole, rest));
            Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            }
        }
        Expr::Switch { arg, brchs, dflt } => {
            let brchs = brchs
                .into_iter()
                .map(|(i, brch)| (i, continue_with(joins, brch, hole, rest.clone())))
                .collect();
            let dflt = dflt.map(|dflt| Box::new(continue_with(joins, *dflt, hole, rest)));
            Expr::Switch { arg, brchs, dflt }
        }
        Expr::Retn { res } => Expr::Prim {
            bind: hole,
            prim: PrimOpr::Move,
            args: vec![res],
            cont: Box::new(rest),
        },
    }
}

fn inline_call(decl: Decl, bind: Ident, func: Ident, args: Vec<Atom>, cont: Expr) -> Expr {
    let Decl {
        func: func2,
        pars,
        body,
        info: _,
    } = decl;
    assert_eq!(func, func2);
    assert_eq!(args.len(), pars.len());
    pars.into_iter().zip(args.into_iter()).fold(
        continue_with(&mut HashSet::new(), body, bind, cont),
        |tail, (par, arg)| Expr::Prim {
            bind: par,
            prim: PrimOpr::Move,
            args: vec![arg],
            cont: Box::new(tail),
        },
    )
}

#[test]
#[ignore = "just to see result"]
fn inline_test() {
    let s = r#"
module Test where
fn g(x) begin
    decl
        fn f(x) begin
        return x; 
        end
    in
        let y = f(42);
        return y;
    end
end
"#;
    let expr = super::parser::parse_module(s).unwrap();
    println!("{}", expr);
    let mark = InlineScan::run(&expr);
    let expr = InlinePerform::run(expr, mark);
    println!("{}", expr);
}
