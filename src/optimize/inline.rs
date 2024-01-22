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
            Expr::Brch { prim, args, conts } => todo!(),
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

        let decls: Vec<Decl> = decls
            .into_iter()
            .map(|decl| self.visit_decl(decl))
            .collect();

        decls.iter().for_each(|decl| {
            if self.inline_mark.contains(&decl.func) {
                self.map.insert(decl.func, decl.clone());
            }
        });

        Module { name, decls }
    }

    fn visit_decl(&mut self, decl: Decl) -> Decl {
        let Decl { func, pars, body } = decl;
        let body = self.visit_expr(body);
        Decl { func, pars, body }
    }

    fn visit_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Decls { decls, cont } => {
                let decls: Vec<Decl> = decls
                    .into_iter()
                    .map(|decl| self.visit_decl(decl))
                    .collect();

                let decls: Vec<Decl> = decls
                    .into_iter()
                    .flat_map(|decl| {
                        if self.inline_mark.contains(&decl.func) {
                            self.map.insert(decl.func, decl);
                            None
                        } else {
                            Some(decl)
                        }
                    })
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
            Expr::Brch { prim, args, conts } => todo!(),
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
            Expr::Retn { res } => Expr::Retn { res },
        }
    }
}

fn tailing(expr: Expr, bind: Ident, cont: Expr) -> Expr {
    match expr {
        Expr::Decls { decls, cont: cont2 } => {
            let cont = Box::new(tailing(*cont2, bind, cont));
            Expr::Decls { decls, cont }
        }
        Expr::Prim {
            bind,
            prim,
            args,
            cont: cont2,
        } => {
            let cont = Box::new(tailing(*cont2, bind, cont));
            Expr::Prim {
                bind,
                prim,
                args,
                cont,
            }
        }
        Expr::Brch { prim, args, conts } => todo!(),
        Expr::Call {
            bind,
            func,
            args,
            cont: cont2,
        } => {
            let cont = Box::new(tailing(*cont2, bind, cont));
            Expr::Call {
                bind,
                func,
                args,
                cont,
            }
        }
        Expr::Retn { res } => Expr::Prim {
            bind,
            prim: PrimOpr::Move,
            args: vec![res],
            cont: Box::new(cont),
        },
    }
}

fn inline_call(decl: Decl, bind: Ident, func: Ident, args: Vec<Atom>, cont: Expr) -> Expr {
    let Decl {
        func: func2,
        pars,
        body,
    } = decl;
    assert_eq!(func, func2);
    assert_eq!(args.len(), pars.len());

    pars.into_iter()
        .zip(args.into_iter())
        .fold(tailing(body, bind, cont), |tail, (par, arg)| Expr::Prim {
            bind: par,
            prim: PrimOpr::Move,
            args: vec![arg],
            cont: Box::new(tail),
        })
}

#[test]
#[ignore = "just to see result"]
fn inline_test() {
    let s = r#"
module test where
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
