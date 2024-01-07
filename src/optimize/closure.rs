use super::anf::*;
use crate::utils::ident::Ident;
use std::collections::HashSet;

pub struct ClosConv {
    toplevel: Vec<Decl>,
    freevar: HashSet<Ident>,
}

impl ClosConv {
    pub fn run(expr: Expr) -> (Vec<Decl>, Expr) {
        let mut pass = ClosConv {
            toplevel: Vec::new(),
            freevar: HashSet::new(),
        };
        let mut expr = pass.visit_expr(expr);
        assert!(pass.freevar.is_empty());
        super::rename::Renamer::run(&mut expr);
        for decl in pass.toplevel.iter_mut() {
            super::rename::Renamer::run_decl(decl);
        }
        (pass.toplevel, expr)
    }

    fn visit_atom(&mut self, atom: Atom) -> Atom {
        if let Atom::Var(x) = atom {
            self.freevar.insert(x);
        }
        atom
    }

    fn visit_decl(&mut self, decl: Decl) -> Decl {
        let Decl { func, pars, body } = decl;
        let body = self.visit_expr(body);
        for par in pars.iter() {
            self.freevar.remove(par);
        }
        Decl { func, pars, body }
    }

    fn visit_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Decls { decls, cont } => {
                // first time, scan free variables
                let decls: Vec<Decl> = decls
                    .into_iter()
                    .map(|decl| self.visit_decl(decl))
                    .collect();

                let mut frees = self.freevar.clone();
                decls.iter().for_each(|decl| {
                    frees.remove(&decl.func);
                });

                let free_funcs: Vec<Ident> = decls.iter().map(|decl| decl.func).collect();

                // second time, add closure parameter and unpack
                let decls: Vec<Decl> = decls
                    .into_iter()
                    .map(|decl| {
                        let Decl { func, pars, body } = decl;
                        let c = Ident::fresh(&"c");
                        let pars: Vec<Ident> = [c].iter().chain(pars.iter()).copied().collect();
                        let body = frees
                            .iter()
                            .enumerate()
                            .fold(body, |acc, (i, x)| Expr::Prim {
                                bind: *x,
                                prim: PrimOpr::Select,
                                args: vec![Atom::Var(c), Atom::Int(i as i64)],
                                cont: Box::new(acc),
                            });
                        let body = free_funcs.iter().fold(body, |acc, func| Expr::Prim {
                            bind: *func,
                            prim: PrimOpr::Record,
                            args: vec![Atom::Var(*func), Atom::Var(c)],
                            cont: Box::new(acc),
                        });

                        Decl { func, pars, body }
                    })
                    .collect();

                let cont = self.visit_expr(*cont);

                let c = Ident::fresh(&"c");

                let cont = decls
                    .iter()
                    .map(|decl| decl.func)
                    .fold(cont, |acc, func| Expr::Prim {
                        bind: func,
                        prim: PrimOpr::Record,
                        args: vec![Atom::Var(func), Atom::Var(c)],
                        cont: Box::new(acc),
                    });

                let cont = Expr::Prim {
                    bind: c,
                    prim: PrimOpr::Record,
                    args: frees.iter().map(|x| Atom::Var(*x)).collect(),
                    cont: Box::new(cont),
                };

                for decl in decls {
                    self.freevar.remove(&decl.func);
                    self.toplevel.push(decl);
                }

                cont
            }
            Expr::Prim {
                bind,
                prim,
                args,
                cont,
            } => {
                let cont = Box::new(self.visit_expr(*cont));
                self.freevar.remove(&bind);
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
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
                self.freevar.remove(&bind);
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                let func = self.visit_atom(func);
                let f = Ident::fresh(&"f");
                let c = Ident::fresh(&"c");
                Expr::Prim {
                    bind: f,
                    prim: PrimOpr::Select,
                    args: vec![func, Atom::Int(0)],
                    cont: Box::new(Expr::Prim {
                        bind: c,
                        prim: PrimOpr::Select,
                        args: vec![func, Atom::Int(1)],
                        cont: Box::new(Expr::Call {
                            bind,
                            func: Atom::Var(f),
                            args: [Atom::Var(c)].into_iter().chain(args.into_iter()).collect(),
                            cont,
                        }),
                    }),
                }
            }
            Expr::Retn { res } => {
                let res = self.visit_atom(res);
                Expr::Retn { res }
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn clos_conv_test_1() {
    let s = r#"
decl
    fn f(x) begin
        decl
            fn g(y) begin
                let z = @iadd(x, y);
                return z;
            end
        in
            return g;
        end
    end
in
    let h = f(1);
    let r = h(2);
    return r;
end
"#;
    let expr = super::parser::parse_expr(s).unwrap();
    println!("{}\n", expr);
    let (toplevel, expr) = ClosConv::run(expr);
    for decl in toplevel {
        println!("{}\n", decl);
    }
    println!("{}\n", expr);
}

#[test]
#[ignore = "just to see result"]
fn clos_conv_test_2() {
    let s = r#"
decl
    fn f(x) begin
        let y = @iadd(x, 1);
        return y;
    end
    fn g(z) begin
        let a = f(z);
        return a;
    end
in
    let r = g(42);
    return r;
end
"#;
    let expr = super::parser::parse_expr(s).unwrap();
    println!("{}\n", expr);
    let (toplevel, expr) = ClosConv::run(expr);
    for decl in toplevel {
        println!("{}\n", decl);
    }
    println!("{}\n", expr);
}

#[test]
#[ignore = "just to see result"]
fn clos_conv_test_3() {
    let s = r#"
decl
    fn f(x) begin
        decl
            fn g(z) begin
                let a = f(z);
                return a;
            end
        in
            let y = @iadd(x, 1);
            return y;
        end
    end
in
    let r = f(42);
    return r;
end
"#;
    let expr = super::parser::parse_expr(s).unwrap();
    println!("{}\n", expr);
    let (toplevel, expr) = ClosConv::run(expr);
    for decl in toplevel {
        println!("{}\n", decl);
    }
    println!("{}\n", expr);
}
