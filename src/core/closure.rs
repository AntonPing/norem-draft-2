use super::cps::*;
use crate::utils::ident::Ident;
use std::collections::HashSet;

pub struct ClosConv {
    toplevel: Vec<FuncDecl>,
    freevar: HashSet<Ident>,
}

impl ClosConv {
    pub fn run(modl: Module) -> Module {
        let mut pass = ClosConv {
            toplevel: Vec::new(),
            freevar: HashSet::new(),
        };
        let modl_name = modl.name;
        pass.visit_module(modl);
        assert!(pass.freevar.is_empty());
        let mut res = Module {
            name: modl_name,
            decls: pass.toplevel,
        };
        super::rename::Renamer::run(&mut res);
        res
    }

    fn visit_atom(&mut self, atom: Atom) -> Atom {
        if let Atom::Var(x) = atom {
            self.freevar.insert(x);
        }
        atom
    }

    fn visit_module(&mut self, modl: Module) {
        let Module { name: _, decls } = modl;
        let expr = Expr::Decls {
            funcs: decls,
            conts: Vec::new(),
            body: Box::new(Expr::Retn { res: Atom::Unit }),
        };
        self.visit_expr(expr);
    }

    fn visit_func_decl(&mut self, decl: FuncDecl) -> FuncDecl {
        let FuncDecl {
            func,
            cont,
            pars,
            body,
        } = decl;
        let body = self.visit_expr(body);
        for par in pars.iter() {
            self.freevar.remove(par);
        }
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
        for par in pars.iter() {
            self.freevar.remove(par);
        }
        ContDecl { cont, pars, body }
    }

    fn visit_expr(&mut self, expr: Expr) -> Expr {
        match expr {
            Expr::Decls { funcs, conts, body } => {
                // firstly, scan free variables
                let funcs: Vec<FuncDecl> = funcs
                    .into_iter()
                    .map(|decl| self.visit_func_decl(decl))
                    .collect();
                let conts: Vec<ContDecl> = conts
                    .into_iter()
                    .map(|decl| self.visit_cont_decl(decl))
                    .collect();

                let mut frees = self.freevar.clone();
                for decl in funcs.iter() {
                    frees.remove(&decl.func);
                }
                for decl in conts.iter() {
                    frees.remove(&decl.cont);
                }
                let free_funcs: Vec<Ident> = funcs.iter().map(|decl| decl.func).collect();

                // secondly, add closure parameter and unpack
                let funcs: Vec<FuncDecl> = funcs
                    .into_iter()
                    .map(|decl| {
                        let FuncDecl {
                            func,
                            cont,
                            pars,
                            body,
                        } = decl;
                        let c = Ident::fresh(&"c");
                        let pars: Vec<Ident> = [c].iter().chain(pars.iter()).copied().collect();
                        let body =
                            frees
                                .iter()
                                .enumerate()
                                .fold(body, |acc, (i, x)| Expr::Select {
                                    bind: *x,
                                    rec: Atom::Var(c),
                                    idx: i,
                                    rest: Box::new(acc),
                                });
                        let body = free_funcs.iter().fold(body, |acc, func| Expr::Record {
                            bind: *func,
                            args: vec![(false, Atom::Var(*func)), (false, Atom::Var(c))],
                            rest: Box::new(acc),
                        });

                        FuncDecl {
                            func,
                            cont,
                            pars,
                            body,
                        }
                    })
                    .collect();

                let c = Ident::fresh(&"c");

                let body = self.visit_expr(*body);

                let body =
                    funcs
                        .iter()
                        .map(|decl| decl.func)
                        .fold(body, |acc, func| Expr::Record {
                            bind: func,
                            args: vec![(false, Atom::Var(func)), (false, Atom::Var(c))],
                            rest: Box::new(acc),
                        });

                let body = Expr::Record {
                    bind: c,
                    args: frees.iter().map(|x| (false, Atom::Var(*x))).collect(),
                    rest: Box::new(body),
                };

                for decl in funcs {
                    self.freevar.remove(&decl.func);
                    self.toplevel.push(decl);
                }

                Expr::Decls {
                    funcs: Vec::new(),
                    conts,
                    body: Box::new(body),
                }
            }
            Expr::Prim {
                bind,
                prim,
                args,
                rest,
            } => {
                let rest = Box::new(self.visit_expr(*rest));
                self.freevar.remove(&bind);
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                Expr::Prim {
                    bind,
                    prim,
                    args,
                    rest,
                }
            }
            Expr::Record { bind, args, rest } => {
                let rest = Box::new(self.visit_expr(*rest));
                self.freevar.remove(&bind);
                let args: Vec<(bool, Atom)> = args
                    .into_iter()
                    .map(|arg| (arg.0, self.visit_atom(arg.1)))
                    .collect();
                Expr::Record { bind, args, rest }
            }
            Expr::Select {
                bind,
                rec,
                idx,
                rest,
            } => {
                let rest = Box::new(self.visit_expr(*rest));
                self.freevar.remove(&bind);
                let rec = self.visit_atom(rec);
                Expr::Select {
                    bind,
                    rec,
                    idx,
                    rest,
                }
            }
            Expr::Update {
                rec,
                idx,
                arg,
                rest,
            } => {
                let rest = Box::new(self.visit_expr(*rest));
                let rec = self.visit_atom(rec);
                let arg = self.visit_atom(arg);
                Expr::Update {
                    rec,
                    idx,
                    arg,
                    rest,
                }
            }
            Expr::Call { func, cont, args } => {
                self.visit_atom(Atom::Var(func));
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                let f = Ident::fresh(&"f");
                let c = Ident::fresh(&"c");
                Expr::Select {
                    bind: f,
                    rec: Atom::Var(func),
                    idx: 0,
                    rest: Box::new(Expr::Select {
                        bind: c,
                        rec: Atom::Var(func),
                        idx: 1,
                        rest: Box::new(Expr::Call {
                            func: f,
                            cont,
                            args: [Atom::Var(c)].into_iter().chain(args.into_iter()).collect(),
                        }),
                    }),
                }
            }
            Expr::Jump { cont, args } => {
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                Expr::Jump { cont, args }
            }
            Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            } => {
                let trbr = Box::new(self.visit_expr(*trbr));
                let flbr = Box::new(self.visit_expr(*flbr));
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
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
                    .map(|(i, brch)| (i, self.visit_expr(brch)))
                    .collect();
                let arg = self.visit_atom(arg);
                let dflt = dflt.map(|dflt| Box::new(self.visit_expr(*dflt)));
                Expr::Switch { arg, brchs, dflt }
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
module Test where
func f(k1, x1):
    decls
        func g(k2, x2):
            let r = @iadd(x1, x2);
            jump k2(r);
    in
        jump k1(g);
    end

func top(k):
    decls
        cont next(h):
            call h(k, 2);
    in
        call f(next, 1);
    end
"#;
    let modl = super::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let modl = super::optimize::Optimizer::run(modl);
    println!("{}\n", modl);
    let modl = ClosConv::run(modl);
    println!("{}\n", modl);
    let modl = super::optimize::Optimizer::run(modl);
    println!("{}\n", modl);
}

#[test]
#[ignore = "just to see result"]
fn clos_conv_test_2() {
    let s = r#"
module Test where
fn f(x) begin
    let y = @iadd(x, 1);
    return y;
end
fn g(z) begin
    let a = f(z);
    return a;
end
fn top() begin
    let r = g(42);
    return r;
end
"#;
    let modl = super::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let modl = super::optimize::Optimizer::run(modl);
    println!("{}\n", modl);
    let modl = ClosConv::run(modl);
    println!("{}\n", modl);
    let modl = super::optimize::Optimizer::run(modl);
    println!("{}\n", modl);
}

#[test]
#[ignore = "just to see result"]
fn clos_conv_test_3() {
    let s = r#"
module Test where
fn f(x) begin
    let one = @move(1);
    decl
        fn g(z) begin
            let a = @iadd(z, one);
            return a;
        end
    in
        let y = g(x);
        return y;
    end
end
fn top() begin
    let r = f(42);
    return r;
end
"#;
    let modl = super::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let modl = super::optimize::Optimizer::run(modl);
    println!("{}\n", modl);
    let modl = ClosConv::run(modl);
    println!("{}\n", modl);
    let modl = super::optimize::Optimizer::run(modl);
    println!("{}\n", modl);
}
