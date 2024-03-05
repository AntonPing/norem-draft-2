use super::cps::{self, Atom, IfCond, Module, PrimOpr};
use crate::utils::ident::Ident;
use std::collections::{HashMap, HashSet};

pub struct Optimizer {
    atom_map: HashMap<Ident, Atom>,
    record_map: HashMap<Ident, Vec<Atom>>,
    used_set: HashSet<Ident>,
}

impl Optimizer {
    pub fn run(modl: Module) -> Module {
        let mut pass = Optimizer {
            atom_map: HashMap::new(),
            record_map: HashMap::new(),
            used_set: HashSet::new(),
        };
        pass.visit_module(modl)
    }

    fn visit_atom(&mut self, arg: Atom) -> Atom {
        let mut res = arg;
        while res.is_var() {
            let var = res.unwrap_var();
            if let Some(new_res) = self.atom_map.get(&var) {
                res = *new_res;
            } else {
                break;
            }
        }
        res
    }

    fn mark_val_used(&mut self, arg: &Atom) {
        if let Atom::Var(var) = arg {
            self.used_set.insert(*var);
        }
    }

    fn visit_module(&mut self, modl: cps::Module) -> cps::Module {
        let Module { name, decls } = modl;

        let func_names: Vec<Ident> = decls.iter().map(|decl| decl.func).collect();

        let decls: Vec<cps::FuncDecl> = decls
            .into_iter()
            .map(|decl| {
                let cps::FuncDecl {
                    func,
                    cont,
                    pars,
                    body,
                } = decl;
                let body = self.visit_expr(body);
                self.used_set.remove(&cont);
                for par in pars.iter() {
                    self.used_set.remove(par);
                }
                for name in func_names.iter() {
                    self.used_set.remove(name);
                }
                cps::FuncDecl {
                    func,
                    cont,
                    pars,
                    body,
                }
            })
            .collect();

        Module { name, decls }
    }

    fn visit_expr(&mut self, expr: cps::Expr) -> cps::Expr {
        match expr {
            cps::Expr::Decls { funcs, conts, body } => {
                let func_names: Vec<Ident> = funcs.iter().map(|decl| decl.func).collect();
                let cont_names: Vec<Ident> = conts.iter().map(|decl| decl.cont).collect();
                let decl_names: Vec<Ident> = func_names
                    .iter()
                    .chain(cont_names.iter())
                    .copied()
                    .collect();

                let mut call_graph: HashMap<Ident, HashSet<Ident>> = decl_names
                    .iter()
                    .map(|name| (*name, HashSet::new()))
                    .collect();

                let funcs: Vec<cps::FuncDecl> = funcs
                    .into_iter()
                    .map(|decl| {
                        let cps::FuncDecl {
                            func,
                            cont,
                            pars,
                            body,
                        } = decl;
                        let body = self.visit_expr(body);
                        self.used_set.remove(&cont);
                        for par in pars.iter() {
                            self.used_set.remove(par);
                        }
                        for name in decl_names.iter() {
                            if self.used_set.remove(name) {
                                call_graph.get_mut(&func).unwrap().insert(*name);
                            }
                        }
                        cps::FuncDecl {
                            func,
                            cont,
                            pars,
                            body,
                        }
                    })
                    .collect();

                let conts: Vec<cps::ContDecl> = conts
                    .into_iter()
                    .map(|decl| {
                        let cps::ContDecl { cont, pars, body } = decl;
                        let body = self.visit_expr(body);
                        for par in pars.iter() {
                            self.used_set.remove(par);
                        }
                        for name in decl_names.iter() {
                            if self.used_set.remove(name) {
                                call_graph.get_mut(&cont).unwrap().insert(*name);
                            }
                        }
                        cps::ContDecl { cont, pars, body }
                    })
                    .collect();

                let body = Box::new(self.visit_expr(*body));

                let start: HashSet<Ident> = decl_names
                    .iter()
                    .filter(|name| self.used_set.remove(name))
                    .copied()
                    .collect();

                let reachable = calculate_reachable(&call_graph, &start);

                let funcs: Vec<_> = funcs
                    .into_iter()
                    .filter(|decl| reachable.contains(&decl.func))
                    .collect();

                let conts: Vec<_> = conts
                    .into_iter()
                    .filter(|decl| reachable.contains(&decl.cont))
                    .collect();

                if funcs.is_empty() && conts.is_empty() {
                    *body
                } else {
                    cps::Expr::Decls { funcs, conts, body }
                }
            }
            cps::Expr::Prim {
                bind,
                prim,
                args,
                rest,
            } => {
                assert!(prim.get_arity() == None || prim.get_arity() == Some(args.len()));
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                match (prim, &args[..]) {
                    (PrimOpr::IAdd, [Atom::Int(a), Atom::Int(b)]) => {
                        self.atom_map.insert(bind, Atom::Int(a + b));
                        self.visit_expr(*rest)
                    }
                    (PrimOpr::ISub, [Atom::Int(a), Atom::Int(b)]) => {
                        self.atom_map.insert(bind, Atom::Int(a - b));
                        self.visit_expr(*rest)
                    }
                    (PrimOpr::IMul, [Atom::Int(a), Atom::Int(b)]) => {
                        self.atom_map.insert(bind, Atom::Int(a * b));
                        self.visit_expr(*rest)
                    }
                    (PrimOpr::Move, [atom]) => {
                        self.atom_map.insert(bind, *atom);
                        self.visit_expr(*rest)
                    }
                    (PrimOpr::Record, []) => {
                        self.atom_map.insert(bind, Atom::Unit);
                        self.visit_expr(*rest)
                    }
                    (PrimOpr::Record, _) => {
                        self.record_map.insert(bind, args.clone());
                        let cont = self.visit_expr(*rest);
                        if self.used_set.contains(&bind) {
                            self.used_set.remove(&bind);
                            args.iter().for_each(|arg| self.mark_val_used(arg));
                            cps::Expr::Prim {
                                bind,
                                prim,
                                args,
                                rest: Box::new(cont),
                            }
                        } else {
                            cont
                        }
                    }
                    (PrimOpr::Select, [rec, idx]) => {
                        if let Some(elems) = self.record_map.get(&rec.unwrap_var()) {
                            self.atom_map.insert(bind, elems[idx.unwrap_int() as usize]);
                            self.visit_expr(*rest)
                        } else {
                            let cont = self.visit_expr(*rest);
                            if self.used_set.contains(&bind) {
                                self.used_set.remove(&bind);
                                args.iter().for_each(|arg| self.mark_val_used(arg));
                                cps::Expr::Prim {
                                    bind,
                                    prim,
                                    args,
                                    rest: Box::new(cont),
                                }
                            } else {
                                cont
                            }
                        }
                    }
                    _ => {
                        let cont = self.visit_expr(*rest);
                        // unused primitive elimination
                        if !self.used_set.contains(&bind) && prim.is_pure() {
                            cont
                        } else {
                            self.used_set.remove(&bind);
                            args.iter().for_each(|arg| self.mark_val_used(arg));
                            cps::Expr::Prim {
                                bind,
                                prim,
                                args,
                                rest: Box::new(cont),
                            }
                        }
                    }
                }
            }
            cps::Expr::Call { func, cont, args } => {
                let func = self.visit_atom(Atom::Var(func)).unwrap_var();
                let cont = self.visit_atom(Atom::Var(cont)).unwrap_var();
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                self.used_set.insert(func);
                self.used_set.insert(cont);
                args.iter().for_each(|arg| self.mark_val_used(arg));
                cps::Expr::Call { func, cont, args }
            }
            cps::Expr::Jump { cont, args } => {
                let cont = self.visit_atom(Atom::Var(cont)).unwrap_var();
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                self.used_set.insert(cont);
                args.iter().for_each(|arg| self.mark_val_used(arg));
                cps::Expr::Jump { cont, args }
            }
            cps::Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            } => {
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                match (cond, &args[..]) {
                    (IfCond::BTrue, [Atom::Bool(p)]) => {
                        if *p {
                            self.visit_expr(*trbr)
                        } else {
                            self.visit_expr(*flbr)
                        }
                    }
                    (IfCond::BFalse, [Atom::Bool(p)]) => {
                        if !*p {
                            self.visit_expr(*trbr)
                        } else {
                            self.visit_expr(*flbr)
                        }
                    }
                    (IfCond::ICmpGr, [Atom::Int(a), Atom::Int(b)]) => {
                        if a > b {
                            self.visit_expr(*trbr)
                        } else {
                            self.visit_expr(*flbr)
                        }
                    }
                    (IfCond::ICmpEq, [Atom::Int(a), Atom::Int(b)]) => {
                        if a == b {
                            self.visit_expr(*trbr)
                        } else {
                            self.visit_expr(*flbr)
                        }
                    }
                    (IfCond::ICmpLs, [Atom::Int(a), Atom::Int(b)]) => {
                        if a < b {
                            self.visit_expr(*trbr)
                        } else {
                            self.visit_expr(*flbr)
                        }
                    }
                    _ => {
                        let trbr = Box::new(self.visit_expr(*trbr));
                        let flbr = Box::new(self.visit_expr(*flbr));
                        args.iter().for_each(|arg| self.mark_val_used(arg));
                        cps::Expr::Ifte {
                            cond,
                            args,
                            trbr,
                            flbr,
                        }
                    }
                }
            }
            cps::Expr::Switch { arg, brchs, dflt } => {
                let arg = self.visit_atom(arg);

                if let Atom::Int(n) = arg {
                    if let Some((_, brch)) = brchs.into_iter().find(|(i, _)| *i == n as usize) {
                        self.visit_expr(brch)
                    } else if let Some(dflt) = dflt {
                        self.visit_expr(*dflt)
                    } else {
                        panic!("switch fallthrough without default branch!")
                    }
                } else {
                    let brchs = brchs
                        .into_iter()
                        .map(|(i, brch)| (i, self.visit_expr(brch)))
                        .collect();
                    let dflt = dflt.map(|dflt| Box::new(self.visit_expr(*dflt)));
                    self.mark_val_used(&arg);
                    cps::Expr::Switch { arg, brchs, dflt }
                }
            }
            cps::Expr::Retn { res } => {
                let res = self.visit_atom(res);
                self.mark_val_used(&res);
                cps::Expr::Retn { res }
            }
        }
    }
}

fn calculate_reachable(
    call_graph: &HashMap<Ident, HashSet<Ident>>,
    start: &HashSet<Ident>,
) -> HashSet<Ident> {
    let mut reachable: HashSet<Ident> = start.clone();
    let mut new_reachable: Vec<Ident> = Vec::new();
    loop {
        for name in reachable.iter() {
            for new_name in &call_graph[name] {
                if !reachable.contains(new_name) {
                    new_reachable.push(*new_name);
                }
            }
        }
        if new_reachable.is_empty() {
            return reachable;
        } else {
            while let Some(new_name) = new_reachable.pop() {
                reachable.insert(new_name);
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn optimize_test_const_fold() {
    let s = r#"
module Test where
func f(k):
    let x = @iadd(1, 2);
    let r = @record(x, x);
    let x1 = @select(r, 0);
    let x2 = @select(r, 1);
    let y = @iadd(x1, x2);
    let z = @iadd(x1, y);
    return z;
"#;
    let modl = super::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let expr = Optimizer::run(modl);
    let expr = Optimizer::run(expr);
    println!("{}\n", expr);
}

#[test]
#[ignore = "just to see result"]
fn optimize_test_dead_elim() {
    let s = r#"
module Test where
func f(k):
    let x = @iadd(a, b);
    let y = @iadd(x, c);
    let z = @iadd(x, y);
    return y;
"#;
    let expr = super::parser::parse_module(s).unwrap();
    println!("{}\n", expr);
    let expr = Optimizer::run(expr);
    println!("{}\n", expr);
}

#[test]
#[ignore = "just to see result"]
fn optimize_test_unused_func() {
    let s = r#"
module Test where
func test(k):
    decls
        func f(k1):
            call h(k1, 42);
        func g(k2, x2):
            call h(k2, 42);
        func h(k3, x3):
            jump k3(x3);
    in
        call f(k);
    end
"#;
    let expr = super::parser::parse_module(s).unwrap();
    println!("{}\n", expr);
    let expr = Optimizer::run(expr);
    println!("{}\n", expr);
}
