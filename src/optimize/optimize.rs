use super::anf::{self, Atom, Module, PrimOpr};
use crate::{optimize::anf::BrchOpr, utils::ident::Ident};
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

    fn mark_used(&mut self, arg: &Atom) {
        if let Atom::Var(var) = arg {
            self.used_set.insert(*var);
        }
    }

    fn visit_module(&mut self, modl: anf::Module) -> anf::Module {
        let Module { name, decls } = modl;

        let func_names: Vec<Ident> = decls.iter().map(|decl| decl.func).collect();

        let decls: Vec<anf::Decl> = decls
            .into_iter()
            .map(|decl| {
                let anf::Decl {
                    func,
                    pars,
                    body,
                    info,
                } = decl;
                let body = self.visit_expr(body);
                for par in pars.iter() {
                    self.used_set.remove(par);
                }
                for name in func_names.iter() {
                    self.used_set.remove(name);
                }
                anf::Decl {
                    func,
                    pars,
                    body,
                    info,
                }
            })
            .collect();

        Module { name, decls }
    }

    fn visit_expr(&mut self, expr: anf::Expr) -> anf::Expr {
        match expr {
            anf::Expr::Decls { decls, cont } => {
                let func_names: Vec<Ident> = decls.iter().map(|decl| decl.func).collect();

                let mut call_graph: HashMap<Ident, HashSet<Ident>> = func_names
                    .iter()
                    .map(|name| (*name, HashSet::new()))
                    .collect();

                let decls: Vec<anf::Decl> = decls
                    .into_iter()
                    .map(|decl| {
                        let anf::Decl {
                            func,
                            pars,
                            body,
                            info,
                        } = decl;
                        let body = self.visit_expr(body);
                        for par in pars.iter() {
                            self.used_set.remove(par);
                        }
                        for name in func_names.iter() {
                            if self.used_set.remove(name) {
                                call_graph.get_mut(&func).unwrap().insert(*name);
                            }
                        }
                        anf::Decl {
                            func,
                            pars,
                            body,
                            info,
                        }
                    })
                    .collect();

                let cont = Box::new(self.visit_expr(*cont));

                let start: HashSet<Ident> = func_names
                    .iter()
                    .filter(|name| self.used_set.remove(name))
                    .copied()
                    .collect();

                let reachable = calculate_reachable(&call_graph, &start);

                let decls = decls
                    .into_iter()
                    .filter(|decl| reachable.contains(&decl.func))
                    .collect();

                anf::Expr::Decls { decls, cont }
            }
            anf::Expr::Prim {
                bind,
                prim,
                args,
                cont,
            } => {
                assert!(prim.get_arity() == None || prim.get_arity() == Some(args.len()));
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                match (prim, &args[..]) {
                    (PrimOpr::IAdd, [Atom::Int(a), Atom::Int(b)]) => {
                        self.atom_map.insert(bind, Atom::Int(a + b));
                        self.visit_expr(*cont)
                    }
                    (PrimOpr::ISub, [Atom::Int(a), Atom::Int(b)]) => {
                        self.atom_map.insert(bind, Atom::Int(a - b));
                        self.visit_expr(*cont)
                    }
                    (PrimOpr::IMul, [Atom::Int(a), Atom::Int(b)]) => {
                        self.atom_map.insert(bind, Atom::Int(a * b));
                        self.visit_expr(*cont)
                    }
                    (PrimOpr::Move, [atom]) => {
                        self.atom_map.insert(bind, *atom);
                        self.visit_expr(*cont)
                    }
                    (PrimOpr::Record, []) => {
                        self.atom_map.insert(bind, Atom::Unit);
                        self.visit_expr(*cont)
                    }
                    (PrimOpr::Record, _) => {
                        self.record_map.insert(bind, args.clone());
                        let cont = self.visit_expr(*cont);
                        if self.used_set.contains(&bind) {
                            self.used_set.remove(&bind);
                            args.iter().for_each(|arg| self.mark_used(arg));
                            anf::Expr::Prim {
                                bind,
                                prim,
                                args,
                                cont: Box::new(cont),
                            }
                        } else {
                            cont
                        }
                    }
                    (PrimOpr::Select, [rec, idx]) => {
                        if let Some(elems) = self.record_map.get(&rec.unwrap_var()) {
                            self.atom_map.insert(bind, elems[idx.unwrap_int() as usize]);
                            self.visit_expr(*cont)
                        } else {
                            let cont = self.visit_expr(*cont);
                            if self.used_set.contains(&bind) {
                                self.used_set.remove(&bind);
                                args.iter().for_each(|arg| self.mark_used(arg));
                                anf::Expr::Prim {
                                    bind,
                                    prim,
                                    args,
                                    cont: Box::new(cont),
                                }
                            } else {
                                cont
                            }
                        }
                    }
                    _ => {
                        let cont = self.visit_expr(*cont);
                        // unused primitive elimination
                        // do purity check if we have impure primitive in the future
                        if self.used_set.contains(&bind) {
                            self.used_set.remove(&bind);
                            args.iter().for_each(|arg| self.mark_used(arg));
                            anf::Expr::Prim {
                                bind,
                                prim,
                                args,
                                cont: Box::new(cont),
                            }
                        } else {
                            cont
                        }
                    }
                }
            }
            anf::Expr::Brch { prim, args, conts } => {
                assert!(prim.get_arity() == None || prim.get_arity() == Some(args.len()));
                assert!(
                    prim.get_cont_arity() == None || prim.get_cont_arity() == Some(conts.len())
                );
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                match (prim, &args[..]) {
                    (BrchOpr::Ifte, [Atom::Bool(true)]) => {
                        self.visit_expr(conts.into_iter().nth(0).unwrap())
                    }
                    (BrchOpr::Ifte, [Atom::Bool(false)]) => {
                        self.visit_expr(conts.into_iter().nth(1).unwrap())
                    }
                    (BrchOpr::Switch, [Atom::Int(n)]) => {
                        let cont = conts.into_iter().nth(*n as usize).unwrap();
                        self.visit_expr(cont)
                    }
                    _ => {
                        let conts = conts
                            .into_iter()
                            .map(|cont| self.visit_expr(cont))
                            .collect();
                        args.iter().for_each(|arg| self.mark_used(arg));
                        anf::Expr::Brch { prim, args, conts }
                    }
                }
            }
            anf::Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                let func = self.visit_atom(func);
                let args: Vec<Atom> = args.into_iter().map(|arg| self.visit_atom(arg)).collect();
                let cont = Box::new(self.visit_expr(*cont));
                self.mark_used(&func);
                args.iter().for_each(|arg| self.mark_used(arg));
                anf::Expr::Call {
                    bind,
                    func,
                    args,
                    cont,
                }
            }
            anf::Expr::Retn { res } => {
                let res = self.visit_atom(res);
                self.mark_used(&res);
                anf::Expr::Retn { res }
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
fn f() begin
    let x = @iadd(1, 2);
    let r = @record(x, x);
    let x1 = @select(r, 0);
    let x2 = @select(r, 1);
    let y = @iadd(x1, x2);
    let z = @iadd(x1, y);
    return z;
end
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
fn f() begin
    let x = @iadd(a, b);
    let y = @iadd(x, c);
    let z = @iadd(x, y);
    return y;
end
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
fn f() begin
    decl
        fn f(x) begin
        return x; 
        end
        fn g(x) begin
            let y = g(x);
            return y; 
        end
    in
        let y = f(x);
        return y;
    end
end
"#;
    let expr = super::parser::parse_module(s).unwrap();
    println!("{}\n", expr);
    let expr = Optimizer::run(expr);
    println!("{}\n", expr);
}
