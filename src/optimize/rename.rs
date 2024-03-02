use super::cps::*;
use crate::utils::env_map::EnvMap;
use crate::utils::ident::Ident;

pub struct Renamer {
    context: EnvMap<Ident, Ident>,
}

impl Renamer {
    pub fn run(modl: &mut Module) {
        let mut pass = Renamer {
            context: EnvMap::new(),
        };
        pass.visit_module(modl);
    }

    fn visit_atom(&mut self, atom: &mut Atom) {
        if let Atom::Var(x) = atom {
            if let Some(y) = self.context.get(&x) {
                *atom = Atom::Var(*y);
            }
        }
    }

    fn visit_module(&mut self, modl: &mut Module) {
        let Module { name: _, decls } = modl;
        self.context.enter_scope();
        for decl in decls.iter_mut() {
            let new = decl.func.uniquify();
            self.context.insert(decl.func, new);
            decl.func = new;
        }
        for decl in decls {
            self.visit_func_decl(decl);
        }
        self.context.leave_scope()
    }

    fn visit_func_decl(&mut self, decl: &mut FuncDecl) {
        let FuncDecl {
            func: _,
            cont,
            pars,
            body,
        } = decl;
        self.context.enter_scope();
        let new = cont.uniquify();
        self.context.insert(*cont, new);
        *cont = new;
        for par in pars {
            let new = par.uniquify();
            self.context.insert(*par, new);
            *par = new;
        }
        self.visit_expr(body);
        self.context.leave_scope();
    }

    fn visit_cont_decl(&mut self, decl: &mut ContDecl) {
        let ContDecl {
            cont: _,
            pars,
            body,
        } = decl;
        self.context.enter_scope();
        for par in pars {
            let new = par.uniquify();
            self.context.insert(*par, new);
            *par = new;
        }
        self.visit_expr(body);
        self.context.leave_scope();
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Decls { funcs, conts, body } => {
                self.context.enter_scope();
                for decl in funcs.iter_mut() {
                    let new = decl.func.uniquify();
                    self.context.insert(decl.func, new);
                    decl.func = new;
                }
                for decl in conts.iter_mut() {
                    let new = decl.cont.uniquify();
                    self.context.insert(decl.cont, new);
                    decl.cont = new;
                }
                for decl in funcs {
                    self.visit_func_decl(decl);
                }
                for decl in conts {
                    self.visit_cont_decl(decl);
                }
                self.visit_expr(body);
                self.context.leave_scope()
            }
            Expr::Prim {
                bind,
                prim: _,
                args,
                rest,
            } => {
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
                self.context.enter_scope();
                let new = bind.uniquify();
                self.context.insert(*bind, new);
                *bind = new;
                self.visit_expr(rest);
                self.context.leave_scope()
            }
            Expr::Call { func, cont, args } => {
                let new = *self.context.get(func).unwrap();
                *func = new;
                let new = *self.context.get(cont).unwrap();
                *cont = new;
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
            }
            Expr::Jump { cont, args } => {
                let new = *self.context.get(cont).unwrap();
                *cont = new;
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
            }
            Expr::Ifte {
                cond: _,
                args,
                trbr,
                flbr,
            } => {
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
                self.visit_expr(trbr);
                self.visit_expr(flbr);
            }
            Expr::Switch { arg, brchs, dflt } => {
                self.visit_atom(arg);
                for (_, brch) in brchs.iter_mut() {
                    self.visit_expr(brch);
                }
                if let Some(dflt) = dflt {
                    self.visit_expr(dflt)
                }
            }
            Expr::Retn { res } => {
                self.visit_atom(res);
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn rename_test() {
    let s = r#"
module Test where
func top1(x, y):
    return x;
func top2(x):
    decls
        func f(k, x, y, z):
            jump k(x);
        cont k(a):
            return a;
    in
        let x = @iadd(1, 2);
        call f(k, 1, 2, 3);
    end
"#;
    let mut modl = super::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    Renamer::run(&mut modl);
    println!("{}\n", modl);
}
