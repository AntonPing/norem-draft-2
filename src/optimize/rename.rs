use super::anf::*;
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
            self.visit_decl(decl);
        }
        self.context.leave_scope()
    }

    fn visit_decl(&mut self, decl: &mut Decl) {
        let Decl {
            func: _,
            pars,
            body,
            info: _,
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
            Expr::Decls { decls, cont } => {
                self.context.enter_scope();
                for decl in decls.iter_mut() {
                    let new = decl.func.uniquify();
                    self.context.insert(decl.func, new);
                    decl.func = new;
                }
                for decl in decls {
                    self.visit_decl(decl);
                }
                self.visit_expr(cont);
                self.context.leave_scope()
            }
            Expr::Prim {
                bind,
                prim: _,
                args,
                cont,
            } => {
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
                self.context.enter_scope();
                let new = bind.uniquify();
                self.context.insert(*bind, new);
                *bind = new;
                self.visit_expr(cont);
                self.context.leave_scope()
            }
            Expr::Brch {
                prim: _,
                args,
                conts,
            } => {
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
                for cont in conts.iter_mut() {
                    self.visit_expr(cont)
                }
            }
            Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                self.visit_atom(func);
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
                self.context.enter_scope();
                let new = bind.uniquify();
                self.context.insert(*bind, new);
                *bind = new;
                self.visit_expr(cont);
                self.context.leave_scope()
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
fn f(x) begin
    let x = @move(1);
    decl
        fn f(x) begin
        return x; 
        end
    in
        let y = f(42);
        let z = @iadd(x, y);
        return z;
    end
end
"#;
    let mut modl = super::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    Renamer::run(&mut modl);
    println!("{}\n", modl);
}
