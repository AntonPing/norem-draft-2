use super::anf::*;
use crate::utils::ident::Ident;
use std::collections::HashMap;

pub struct Renamer {
    subst: HashMap<Ident, Ident>,
}

impl Renamer {
    pub fn run(expr: &mut Expr) {
        let mut pass = Renamer {
            subst: HashMap::new(),
        };
        pass.visit_expr(expr);
    }

    fn enter_scope(&mut self, bind: &mut Ident) -> Option<(Ident, Ident)> {
        let new_bind = bind.uniquify();
        let old = self.subst.insert(*bind, new_bind).map(|v| (*bind, v));
        *bind = new_bind;
        old
    }

    fn leave_scope(&mut self, old: Option<(Ident, Ident)>) {
        if let Some((k, v)) = old {
            self.subst.insert(k, v);
        }
    }

    fn visit_atom(&mut self, atom: &mut Atom) {
        if let Atom::Var(x) = atom {
            if let Some(y) = self.subst.get(&x) {
                *atom = Atom::Var(*y);
            }
        }
    }

    fn visit_decl(&mut self, decl: &mut Decl) {
        let Decl {
            func: _,
            pars,
            body,
        } = decl;
        let olds: Vec<Option<(Ident, Ident)>> =
            pars.iter_mut().map(|par| self.enter_scope(par)).collect();
        self.visit_expr(body);
        olds.into_iter().for_each(|old| self.leave_scope(old))
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Decls { decls, cont } => {
                let olds: Vec<Option<(Ident, Ident)>> = decls
                    .iter_mut()
                    .map(|decl| self.enter_scope(&mut decl.func))
                    .collect();
                decls.iter_mut().for_each(|decl| self.visit_decl(decl));
                self.visit_expr(cont);
                olds.into_iter().for_each(|old| self.leave_scope(old))
            }
            Expr::Prim {
                bind,
                prim: _,
                args,
                cont,
            } => {
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
                let old = self.enter_scope(bind);
                self.visit_expr(cont);
                self.leave_scope(old)
            }
            Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                self.visit_atom(func);
                args.iter_mut().for_each(|arg| self.visit_atom(arg));
                let old = self.enter_scope(bind);
                self.visit_expr(cont);
                self.leave_scope(old)
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
"#;
    let mut expr = super::parser::parse_expr(s).unwrap();
    println!("{}\n", expr);
    Renamer::run(&mut expr);
    println!("{}\n", expr);
}
