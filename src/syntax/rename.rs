use super::ast::{Decl, Expr, Module, Stmt};
use crate::utils::env_map::EnvMap;
use crate::utils::ident::Ident;
use std::ops::DerefMut;

struct Renamer {
    context: EnvMap<Ident, Ident>,
}

type RenameResult = Result<(), String>;

impl Renamer {
    pub fn new() -> Renamer {
        Renamer {
            context: EnvMap::new(),
        }
    }

    fn rename_expr(&mut self, expr: &mut Expr) -> RenameResult {
        match expr {
            Expr::Lit { lit: _, span: _ } => Ok(()),
            Expr::Var { ident, span: _ } => {
                assert!(ident.is_dummy());
                if let Some(res) = self.context.get(&ident) {
                    *ident = *res;
                    Ok(())
                } else {
                    Err("Variable not in scope!".to_string())
                }
            }
            Expr::Prim {
                prim: _,
                args,
                span: _,
            } => {
                for arg in args.iter_mut() {
                    self.rename_expr(arg)?
                }
                Ok(())
            }
            Expr::Func {
                pars,
                body,
                span: _,
            } => {
                self.context.enter_scope();
                for par in pars.iter_mut() {
                    let new = par.uniquify();
                    self.context.insert(*par, new);
                    *par = new;
                }
                self.rename_expr(body)?;
                self.context.leave_scope();
                Ok(())
            }
            Expr::App {
                func,
                args,
                span: _,
            } => {
                self.rename_expr(func)?;
                for arg in args.iter_mut() {
                    self.rename_expr(arg)?;
                }
                Ok(())
            }
            Expr::Stmt {
                stmt,
                cont,
                span: _,
            } => match stmt.deref_mut() {
                Stmt::Let {
                    ident,
                    typ: _,
                    expr,
                    span: _,
                } => {
                    self.rename_expr(expr)?;
                    self.context.enter_scope();
                    let new = ident.uniquify();
                    self.context.insert(*ident, new);
                    *ident = new;
                    self.rename_expr(cont)?;
                    self.context.leave_scope();
                    Ok(())
                }
                Stmt::Do { expr, span: _ } => {
                    self.rename_expr(expr)?;
                    self.rename_expr(cont)?;
                    Ok(())
                }
            },
        }
    }
    fn rename_decl(&mut self, decl: &mut Decl) -> RenameResult {
        match decl {
            Decl::Func {
                func: _,
                pars,
                res: _,
                span1: _,
                body,
                span2: _,
            } => {
                self.context.enter_scope();
                for (par, _) in pars.iter_mut() {
                    let new = par.uniquify();
                    self.context.insert(*par, new);
                    *par = new;
                }
                self.rename_expr(body)?;
                self.context.leave_scope();
                Ok(())
            }
        }
    }

    fn rename_module(&mut self, modl: &mut Module) -> RenameResult {
        let Module { name: _, decls } = modl;
        self.context.enter_scope();
        for decl in decls.iter_mut() {
            match decl {
                Decl::Func { func, .. } => {
                    let new = func.uniquify();
                    self.context.insert(*func, new);
                    *func = new;
                }
            }
        }
        for decl in decls.iter_mut() {
            self.rename_decl(decl)?;
        }
        self.context.leave_scope();
        Ok(())
    }
}

pub fn rename_expr(expr: &mut Expr) -> RenameResult {
    let mut pass = Renamer::new();
    pass.rename_expr(expr)
}

pub fn rename_module(expr: &mut Module) -> RenameResult {
    let mut pass = Renamer::new();
    pass.rename_module(expr)
}

#[test]
#[ignore = "just to see result"]
fn renamer_test() {
    use crate::syntax::parser::parse_module;
    let s = r#"
module test
begin
    function f(x: Int) -> Int
    begin
        let h = fn(x) => @iadd(x, 1);
        let r = g(x);
        r
    end
    function g(x: Int) -> Int
    begin
        let r = @iadd(x, 1);
        r
    end
end
"#;

    let mut modl = parse_module(s).unwrap();
    rename_module(&mut modl).unwrap();
    println!("{:#?}", modl);
}
