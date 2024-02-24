use super::ast::{Decl, Expr, Module, Stmt, Type};
use crate::utils::env_map::EnvMap;
use crate::utils::ident::Ident;
use std::ops::DerefMut;

struct Renamer {
    val_ctx: EnvMap<Ident, Ident>,
    typ_ctx: EnvMap<Ident, Ident>,
}

type RenameResult = Result<(), String>;

impl Renamer {
    pub fn new() -> Renamer {
        Renamer {
            val_ctx: EnvMap::new(),
            typ_ctx: EnvMap::new(),
        }
    }

    fn intro_val_ident(&mut self, ident: &mut Ident) {
        assert!(ident.is_dummy());
        let new = ident.uniquify();
        self.val_ctx.insert(*ident, new);
        *ident = new;
    }

    fn intro_typ_ident(&mut self, ident: &mut Ident) {
        assert!(ident.is_dummy());
        let new = ident.uniquify();
        self.typ_ctx.insert(*ident, new);
        *ident = new;
    }

    fn rename_val_ident(&mut self, ident: &mut Ident) -> RenameResult {
        assert!(ident.is_dummy());
        if let Some(res) = self.val_ctx.get(&ident) {
            *ident = *res;
            Ok(())
        } else {
            Err("Value variable not in scope!".to_string())
        }
    }

    fn rename_typ_ident(&mut self, ident: &mut Ident) -> RenameResult {
        assert!(ident.is_dummy());
        if let Some(res) = self.typ_ctx.get(&ident) {
            *ident = *res;
            Ok(())
        } else {
            Err("Type variable not in scope!".to_string())
        }
    }

    fn rename_expr(&mut self, expr: &mut Expr) -> RenameResult {
        match expr {
            Expr::Lit { lit: _, span: _ } => Ok(()),
            Expr::Var { ident, span: _ } => self.rename_val_ident(ident),
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
            Expr::Cons {
                cons,
                flds,
                span: _,
            } => {
                todo!()
            }
            Expr::Func {
                pars,
                body,
                span: _,
            } => {
                self.val_ctx.enter_scope();
                for par in pars.iter_mut() {
                    self.intro_val_ident(par);
                }
                self.rename_expr(body)?;
                self.val_ctx.leave_scope();
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
            Expr::Ifte {
                cond,
                trbr,
                flbr,
                span: _,
            } => {
                self.rename_expr(cond)?;
                self.rename_expr(trbr)?;
                self.rename_expr(flbr)?;
                Ok(())
            }
            Expr::Case {
                expr,
                rules,
                span: _,
            } => {
                todo!()
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
                    self.val_ctx.enter_scope();
                    let new = ident.uniquify();
                    self.val_ctx.insert(*ident, new);
                    *ident = new;
                    self.rename_expr(cont)?;
                    self.val_ctx.leave_scope();
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

    fn rename_type(&mut self, typ: &mut Type) -> RenameResult {
        match typ {
            Type::Lit { lit: _ } => Ok(()),
            Type::Var { ident } => self.rename_typ_ident(ident),
            Type::Cons { cons, args } => {
                self.rename_typ_ident(cons)?;
                for arg in args.iter_mut() {
                    self.rename_type(arg)?;
                }
                Ok(())
            }
            Type::Func { pars, res } => {
                for par in pars.iter_mut() {
                    self.rename_type(par)?;
                }
                self.rename_type(res)?;
                Ok(())
            }
        }
    }
    fn rename_decl(&mut self, decl: &mut Decl) -> RenameResult {
        match decl {
            Decl::Func {
                ident: _,
                polys,
                pars,
                res,
                span1: _,
                body,
                span2: _,
            } => {
                self.val_ctx.enter_scope();
                self.typ_ctx.enter_scope();
                for poly in polys {
                    self.intro_typ_ident(poly);
                }
                for (par, typ) in pars.iter_mut() {
                    self.intro_val_ident(par);
                    self.rename_type(typ)?;
                }
                self.rename_type(res)?;
                self.rename_expr(body)?;
                self.val_ctx.leave_scope();
                self.typ_ctx.leave_scope();
                Ok(())
            }
            Decl::Data {
                ident,
                polys,
                vars,
                span: _,
            } => {
                todo!()
            }
        }
    }

    fn rename_module(&mut self, modl: &mut Module) -> RenameResult {
        let Module { name: _, decls } = modl;
        self.val_ctx.enter_scope();
        for decl in decls.iter_mut() {
            match decl {
                Decl::Func { ident, .. } => self.intro_val_ident(ident),
                Decl::Data {
                    ident,
                    polys,
                    vars,
                    span: _,
                } => {
                    todo!()
                }
            }
        }
        for decl in decls.iter_mut() {
            self.rename_decl(decl)?;
        }
        self.val_ctx.leave_scope();
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
module Test where
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
function id[T](x: T) -> T
begin
    x
end
"#;
    let mut modl = parse_module(s).unwrap();
    rename_module(&mut modl).unwrap();
    println!("{:#?}", modl);
}
