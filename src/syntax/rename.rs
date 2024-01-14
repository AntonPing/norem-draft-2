use super::ast::{Expr, Stmt};
use crate::utils::ident::Ident;
use std::collections::HashMap;
use std::ops::DerefMut;

struct Renamer {
    context: HashMap<Ident, Ident>,
}

type RenameResult = Result<(), String>;

impl Renamer {
    pub fn new() -> Renamer {
        Renamer {
            context: HashMap::new(),
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
                let mut old: Vec<(Ident, Ident)> = Vec::new();
                for par in pars.iter_mut() {
                    let new = par.uniquify();
                    if let Some(val) = self.context.insert(*par, new) {
                        old.push((*par, val));
                    }
                    *par = new;
                }
                self.rename_expr(body)?;
                for (k, v) in old.into_iter() {
                    self.context.insert(k, v);
                }
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
            Expr::Stmt { stmt, cont } => match stmt.deref_mut() {
                Stmt::Let {
                    ident,
                    typ: _,
                    expr,
                } => {
                    self.rename_expr(expr)?;
                    let new = ident.uniquify();
                    let old = self.context.insert(*ident, new);
                    self.rename_expr(cont)?;
                    if let Some(old) = old {
                        self.context.insert(*ident, old);
                    }

                    Ok(())
                }
                Stmt::Do { expr } => {
                    self.rename_expr(expr)?;
                    self.rename_expr(cont)?;
                    Ok(())
                }
            },
        }
    }
}

pub fn rename_expr(expr: &mut Expr) -> RenameResult {
    let mut pass = Renamer::new();
    pass.rename_expr(expr)
}

#[test]
#[ignore = "just to see result"]
fn renamer_test() {
    use super::parser::parse_expr;
    let s = r#"
fn(x) => @iadd((fn(x) => @iadd(x,1))(42), x)
"#;

    let mut res = parse_expr(s).unwrap();
    rename_expr(&mut res).unwrap();
    println!("{:#?}", res);
}
