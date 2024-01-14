use std::iter;
use std::ops::Deref;

use super::anf::{self, Atom, PrimOpr};
use crate::syntax::ast;
use crate::utils::ident::Ident;

pub struct Normalizer {}

fn subst(expr: anf::Expr, hole: Ident, atom: Atom) -> anf::Expr {
    // subst(expr,hole,atom) ~=~ let hole = move(atom); expr
    // it will be substituted in constant-fold pass anyway
    anf::Expr::Prim {
        bind: hole,
        prim: PrimOpr::Move,
        args: vec![atom],
        cont: Box::new(expr),
    }
}

impl Normalizer {
    pub fn run(expr: &ast::Expr) -> anf::Expr {
        let mut pass = Normalizer {};
        let bind = Ident::fresh(&"r");
        pass.normalize(
            expr,
            &bind,
            anf::Expr::Retn {
                res: Atom::Var(bind),
            },
        )
    }

    // translate from ast::Expr to anf::Expr, basically ssa translation
    // order of evaluation for function arguments: from right to left
    fn normalize(&mut self, expr: &ast::Expr, bind: &Ident, rest: anf::Expr) -> anf::Expr {
        match expr {
            ast::Expr::Lit { lit, .. } => subst(rest, *bind, (*lit).into()),
            ast::Expr::Var { ident, .. } => subst(rest, *bind, Atom::Var(*ident)),
            ast::Expr::Prim { prim, args, .. } => {
                // normalize(@iadd(e1, e2), hole, rest) =
                // normalize(e2, x2, normalize(e1, x1, let hole = iadd(x1,x2) in rest))
                let arg_binds: Vec<Ident> = args.iter().map(|_| Ident::fresh(&"x")).collect();
                arg_binds.iter().zip(args.iter()).rev().fold(
                    anf::Expr::Prim {
                        bind: *bind,
                        prim: (*prim).into(),
                        args: arg_binds.iter().map(|x| anf::Atom::Var(*x)).collect(),
                        cont: Box::new(rest),
                    },
                    |rest, (bind, arg)| self.normalize(arg, bind, rest),
                )
            }
            ast::Expr::Func { pars, body, .. } => {
                // normalize(fun(x,y) => e, hole, ctx) =
                // let f(x,y) = normalize_top(e) in ctx[hole:=f]
                let func_bind = Ident::fresh(&"f");
                anf::Expr::Decls {
                    decls: vec![anf::Decl {
                        func: func_bind,
                        pars: pars.clone(),
                        body: Normalizer::run(body),
                    }],
                    cont: Box::new(subst(rest, *bind, Atom::Var(func_bind))),
                }
            }
            ast::Expr::App { func, args, .. } => {
                // normalize(e0(e1,..,en), hole, ctx) =
                // normalize(en,xn,
                //   ...
                //     normalize(e1,x1,
                //       normalize(e0,f,
                //         let hole = f(x1,...,xn) in ctx))...)
                let func_bind = Ident::fresh(&"f");
                let arg_binds: Vec<Ident> = args.iter().map(|_| Ident::fresh(&"x")).collect();
                iter::once((&func_bind, func.deref()))
                    .chain(arg_binds.iter().zip(args.iter()))
                    .rev()
                    .fold(
                        anf::Expr::Call {
                            bind: *bind,
                            func: Atom::Var(func_bind),
                            args: arg_binds.iter().map(|x| anf::Atom::Var(*x)).collect(),
                            cont: Box::new(rest),
                        },
                        |rest, (bind, arg)| self.normalize(arg, bind, rest),
                    )
            }
            ast::Expr::Stmt { stmt, cont } => {
                // normalize(let x = e1; e2, hole, ctx) =
                // normalize(e1, x, normalize(e2, hole, ctx)
                let cont = self.normalize(cont, bind, rest);
                match stmt.deref() {
                    ast::Stmt::Let {
                        ident,
                        typ: _,
                        expr,
                    } => self.normalize(expr, ident, cont),
                    ast::Stmt::Do { expr } => {
                        let ident = Ident::fresh(&"_");
                        self.normalize(expr, &ident, cont)
                    }
                }
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn check_test() {
    use crate::syntax::parser::parse_expr;
    use crate::syntax::rename::rename_expr;
    let s = r#"
(fn(x) => @iadd(42, x))
"#;
    let mut res = parse_expr(s).unwrap();
    rename_expr(&mut res).unwrap();
    let res = Normalizer::run(&res);
    println!("{}", res);
}
