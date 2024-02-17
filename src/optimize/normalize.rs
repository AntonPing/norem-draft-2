use std::iter;
use std::ops::Deref;

use super::anf::{self, Atom, PrimOpr};
use crate::syntax::ast::{self, Module};
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
    pub fn run(modl: &ast::Module) -> anf::Module {
        let mut pass = Normalizer {};
        pass.normalize_module(modl)
    }

    pub fn normalize_expr(expr: &ast::Expr) -> anf::Expr {
        let mut pass = Normalizer {};
        let bind = Ident::fresh(&"r");
        pass.normalize_expr_with_cont(
            expr,
            &bind,
            anf::Expr::Retn {
                res: Atom::Var(bind),
            },
        )
    }

    // translate from ast::Expr to anf::Expr, basically ssa translation
    // order of evaluation for function arguments: from right to left
    fn normalize_expr_with_cont(
        &mut self,
        expr: &ast::Expr,
        bind: &Ident,
        rest: anf::Expr,
    ) -> anf::Expr {
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
                    |rest, (bind, arg)| self.normalize_expr_with_cont(arg, bind, rest),
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
                        body: Normalizer::normalize_expr(body),
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
                        |rest, (bind, arg)| self.normalize_expr_with_cont(arg, bind, rest),
                    )
            }
            ast::Expr::Ifte {
                cond, trbr, flbr, ..
            } => {
                // normalize(if e1 then e2 else e3, hole, ctx) =
                // letjoin j(hole) = ctx in
                //      normalize(e1, x1,
                //          ifte x1 {
                //              normalize(e2, x2, j(x2))
                //              normalize(e3, x3, j(x3))
                //          } )
                let j = Ident::fresh(&"j");
                let x1 = Ident::fresh(&"x");
                let x2 = Ident::fresh(&"x");
                let x3 = Ident::fresh(&"x");
                let r2 = Ident::fresh(&"r");
                let r3 = Ident::fresh(&"r");
                let ifte = anf::Expr::Brch {
                    prim: anf::BrchOpr::Ifte,
                    args: vec![Atom::Var(x1)],
                    conts: vec![
                        self.normalize_expr_with_cont(
                            trbr,
                            &x2,
                            anf::Expr::Call {
                                bind: r2,
                                func: Atom::Var(j),
                                args: vec![Atom::Var(x2)],
                                cont: Box::new(anf::Expr::Retn { res: Atom::Var(r2) }),
                            },
                        ),
                        self.normalize_expr_with_cont(
                            flbr,
                            &x3,
                            anf::Expr::Call {
                                bind: r3,
                                func: Atom::Var(j),
                                args: vec![Atom::Var(x3)],
                                cont: Box::new(anf::Expr::Retn { res: Atom::Var(r3) }),
                            },
                        ),
                    ],
                };
                anf::Expr::Decls {
                    decls: vec![anf::Decl {
                        func: j,
                        pars: vec![*bind],
                        body: rest,
                    }],
                    cont: Box::new(self.normalize_expr_with_cont(cond, &x1, ifte)),
                }
            }
            ast::Expr::Stmt { stmt, cont, .. } => {
                // normalize(let x = e1; e2, hole, ctx) =
                // normalize(e1, x, normalize(e2, hole, ctx)
                let cont = self.normalize_expr_with_cont(cont, bind, rest);
                match stmt.deref() {
                    ast::Stmt::Let {
                        ident,
                        typ: _,
                        expr,
                        span: _,
                    } => self.normalize_expr_with_cont(expr, ident, cont),
                    ast::Stmt::Do { expr, span: _ } => {
                        let ident = Ident::fresh(&"_");
                        self.normalize_expr_with_cont(expr, &ident, cont)
                    }
                }
            }
        }
    }
    pub fn normalize_decl(&mut self, decl: &ast::Decl) -> anf::Decl {
        match decl {
            ast::Decl::Func {
                func, pars, body, ..
            } => {
                let (pars, _): (_, Vec<ast::Type>) = pars.iter().cloned().unzip();
                let bind = Ident::fresh(&"r");
                let body = self.normalize_expr_with_cont(
                    body,
                    &bind,
                    anf::Expr::Retn {
                        res: Atom::Var(bind),
                    },
                );
                anf::Decl {
                    func: *func,
                    pars,
                    body,
                }
            }
        }
    }
    pub fn normalize_module(&mut self, modl: &ast::Module) -> anf::Module {
        let Module { name, decls } = modl;

        let decls = decls.iter().map(|decl| self.normalize_decl(decl)).collect();

        anf::Module { name: *name, decls }
    }
}

#[test]
#[ignore = "just to see result"]
fn normalize_test() {
    let s = r#"
module test where
function f(x: Int) -> Int
begin
    let f = fn(x) => @iadd(x,1);
    let res = f(42);
    res
end
function g(x: Int) -> Int
begin
    let r = @iadd(x, 1);
    r
end
"#;
    let mut modl = crate::syntax::parser::parse_module(s).unwrap();
    crate::syntax::rename::rename_module(&mut modl).unwrap();
    let res = Normalizer::run(&modl);
    println!("{}", res);
}
