use std::collections::HashMap;
use std::iter;
use std::ops::Deref;

use super::anf::{self, Atom, PrimOpr};
use super::pattern::PatnMatrix;

use crate::optimize::pattern;
use crate::syntax::ast::{self, Pattern, Varient};
use crate::utils::ident::Ident;
use crate::utils::intern::InternStr;

pub struct Normalizer {
    cons_map: HashMap<Ident, Ident>,
    data_map: HashMap<Ident, Vec<Varient>>,
}

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
        let mut pass = Normalizer {
            cons_map: HashMap::new(),
            data_map: HashMap::new(),
        };
        let mut modl = pass.normalize_module(modl);
        super::rename::Renamer::run(&mut modl);
        modl
    }

    pub fn normalize_module(&mut self, modl: &ast::Module) -> anf::Module {
        let ast::Module { name, decls } = modl;
        for decl in decls.iter() {
            match decl {
                ast::Decl::Func { .. } => {}
                ast::Decl::Data {
                    ident,
                    polys: _,
                    vars,
                    span: _,
                } => {
                    self.data_map.insert(*ident, vars.clone());
                    for var in vars {
                        self.cons_map.insert(var.cons, *ident);
                    }
                }
            }
        }
        let decls = decls
            .iter()
            .flat_map(|decl| self.normalize_decl(decl))
            .collect();

        anf::Module { name: *name, decls }
    }

    pub fn normalize_expr(expr: &ast::Expr) -> anf::Expr {
        let mut pass = Normalizer {
            cons_map: HashMap::new(),
            data_map: HashMap::new(),
        };
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
            ast::Expr::Lit { lit, span: _ } => subst(rest, *bind, (*lit).into()),
            ast::Expr::Var { ident, span: _ } => subst(rest, *bind, Atom::Var(*ident)),
            ast::Expr::Prim {
                prim,
                args,
                span: _,
            } => {
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
            ast::Expr::Func {
                pars,
                body,
                span: _,
            } => {
                // normalize(fun(x,y) => e, hole, ctx) =
                // let f(x,y) = normalize_top(e) in ctx[hole:=f]
                let func_bind = Ident::fresh(&"f");
                anf::Expr::Decls {
                    decls: vec![anf::Decl {
                        func: func_bind,
                        pars: pars.clone(),
                        body: Normalizer::normalize_expr(body),
                        info: anf::CallInfo::NoInfo,
                    }],
                    cont: Box::new(subst(rest, *bind, Atom::Var(func_bind))),
                }
            }
            ast::Expr::Cons {
                cons,
                flds,
                span: _,
            } => {
                // normalize(ci(e1,..,en), hole, ctx) =
                // normalize(en,xn,
                //   ...
                //     normalize(e1,x1,
                //       normalize(e0,f,
                //         let r = @record(x0, ..., xn);
                //         let hole = move(r);
                //         ctx))...)

                let typ = self.cons_map[cons];
                let (tag, label_vec): (usize, Vec<InternStr>) = self.data_map[&typ]
                    .iter()
                    .enumerate()
                    .find(|(_, var)| var.cons == *cons)
                    .map(|(i, var)| (i, var.flds.iter().map(|fld| fld.label).collect()))
                    .unwrap();

                let xs: Vec<Ident> = label_vec.iter().map(|_| Ident::fresh(&"x")).collect();
                let r = Ident::fresh(&"r");
                let cont = anf::Expr::Prim {
                    bind: r,
                    prim: anf::PrimOpr::Record,
                    args: [Atom::Int(tag as i64)]
                        .into_iter()
                        .chain(xs.iter().map(|x| Atom::Var(*x)))
                        .collect(),
                    cont: Box::new(anf::Expr::Prim {
                        bind: *bind,
                        prim: anf::PrimOpr::Move,
                        args: vec![Atom::Var(r)],
                        cont: Box::new(rest),
                    }),
                };

                label_vec
                    .iter()
                    .zip(xs.iter())
                    .map(|(label, bind)| {
                        let fld = flds.iter().find(|fld| fld.label == *label).unwrap();
                        (bind, &fld.data)
                    })
                    .fold(cont, |cont, (bind, expr)| {
                        self.normalize_expr_with_cont(&expr, bind, cont)
                    })
            }
            ast::Expr::App {
                func,
                args,
                span: _,
            } => {
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
                cond,
                trbr,
                flbr,
                span: _,
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
                let trbr = self.normalize_expr_with_cont(
                    trbr,
                    &x2,
                    anf::Expr::Call {
                        bind: r2,
                        func: Atom::Var(j),
                        args: vec![Atom::Var(x2)],
                        cont: Box::new(anf::Expr::Retn { res: Atom::Var(r2) }),
                    },
                );
                let flbr = self.normalize_expr_with_cont(
                    flbr,
                    &x3,
                    anf::Expr::Call {
                        bind: r3,
                        func: Atom::Var(j),
                        args: vec![Atom::Var(x3)],
                        cont: Box::new(anf::Expr::Retn { res: Atom::Var(r3) }),
                    },
                );
                let ifte = anf::Expr::Ifte {
                    cond: anf::IfCond::BTrue,
                    args: vec![Atom::Var(x1)],
                    trbr: Box::new(trbr),
                    flbr: Box::new(flbr),
                };
                anf::Expr::Decls {
                    decls: vec![anf::Decl {
                        func: j,
                        pars: vec![*bind],
                        body: rest,
                        info: anf::CallInfo::NoInfo,
                    }],
                    cont: Box::new(self.normalize_expr_with_cont(cond, &x1, ifte)),
                }
            }
            ast::Expr::Case {
                expr,
                rules,
                span: _,
            } => {
                /*
                    normalize(
                        match top of
                        | patn_0 => e_0
                        ......
                        | patn_n => e_n
                    hole,
                    rest
                    ) =
                    normalize(top, o
                        decls
                            fn a_0(..) begin normalize(e_0, r, j(r) end
                            ......
                            fn a_n(..) begin normalize(e_n, r, j(r) end
                            fn j(hole) begin rest end
                        in
                            inline(
                                compile_match_with(
                                    (o),
                                    (patn_1)
                                    ......
                                    (patn_n),
                                    (a_1, ..., a_n),
                                ),
                            )
                        end
                    )
                */

                let j = Ident::fresh(&"j");
                let r = Ident::fresh(&"r");

                let obj = Ident::fresh(&"o");
                let objs = vec![obj];

                let mut decls: Vec<anf::Decl> = Vec::new();
                let (matrix, acts): (Vec<Vec<Pattern>>, Vec<Ident>) = rules
                    .iter()
                    .map(|rule| {
                        let act = Ident::fresh(&"a");
                        let binds = pattern::get_bind_vars(&rule.patn);
                        let body = self.normalize_expr_with_cont(
                            &rule.body,
                            &r,
                            anf::Expr::Call {
                                bind: r,
                                func: Atom::Var(j),
                                args: vec![Atom::Var(r)],
                                cont: Box::new(anf::Expr::Retn { res: Atom::Var(r) }),
                            },
                        );
                        let decl = anf::Decl {
                            func: act,
                            pars: binds,
                            body,
                            info: anf::CallInfo::JoinPoint,
                        };
                        decls.push(decl);
                        (vec![rule.patn.clone()], act)
                    })
                    .unzip();

                let decl = anf::Decl {
                    func: j,
                    pars: vec![*bind],
                    body: rest,
                    info: anf::CallInfo::JoinPoint,
                };
                decls.push(decl);

                let mat = PatnMatrix { objs, matrix, acts };
                let cont = self.normalize_match(&mat, &decls);
                let rest = anf::Expr::Decls {
                    decls,
                    cont: Box::new(cont),
                };
                self.normalize_expr_with_cont(expr, &obj, rest)
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
    pub fn normalize_decl(&mut self, decl: &ast::Decl) -> Option<anf::Decl> {
        match decl {
            ast::Decl::Func {
                ident,
                polys: _,
                pars,
                res: _,
                span1: _,
                body,
                span2: _,
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
                Some(anf::Decl {
                    func: *ident,
                    pars,
                    body,
                    info: anf::CallInfo::NoInfo,
                })
            }
            ast::Decl::Data { .. } => None,
        }
    }

    fn normalize_match(&mut self, mat: &PatnMatrix, decls: &Vec<anf::Decl>) -> anf::Expr {
        if mat.is_empty() {
            panic!("pattern match not exhaustive!")
        } else if mat.first_row_aways_match() {
            let (bindings, act) = mat.success();
            let r = Ident::fresh(&"r");
            bindings.into_iter().fold(
                anf::Expr::Call {
                    bind: r,
                    func: Atom::Var(act),
                    args: decls
                        .iter()
                        .find(|decl| decl.func == act)
                        .unwrap()
                        .pars
                        .iter()
                        .map(|par| Atom::Var(*par))
                        .collect(),
                    cont: Box::new(anf::Expr::Retn { res: Atom::Var(r) }),
                },
                |cont, (var, obj)| anf::Expr::Prim {
                    bind: var,
                    prim: PrimOpr::Move,
                    args: vec![Atom::Var(obj)],
                    cont: Box::new(cont),
                },
            )
        } else {
            let j = 0;
            match mat.get_col_type(j) {
                pattern::ColType::Lit => {
                    todo!()
                }
                pattern::ColType::Cons => {
                    let cons_set = mat.get_cons_set(j);
                    let typ = self.cons_map[&cons_set[0]];
                    let vars = self.data_map[&typ].clone();
                    for cons in cons_set {
                        assert!(vars.iter().any(|var| var.cons == cons));
                    }
                    let mut brchs: Vec<(usize, anf::Expr)> = Vec::new();
                    for (i, var) in vars.iter().enumerate() {
                        let binds = var
                            .flds
                            .iter()
                            .map(|fld| (fld.label, Ident::fresh(&"o")))
                            .collect();
                        let (new_mat, hits) = mat.specialize_cons(j, &var.cons, &binds);

                        let brch = binds.iter().enumerate().fold(
                            self.normalize_match(&new_mat, decls),
                            |cont, (i, (_label, obj))| anf::Expr::Prim {
                                bind: *obj,
                                prim: PrimOpr::Select,
                                args: vec![Atom::Var(mat.objs[j]), Atom::Int((i + 1) as i64)],
                                cont: Box::new(cont),
                            },
                        );

                        let brch = hits.iter().fold(brch, |cont, hit| anf::Expr::Prim {
                            bind: *hit,
                            prim: PrimOpr::Move,
                            args: vec![Atom::Var(mat.objs[j])],
                            cont: Box::new(cont),
                        });
                        brchs.push((i, brch));
                    }

                    let t = Ident::fresh(&"t");
                    anf::Expr::Prim {
                        bind: t,
                        prim: PrimOpr::Select,
                        args: vec![Atom::Var(mat.objs[j]), Atom::Int(0)],
                        cont: Box::new(anf::Expr::Switch {
                            arg: Atom::Var(t),
                            brchs,
                            dflt: None,
                        }),
                    }
                }
                pattern::ColType::Unknown => {
                    let (new_mat, hits) = mat.default(j);
                    let brch =
                        hits.iter()
                            .fold(self.normalize_match(&new_mat, decls), |cont, hit| {
                                anf::Expr::Prim {
                                    bind: *hit,
                                    prim: PrimOpr::Move,
                                    args: vec![Atom::Var(mat.objs[j])],
                                    cont: Box::new(cont),
                                }
                            });

                    brch
                }
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn normalize_test() {
    let s = r#"
module Test where
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
