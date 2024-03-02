use std::collections::HashMap;
use std::iter;
use std::ops::Deref;

use super::cps::{self, Atom, ContDecl, PrimOpr};
use super::pattern::PatnMatrix;

use crate::optimize::pattern;
use crate::syntax::ast::{self, Pattern, Varient};
use crate::utils::ident::Ident;
use crate::utils::intern::InternStr;

pub struct Normalizer {
    cons_map: HashMap<Ident, Ident>,
    data_map: HashMap<Ident, Vec<Varient>>,
}

impl Normalizer {
    pub fn run(modl: &ast::Module) -> cps::Module {
        let mut pass = Normalizer {
            cons_map: HashMap::new(),
            data_map: HashMap::new(),
        };
        let mut modl = pass.normalize_module(modl);
        super::rename::Renamer::run(&mut modl);
        modl
    }

    pub fn normalize_module(&mut self, modl: &ast::Module) -> cps::Module {
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
            .flat_map(|decl| self.normalize_func_decl(decl))
            .collect();

        cps::Module { name: *name, decls }
    }

    pub fn normalize_func_decl(&mut self, decl: &ast::Decl) -> Option<cps::FuncDecl> {
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
                let k = Ident::fresh(&"k");
                let r = Ident::fresh(&"r");

                Some(cps::FuncDecl {
                    func: *ident,
                    cont: k,
                    pars: pars.iter().map(|(par, _typ)| *par).collect(),
                    body: self.normalize_expr_with_cont(
                        body,
                        r,
                        cps::Expr::Jump {
                            cont: k,
                            args: vec![Atom::Var(r)],
                        },
                    ),
                })
            }
            ast::Decl::Data { .. } => None,
        }
    }

    pub fn normalize_expr(expr: &ast::Expr) -> cps::Expr {
        let mut pass = Normalizer {
            cons_map: HashMap::new(),
            data_map: HashMap::new(),
        };
        let bind = Ident::fresh(&"r");
        pass.normalize_expr_with_cont(
            expr,
            bind,
            cps::Expr::Retn {
                res: Atom::Var(bind),
            },
        )
    }

    // translate from ast::Expr to anf::Expr, basically ssa translation
    // order of evaluation for function arguments: from right to left
    fn normalize_expr_with_cont(
        &mut self,
        expr: &ast::Expr,
        bind: Ident,
        rest: cps::Expr,
    ) -> cps::Expr {
        match expr {
            ast::Expr::Lit { lit, span: _ } => {
                //  normalize(v, bind, rest) =
                //  let bind = @move(v);
                //  rest
                cps::Expr::Prim {
                    bind,
                    prim: PrimOpr::Move,
                    args: vec![(*lit).into()],
                    rest: Box::new(rest),
                }
            }
            ast::Expr::Var { ident, span: _ } => {
                //  normalize(x, bind, rest) =
                //  let bind = @move(x);
                //  rest
                cps::Expr::Prim {
                    bind,
                    prim: PrimOpr::Move,
                    args: vec![Atom::Var(*ident)],
                    rest: Box::new(rest),
                }
            }
            ast::Expr::Prim {
                prim,
                args,
                span: _,
            } => {
                //  normalize(@prim(e1, ..., en), bind, rest) =
                //  normalize(en, xn,
                //      ...
                //          normalize(e1, x1,
                //              let bind = @prim(x1, ..., xn);
                //              rest)...)
                let xs: Vec<Ident> = args.iter().map(|_| Ident::fresh(&"x")).collect();
                xs.iter().zip(args.iter()).rev().fold(
                    cps::Expr::Prim {
                        bind,
                        prim: (*prim).into(),
                        args: xs.iter().map(|x| cps::Atom::Var(*x)).collect(),
                        rest: Box::new(rest),
                    },
                    |rest, (bind, arg)| self.normalize_expr_with_cont(arg, *bind, rest),
                )
            }
            ast::Expr::Func {
                pars,
                body,
                span: _,
            } => {
                //  normalize(fun(x1, ..., xn) => body, bind, rest) =
                //  decls
                //      func f(k, x1, ..., xn):
                //          normalize(body, r, jump k(r))
                //  in
                //      let bind = @move(f);
                //      rest
                //  end
                let f = Ident::fresh(&"f");
                let k = Ident::fresh(&"k");
                let r = Ident::fresh(&"r");

                cps::Expr::Decls {
                    funcs: vec![cps::FuncDecl {
                        func: f,
                        cont: k,
                        pars: pars.clone(),
                        body: self.normalize_expr_with_cont(
                            body,
                            r,
                            cps::Expr::Jump {
                                cont: k,
                                args: vec![Atom::Var(r)],
                            },
                        ),
                    }],
                    conts: Vec::new(),
                    body: Box::new(cps::Expr::Prim {
                        bind,
                        prim: PrimOpr::Move,
                        args: vec![Atom::Var(f)],
                        rest: Box::new(rest),
                    }),
                }
            }
            ast::Expr::Cons {
                cons,
                flds,
                span: _,
            } => {
                //  normalize(ci(e1, ..., en), bind, rest) =
                //  normalize(en, xn,
                //      ...
                //          normalize(e1,x1,
                //              let r = @record(i, x1, ..., xn);
                //              let hole = move(r);
                //              rest)...)

                let typ = self.cons_map[cons];
                let (tag, label_vec): (usize, Vec<InternStr>) = self.data_map[&typ]
                    .iter()
                    .enumerate()
                    .find(|(_, var)| var.cons == *cons)
                    .map(|(i, var)| (i, var.flds.iter().map(|fld| fld.label).collect()))
                    .unwrap();

                let xs: Vec<Ident> = label_vec.iter().map(|_| Ident::fresh(&"x")).collect();
                let r = Ident::fresh(&"r");

                label_vec
                    .into_iter()
                    .zip(xs.iter())
                    .map(|(label, bind)| {
                        let fld = flds.iter().find(|fld| fld.label == label).unwrap();
                        (bind, &fld.data)
                    })
                    .fold(
                        cps::Expr::Prim {
                            bind: r,
                            prim: cps::PrimOpr::Record,
                            args: [Atom::Int(tag as i64)]
                                .into_iter()
                                .chain(xs.iter().map(|x| Atom::Var(*x)))
                                .collect(),
                            rest: Box::new(cps::Expr::Prim {
                                bind,
                                prim: cps::PrimOpr::Move,
                                args: vec![Atom::Var(r)],
                                rest: Box::new(rest),
                            }),
                        },
                        |rest, (bind, expr)| self.normalize_expr_with_cont(&expr, *bind, rest),
                    )
            }
            ast::Expr::App {
                func,
                args,
                span: _,
            } => {
                //  normalize(e0(e1, ..., en), bind, rest) =
                //  normalize(en, xn,
                //      ...
                //          normalize(e1, x1,
                //              normalize(e0, f,
                //                  decls
                //                      cont k(r):
                //                          let bind = @move(r);
                //                          rest
                //                  in
                //                      call f(k, x1, ..., xn);
                //                  end

                let f = Ident::fresh(&"f");
                let k = Ident::fresh(&"k");
                let r = Ident::fresh(&"r");
                let xs: Vec<Ident> = args.iter().map(|_| Ident::fresh(&"x")).collect();

                iter::once((&f, func.as_ref()))
                    .chain(xs.iter().zip(args.into_iter()))
                    .fold(
                        cps::Expr::Decls {
                            funcs: Vec::new(),
                            conts: vec![ContDecl {
                                cont: k,
                                pars: vec![r],
                                body: cps::Expr::Prim {
                                    bind,
                                    prim: PrimOpr::Move,
                                    args: vec![Atom::Var(r)],
                                    rest: Box::new(rest),
                                },
                            }],
                            body: Box::new(cps::Expr::Call {
                                func: f,
                                cont: k,
                                args: xs.iter().map(|x| Atom::Var(*x)).collect(),
                            }),
                        },
                        |rest, (bind, arg)| self.normalize_expr_with_cont(arg, *bind, rest),
                    )
            }
            ast::Expr::Ifte {
                cond,
                trbr,
                flbr,
                span: _,
            } => {
                //  normalize(if e1 then e2 else e3, bind, rest) =
                //  decls
                //      cont k(bind):
                //          rest
                //  in
                //      normalize(e1, x1,
                //          if x1
                //          then
                //              normalize(e2, x2, jump k(x2))
                //          else
                //              normalize(e3, x3, jump k(x3)))
                //  end

                let k = Ident::fresh(&"k");
                let x1 = Ident::fresh(&"x");
                let x2 = Ident::fresh(&"x");
                let x3 = Ident::fresh(&"x");

                let trbr = self.normalize_expr_with_cont(
                    trbr,
                    x2,
                    cps::Expr::Jump {
                        cont: k,
                        args: vec![Atom::Var(x2)],
                    },
                );
                let flbr = self.normalize_expr_with_cont(
                    flbr,
                    x3,
                    cps::Expr::Jump {
                        cont: k,
                        args: vec![Atom::Var(x3)],
                    },
                );
                cps::Expr::Decls {
                    funcs: Vec::new(),
                    conts: vec![cps::ContDecl {
                        cont: k,
                        pars: vec![bind],
                        body: rest,
                    }],
                    body: Box::new(self.normalize_expr_with_cont(
                        cond,
                        x1,
                        cps::Expr::Ifte {
                            cond: cps::IfCond::BTrue,
                            args: vec![Atom::Var(x1)],
                            trbr: Box::new(trbr),
                            flbr: Box::new(flbr),
                        },
                    )),
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
                        | patn_1 => e_1
                        ......
                        | patn_n => e_n
                        bind, rest) =

                    normalize(top, o
                        decls
                            cont a_1(..):
                                normalize(e_1, r1, jump k(r0))
                            ...
                            cont a_n(..):
                                normalize(e_n, rn, jump k(r1))
                            cont k(bind):
                                rest
                        in
                            compile_match_with(
                                (o),
                                (patn_1)
                                ......
                                (patn_n),
                                (a_1, ..., a_n),
                            ),
                        end
                    )
                */
                let k = Ident::fresh(&"k");
                let obj = Ident::fresh(&"o");
                let objs = vec![obj];
                let mut decls: Vec<cps::ContDecl> = Vec::new();
                let (matrix, acts): (Vec<Vec<Pattern>>, Vec<Ident>) = rules
                    .iter()
                    .map(|rule| {
                        let act = Ident::fresh(&"a");
                        let r = Ident::fresh(&"r");
                        let body = self.normalize_expr_with_cont(
                            &rule.body,
                            r,
                            cps::Expr::Jump {
                                cont: k,
                                args: vec![Atom::Var(r)],
                            },
                        );
                        let decl = cps::ContDecl {
                            cont: act,
                            pars: pattern::get_bind_vars(&rule.patn),
                            body,
                        };
                        decls.push(decl);
                        (vec![rule.patn.clone()], act)
                    })
                    .unzip();

                let decl = cps::ContDecl {
                    cont: k,
                    pars: vec![bind],
                    body: rest,
                };
                decls.push(decl);

                let mat = PatnMatrix { objs, matrix, acts };
                let body = self.normalize_match(&mat, &decls);
                let rest = cps::Expr::Decls {
                    funcs: Vec::new(),
                    conts: decls,
                    body: Box::new(body),
                };
                self.normalize_expr_with_cont(expr, obj, rest)
            }
            ast::Expr::Stmt { stmt, cont, .. } => {
                //  normalize(let x = e1; e2, bind, rest) =
                //  normalize(e1, x, normalize(e2, bind, rest))
                let cont = self.normalize_expr_with_cont(cont, bind, rest);
                match stmt.deref() {
                    ast::Stmt::Let {
                        ident,
                        typ: _,
                        expr,
                        span: _,
                    } => self.normalize_expr_with_cont(expr, *ident, cont),
                    ast::Stmt::Do { expr, span: _ } => {
                        let ident = Ident::fresh(&"_");
                        self.normalize_expr_with_cont(expr, ident, cont)
                    }
                }
            }
        }
    }

    fn normalize_match(&mut self, mat: &PatnMatrix, decls: &Vec<cps::ContDecl>) -> cps::Expr {
        if mat.is_empty() {
            panic!("pattern match not exhaustive!")
        } else if mat.first_row_aways_match() {
            let (bindings, act) = mat.success();
            bindings.into_iter().fold(
                cps::Expr::Jump {
                    cont: act,
                    args: decls
                        .iter()
                        .find(|decl| decl.cont == act)
                        .unwrap()
                        .pars
                        .iter()
                        .map(|par| Atom::Var(*par))
                        .collect(),
                },
                |rest, (var, obj)| cps::Expr::Prim {
                    bind: var,
                    prim: PrimOpr::Move,
                    args: vec![Atom::Var(obj)],
                    rest: Box::new(rest),
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
                    let mut brchs: Vec<(usize, cps::Expr)> = Vec::new();
                    for (i, var) in vars.iter().enumerate() {
                        let binds = var
                            .flds
                            .iter()
                            .map(|fld| (fld.label, Ident::fresh(&"o")))
                            .collect();
                        let (new_mat, hits) = mat.specialize_cons(j, &var.cons, &binds);

                        let brch = binds.iter().enumerate().fold(
                            self.normalize_match(&new_mat, decls),
                            |cont, (i, (_label, obj))| cps::Expr::Prim {
                                bind: *obj,
                                prim: PrimOpr::Select,
                                args: vec![Atom::Var(mat.objs[j]), Atom::Int((i + 1) as i64)],
                                rest: Box::new(cont),
                            },
                        );

                        let brch = hits.iter().fold(brch, |cont, hit| cps::Expr::Prim {
                            bind: *hit,
                            prim: PrimOpr::Move,
                            args: vec![Atom::Var(mat.objs[j])],
                            rest: Box::new(cont),
                        });
                        brchs.push((i, brch));
                    }

                    let t = Ident::fresh(&"t");
                    cps::Expr::Prim {
                        bind: t,
                        prim: PrimOpr::Select,
                        args: vec![Atom::Var(mat.objs[j]), Atom::Int(0)],
                        rest: Box::new(cps::Expr::Switch {
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
                                cps::Expr::Prim {
                                    bind: *hit,
                                    prim: PrimOpr::Move,
                                    args: vec![Atom::Var(mat.objs[j])],
                                    rest: Box::new(cont),
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
