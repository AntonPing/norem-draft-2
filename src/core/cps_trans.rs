use std::collections::HashMap;
use std::iter;
use std::ops::Deref;

use itertools::Itertools;

use super::cps::{self, Atom, ContDecl, PrimOpr};
use super::pattern::PatnMatrix;

use crate::core::pattern;
use crate::syntax::ast::{self, FuncSign, Pattern, Varient};
use crate::utils::ident::Ident;

pub struct Translator {
    // cons_map: constructor -> (datatype, varient)
    cons_map: HashMap<Ident, (Ident, Varient)>,
    // data_map: datatype -> a list of constructors
    data_map: HashMap<Ident, Vec<Ident>>,
}

impl Translator {
    pub fn run(modl: &ast::Module) -> cps::Module {
        let mut pass = Translator {
            cons_map: HashMap::new(),
            data_map: HashMap::new(),
        };
        let mut modl = pass.translate_module(modl);
        super::rename::Renamer::run(&mut modl);
        modl
    }

    pub fn translate_module(&mut self, modl: &ast::Module) -> cps::Module {
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
                    let conss = vars.iter().map(|var| var.cons).collect();
                    self.data_map.insert(*ident, conss);
                    for var in vars {
                        self.cons_map.insert(var.cons, (*ident, var.clone()));
                    }
                }
            }
        }
        let decls = decls
            .iter()
            .flat_map(|decl| self.translate_func_decl(decl))
            .collect();

        cps::Module { name: *name, decls }
    }

    pub fn translate_func_decl(&mut self, decl: &ast::Decl) -> Option<cps::FuncDecl> {
        match decl {
            ast::Decl::Func {
                sign:
                    FuncSign {
                        func,
                        polys: _,
                        pars,
                        res: _,
                        span: _,
                    },
                body,
                span: _,
            } => {
                let k = Ident::fresh(&"k");
                let r = Ident::fresh(&"r");

                Some(cps::FuncDecl {
                    func: *func,
                    cont: k,
                    pars: pars.iter().map(|(par, _typ)| *par).collect(),
                    body: self.translate_expr(
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

    // translate from ast::Expr to cps::Expr, cps translation
    // order of evaluation for function arguments: from right to left
    fn translate_expr(&mut self, expr: &ast::Expr, bind: Ident, rest: cps::Expr) -> cps::Expr {
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
                    |rest, (bind, arg)| self.translate_expr(arg, *bind, rest),
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
                        body: self.translate_expr(
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
                //              record r = { i, x1, ..., xn };
                //              let hole = move(r);
                //              rest)...)
                let (data, var) = &self.cons_map[cons];
                // get varient tag index
                let tag = self.data_map[&data]
                    .iter()
                    .enumerate()
                    .find(|(_i, cons2)| *cons2 == cons)
                    .unwrap()
                    .0;

                let label_vec: Vec<_> = var.flds.iter().map(|fld| fld.label).collect();
                let is_mut_vec: Vec<_> = var.flds.iter().map(|fld| fld.data.0).collect();
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
                        cps::Expr::Record {
                            bind: r,
                            args: [(false, Atom::Int(tag as i64))]
                                .into_iter()
                                .chain(
                                    is_mut_vec
                                        .iter()
                                        .zip(xs.iter())
                                        .map(|(is_mut, x)| (*is_mut, Atom::Var(*x))),
                                )
                                .collect(),
                            rest: Box::new(cps::Expr::Prim {
                                bind,
                                prim: cps::PrimOpr::Move,
                                args: vec![Atom::Var(r)],
                                rest: Box::new(rest),
                            }),
                        },
                        |rest, (bind, expr)| self.translate_expr(&expr, *bind, rest),
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
                        |rest, (bind, arg)| self.translate_expr(arg, *bind, rest),
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

                let trbr = self.translate_expr(
                    trbr,
                    x2,
                    cps::Expr::Jump {
                        cont: k,
                        args: vec![Atom::Var(x2)],
                    },
                );
                let flbr = self.translate_expr(
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
                    body: Box::new(self.translate_expr(
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
                        let body = self.translate_expr(
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
                self.translate_expr(expr, obj, rest)
            }
            ast::Expr::Field {
                expr,
                field,
                cons_info,
                span: _,
            } => {
                //  normalize(e.a, bind, rest) =
                //  normalize(e, x,
                //      select bind = x[i+1];
                //      rest)
                //  (* where i is the index of field a, which is solved in type checker *)
                let i = self.cons_map[&cons_info.unwrap()]
                    .1
                    .flds
                    .iter()
                    .find_position(|fld2| fld2.label == *field)
                    .unwrap()
                    .0;
                let x = Ident::fresh(&"x");
                self.translate_expr(
                    expr,
                    x,
                    cps::Expr::Select {
                        bind,
                        rec: Atom::Var(x),
                        idx: i + 1,
                        rest: Box::new(rest),
                    },
                )
            }
            ast::Expr::NewRef { expr, span: _ } => {
                //  normalize(ref e, bind, rest) =
                //  normalize(e, x,
                //      let bind = alloc 1;
                //      let _ = store bind 0 x;
                //      rest)
                let x = Ident::fresh(&"x");
                let wild = Ident::fresh(&"_");
                self.translate_expr(
                    expr,
                    x,
                    cps::Expr::Prim {
                        bind,
                        prim: PrimOpr::Alloc,
                        args: vec![Atom::Int(1)],
                        rest: Box::new(cps::Expr::Prim {
                            bind: wild,
                            prim: PrimOpr::Store,
                            args: vec![Atom::Var(bind), Atom::Int(0), Atom::Var(x)],
                            rest: Box::new(rest),
                        }),
                    },
                )
            }
            ast::Expr::RefGet { expr, span: _ } => {
                //  normalize(^e, bind, rest) =
                //  normalize(e, r,
                //      let bind = load r 0;
                //      rest)
                let r = Ident::fresh(&"r");
                self.translate_expr(
                    expr,
                    r,
                    cps::Expr::Prim {
                        bind,
                        prim: PrimOpr::Load,
                        args: vec![Atom::Var(r), Atom::Int(0)],
                        rest: Box::new(rest),
                    },
                )
            }
            ast::Expr::Stmt {
                stmt,
                cont,
                span: _,
            } => {
                let cont = self.translate_expr(cont, bind, rest);
                match stmt.deref() {
                    ast::Stmt::Let {
                        ident,
                        typ: _,
                        expr,
                        span: _,
                    } => {
                        //  normalize(let x = e1; e2, bind, rest) =
                        //  normalize(e1, x, normalize(e2, bind, rest))
                        self.translate_expr(expr, *ident, cont)
                    }
                    ast::Stmt::RefSet { lhs, rhs, span: _ } => {
                        //  normalize(lhs <- rhs; e, bind, rest) =
                        //  normalize(lhs, r,
                        //      normalize(rhs, v,
                        //          let _ = store r 0 v;
                        //          normalize(e, bind, rest)))
                        let r = Ident::fresh(&"r");
                        let v = Ident::fresh(&"v");
                        let wild = Ident::fresh(&"_");
                        let inner = cps::Expr::Prim {
                            bind: wild,
                            prim: PrimOpr::Store,
                            args: vec![Atom::Var(r), Atom::Int(0), Atom::Var(v)],
                            rest: Box::new(cont),
                        };
                        let temp = self.translate_expr(rhs, v, inner);
                        self.translate_expr(lhs, r, temp)
                    }
                    ast::Stmt::Assign { lhs, rhs, span: _ } => {
                        //  normalize(e1.a := e2; e3, bind, rest) =
                        //  normalize(e1, r,
                        //      normalize(e2, v,
                        //          let _ = update r (i+1) v;
                        //          normalize(e3, bind, rest)))
                        //  (* where i is the index of field a, which is solved in type checker *)

                        let r = Ident::fresh(&"r");
                        let v = Ident::fresh(&"v");

                        let ast::Expr::Field {
                            expr,
                            field,
                            cons_info,
                            span: _,
                        } = lhs
                        else {
                            panic!("field access check with a non-field-access expression!")
                        };

                        let i = self.cons_map[&cons_info.unwrap()]
                            .1
                            .flds
                            .iter()
                            .find_position(|fld2| fld2.label == *field)
                            .unwrap()
                            .0;

                        let inner = cps::Expr::Update {
                            rec: Atom::Var(r),
                            idx: i + 1,
                            arg: Atom::Var(v),
                            rest: Box::new(cont),
                        };
                        let temp = self.translate_expr(rhs, v, inner);
                        self.translate_expr(expr, r, temp)
                    }
                    ast::Stmt::While {
                        cond,
                        body,
                        span: _,
                    } => {
                        //  normalize(while cond do e1 end; e2, bind, rest) =
                        //  decls
                        //      cont k1():
                        //          normalize(cond, p, if p then jump k2() else jump k3())
                        //      cont k2():
                        //          normalize(body, _, jump k1())
                        //      cont k3():
                        //          normalize(e2, bind, rest)
                        //  in
                        //      jump k1()
                        //  end
                        let k1 = Ident::fresh(&"k1");
                        let k2 = Ident::fresh(&"k2");
                        let k3 = Ident::fresh(&"k3");
                        let wild = Ident::fresh(&"_");
                        let p = Ident::fresh(&"p");
                        let cont1 = ContDecl {
                            cont: k1,
                            pars: Vec::new(),
                            body: self.translate_expr(
                                cond,
                                p,
                                cps::Expr::Ifte {
                                    cond: cps::IfCond::BTrue,
                                    args: vec![Atom::Var(p)],
                                    trbr: Box::new(cps::Expr::Jump {
                                        cont: k2,
                                        args: Vec::new(),
                                    }),
                                    flbr: Box::new(cps::Expr::Jump {
                                        cont: k3,
                                        args: Vec::new(),
                                    }),
                                },
                            ),
                        };
                        let cont2 = ContDecl {
                            cont: k2,
                            pars: Vec::new(),
                            body: self.translate_expr(
                                body,
                                wild,
                                cps::Expr::Jump {
                                    cont: k1,
                                    args: Vec::new(),
                                },
                            ),
                        };
                        let cont3 = ContDecl {
                            cont: k3,
                            pars: Vec::new(),
                            body: cont,
                        };
                        cps::Expr::Decls {
                            funcs: Vec::new(),
                            conts: vec![cont1, cont2, cont3],
                            body: Box::new(cps::Expr::Jump {
                                cont: k1,
                                args: Vec::new(),
                            }),
                        }
                    }
                    ast::Stmt::Do { expr, span: _ } => {
                        //  normalize(e1; e2, bind, rest) =
                        //  normalize(e1, _, normalize(e2, bind, rest))
                        let wild = Ident::fresh(&"_");
                        self.translate_expr(expr, wild, cont)
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
                    let data = self.cons_map[&cons_set[0]].0;
                    let conss = self.data_map[&data].clone();
                    for cons in cons_set {
                        assert!(conss.iter().any(|cons2| *cons2 == cons));
                    }

                    let mut brchs: Vec<(usize, cps::Expr)> = Vec::new();
                    for (i, cons) in conss.iter().enumerate() {
                        let binds = self.cons_map[cons]
                            .1
                            .flds
                            .iter()
                            .map(|fld| (fld.label, Ident::fresh(&"o")))
                            .collect();
                        let (new_mat, hits) = mat.specialize_cons(j, cons, &binds);

                        let brch = binds.iter().enumerate().fold(
                            self.normalize_match(&new_mat, decls),
                            |cont, (i, (_label, obj))| cps::Expr::Select {
                                bind: *obj,
                                rec: Atom::Var(mat.objs[j]),
                                idx: i + 1,
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
                    cps::Expr::Select {
                        bind: t,
                        rec: Atom::Var(mat.objs[j]),
                        idx: 0,
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
    let mut diags = Vec::new();
    let mut modl = crate::syntax::parser::parse_module(s, &mut diags).unwrap();
    assert!(diags.is_empty());
    crate::syntax::rename::rename_module(&mut modl, &mut diags).unwrap();
    let res = Translator::run(&modl);
    println!("{}", res);
}
