use crate::analyze::unify::{self, UnifySolver, UnifyType};
use crate::syntax::ast::*;
use crate::utils::ident::Ident;
use std::collections::HashMap;
use std::ops::Deref;

use super::diagnostic::Diagnostic;

#[derive(Clone, Debug)]
struct ValType {
    polys: Vec<Ident>,
    typ: UnifyType,
}

#[derive(Clone, Debug)]
struct ConsType {
    polys: Vec<Ident>,
    pars: Vec<Labeled<UnifyType>>,
    res: UnifyType,
}

struct TypeChecker<'diag> {
    val_ctx: HashMap<Ident, ValType>,
    cons_ctx: HashMap<Ident, ConsType>,
    data_ctx: HashMap<Ident, Vec<Ident>>,
    as_bind: HashMap<Ident, Ident>,
    solver: UnifySolver,
    diags: &'diag mut Vec<Diagnostic>,
}

type CheckResult<T> = Result<T, String>;

impl<'diag> TypeChecker<'diag> {
    pub fn new(diags: &'diag mut Vec<Diagnostic>) -> TypeChecker<'diag> {
        TypeChecker {
            val_ctx: HashMap::new(),
            cons_ctx: HashMap::new(),
            data_ctx: HashMap::new(),
            as_bind: HashMap::new(),
            solver: UnifySolver::new(),
            diags,
        }
    }

    fn fresh(&mut self) -> UnifyType {
        UnifyType::Cell(self.solver.new_cell())
    }

    fn unify(&mut self, typ1: &UnifyType, typ2: &UnifyType) {
        match self.solver.unify(typ1, typ2) {
            Ok(()) => {}
            Err(err) => match err {
                unify::UnifyError::VecDiffLen(_typs1, _typs2) => {
                    self.diags.push(Diagnostic::error(
                        "cannot unify varibles with different length!",
                    ));
                }
                unify::UnifyError::CannotUnify(_typ1, _typ2) => {
                    self.diags.push(Diagnostic::error("cannot unify types!"));
                }
                unify::UnifyError::OccurCheckFailed(_var, _typ) => {
                    self.diags.push(Diagnostic::error("occur check failed!"));
                }
            },
        }
    }

    fn make_instantiate_map(&mut self, polys: &Vec<Ident>) -> HashMap<Ident, usize> {
        polys
            .iter()
            .map(|poly| (*poly, self.solver.new_cell()))
            .collect()
    }

    fn instantiate_val(&mut self, val: &ValType) -> UnifyType {
        if val.polys.is_empty() {
            val.typ.clone()
        } else {
            let map = self.make_instantiate_map(&val.polys);
            unify::substitute(&map, &val.typ)
        }
    }

    fn instantiate_cons(&mut self, cons: &ConsType) -> (Vec<Labeled<UnifyType>>, UnifyType) {
        if cons.polys.is_empty() {
            (cons.pars.clone(), cons.res.clone())
        } else {
            let map = self.make_instantiate_map(&cons.polys);
            let pars = cons
                .pars
                .iter()
                .map(|par| Labeled {
                    label: par.label,
                    data: unify::substitute(&map, &par.data),
                    span: par.span.clone(),
                })
                .collect();
            let res = unify::substitute(&map, &cons.res);
            (pars, res)
        }
    }

    fn intro_val(&mut self, ident: &Ident, typ: UnifyType) {
        self.val_ctx.insert(
            *ident,
            ValType {
                polys: Vec::new(),
                typ,
            },
        );
    }

    fn check_expr(&mut self, expr: &Expr) -> CheckResult<UnifyType> {
        match expr {
            Expr::Lit { lit, span: _ } => {
                let typ = UnifyType::Lit(lit.get_lit_type());
                Ok(typ)
            }
            Expr::Var { ident, span: _ } => {
                if let Some(val_ty) = self.val_ctx.get(&ident).cloned() {
                    Ok(self.instantiate_val(&val_ty))
                } else {
                    // the error reporting part should be in renamer
                    panic!("value variable not in context!")
                }
            }
            Expr::Prim { prim, args, span } => {
                if args.len() != prim.get_arity() {
                    self.diags.push(
                        Diagnostic::error("primitive with wrong number of aruments!")
                            .line_span(span.clone(), "here is the primitive application"),
                    );
                    let res = match prim {
                        PrimOpr::IAdd | PrimOpr::ISub | PrimOpr::IMul => {
                            UnifyType::Lit(LitType::TyInt)
                        }
                        PrimOpr::ICmpLs | PrimOpr::ICmpEq | PrimOpr::ICmpGr => {
                            UnifyType::Lit(LitType::TyBool)
                        }
                    };
                    return Ok(res);
                }
                match prim {
                    PrimOpr::IAdd | PrimOpr::ISub | PrimOpr::IMul => {
                        let arg0 = self.check_expr(&args[0])?;
                        self.unify(&arg0, &UnifyType::Lit(LitType::TyInt));
                        let arg1 = self.check_expr(&args[1])?;
                        self.unify(&arg1, &UnifyType::Lit(LitType::TyInt));
                        Ok(UnifyType::Lit(LitType::TyInt))
                    }
                    PrimOpr::ICmpLs | PrimOpr::ICmpEq | PrimOpr::ICmpGr => {
                        let arg0 = self.check_expr(&args[0])?;
                        self.unify(&arg0, &UnifyType::Lit(LitType::TyInt));
                        let arg1 = self.check_expr(&args[1])?;
                        self.unify(&arg1, &UnifyType::Lit(LitType::TyInt));
                        Ok(UnifyType::Lit(LitType::TyBool))
                    }
                }
            }
            Expr::Cons { cons, flds, span } => {
                if let Some(cons_ty) = self.cons_ctx.get(cons).cloned() {
                    let (pars, res) = self.instantiate_cons(&cons_ty);
                    for par in pars.iter() {
                        if let Some(fld) = flds.iter().find(|fld| fld.label == par.label) {
                            let typ = self.check_expr(&fld.data)?;
                            self.unify(&typ, &par.data);
                        } else {
                            self.diags.push(
                                Diagnostic::error("constructor label missing!").line_span(
                                    span.clone(),
                                    format!("label {} is missing!", par.label),
                                ),
                            );
                        }
                    }
                    for fld in flds {
                        if pars.iter().find(|par| fld.label == par.label).is_none() {
                            self.diags.push(
                                Diagnostic::error("constructor label not defined!").line_span(
                                    span.clone(),
                                    format!("label {} not found!", fld.label),
                                ),
                            );
                        }
                    }
                    Ok(res)
                } else {
                    // the error reporting part should be in renamer
                    panic!("constructor not in context!")
                }
            }
            Expr::Func {
                pars,
                body,
                span: _,
            } => {
                let pars_ty: Vec<UnifyType> = pars
                    .iter()
                    .map(|par| {
                        let cell = self.fresh();
                        self.intro_val(par, cell.clone());
                        cell
                    })
                    .collect();
                let body_ty = Box::new(self.check_expr(body)?);
                Ok(UnifyType::Func(pars_ty, body_ty))
            }
            Expr::App {
                func,
                args,
                span: _,
            } => {
                let func_ty = self.check_expr(func)?;
                let args_ty = args
                    .iter()
                    .map(|arg| self.check_expr(arg))
                    .collect::<CheckResult<Vec<_>>>()?;
                let res_ty = self.fresh();
                self.unify(
                    &func_ty,
                    &UnifyType::Func(args_ty, Box::new(res_ty.clone())),
                );
                Ok(res_ty)
            }
            Expr::Ifte {
                cond,
                trbr,
                flbr,
                span: _,
            } => {
                let cond_ty = self.check_expr(cond)?;
                self.unify(&cond_ty, &UnifyType::Lit(LitType::TyBool));
                let trbr_ty = self.check_expr(trbr)?;
                let flbr_ty = self.check_expr(flbr)?;
                self.unify(&trbr_ty, &flbr_ty);
                Ok(trbr_ty)
            }
            Expr::Case {
                expr,
                rules,
                span: _,
            } => {
                let lhs = self.check_expr(expr)?;
                let rhs = self.fresh();
                for rule in rules.iter() {
                    self.check_rule(rule, &lhs, &rhs)?;
                }
                Ok(rhs)
            }
            Expr::NewRef { expr, span: _ } => {
                let typ = self.check_expr(expr)?;
                Ok(UnifyType::Cons(Ident::dummy(&"Ref"), vec![typ]))
            }
            Expr::RefGet { expr, span: _ } => {
                let typ = self.check_expr(expr)?;
                let cell = self.fresh();
                self.unify(
                    &typ,
                    &UnifyType::Cons(Ident::dummy(&"Ref"), vec![cell.clone()]),
                );
                Ok(cell)
            }
            Expr::Stmt {
                stmt,
                cont,
                span: _,
            } => match stmt.deref() {
                Stmt::Let {
                    ident,
                    typ: ty_anno,
                    expr,
                    span: _,
                } => {
                    let typ = self.check_expr(expr)?;
                    if let Some(typ_anno) = ty_anno {
                        self.unify(&typ, &typ_anno.into());
                    }
                    self.intro_val(ident, typ);
                    let res = self.check_expr(cont)?;
                    Ok(res)
                }
                Stmt::Assign { lhs, rhs, span: _ } => {
                    let lhs = self.check_expr(lhs)?;
                    let rhs = self.check_expr(rhs)?;
                    self.unify(&lhs, &UnifyType::Cons(Ident::dummy(&"Ref"), vec![rhs]));
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
                Stmt::While {
                    cond,
                    body,
                    span: _,
                } => {
                    let cond_ty = self.check_expr(cond)?;
                    self.unify(&cond_ty, &UnifyType::Lit(LitType::TyBool));
                    let body_ty = self.check_expr(body)?;
                    self.unify(&body_ty, &UnifyType::Lit(LitType::TyUnit));
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
                Stmt::Do { expr, span: _ } => {
                    let ty = self.check_expr(expr)?;
                    self.unify(&ty, &UnifyType::Lit(LitType::TyUnit));
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
            },
        }
    }

    fn check_rule(&mut self, rule: &Rule, lhs: &UnifyType, rhs: &UnifyType) -> CheckResult<()> {
        self.check_pattern(&rule.patn, lhs)?;
        let typ = self.check_expr(&rule.body)?;
        self.unify(&typ, rhs);
        Ok(())
    }

    fn check_pattern(&mut self, patn: &Pattern, lhs: &UnifyType) -> CheckResult<()> {
        match patn {
            Pattern::Var { ident, span: _ } => {
                self.intro_val(ident, lhs.clone());
                Ok(())
            }
            Pattern::Lit { lit, span: _ } => {
                self.unify(&UnifyType::Lit(lit.get_lit_type()), lhs);
                Ok(())
            }
            Pattern::Cons {
                cons,
                patns,
                as_ident,
                span,
            } => {
                if let Some(as_ident) = as_ident {
                    self.intro_val(as_ident, lhs.clone());
                    self.as_bind.insert(*as_ident, *cons);
                }
                if let Some(cons_ty) = self.cons_ctx.get(cons).cloned() {
                    let (pars, res) = self.instantiate_cons(&cons_ty);
                    for par in pars.iter() {
                        if let Some(patn) = patns.iter().find(|patn| patn.label == par.label) {
                            self.check_pattern(&patn.data, &par.data)?;
                        } else {
                            self.diags.push(
                                Diagnostic::error("constructor label missing!").line_span(
                                    span.clone(),
                                    format!("label {} is missing!", par.label),
                                ),
                            );
                        }
                    }
                    for patn in patns.iter() {
                        if pars.iter().find(|arg| patn.label == arg.label).is_none() {
                            self.diags.push(
                                Diagnostic::error("constructor label not defined!").line_span(
                                    span.clone(),
                                    format!("label {} not found!", patn.label),
                                ),
                            );
                        }
                    }
                    self.unify(&res, lhs);
                    Ok(())
                } else {
                    // the error reporting part should be in renamer
                    Ok(())
                }
            }
            Pattern::Wild { span: _ } => Ok(()),
        }
    }

    fn check_decl(&mut self, decl: &Decl) -> CheckResult<()> {
        match decl {
            Decl::Func {
                sign:
                    FuncSign {
                        func: _,
                        polys: _,
                        pars,
                        res,
                        span: _,
                    },
                body,
                span: _,
            } => {
                for (par, typ) in pars {
                    self.intro_val(par, typ.into());
                }
                let res_ty = self.check_expr(body)?;
                self.unify(&res_ty, &res.into());
                Ok(())
            }
            Decl::Data { .. } => Ok(()),
        }
    }

    fn check_module(&mut self, modl: &Module) -> CheckResult<()> {
        let Module { name: _, decls } = modl;
        for decl in decls {
            match decl {
                Decl::Func {
                    sign:
                        FuncSign {
                            func,
                            polys,
                            pars,
                            res,
                            span: _,
                        },
                    body: _,
                    span: _,
                } => {
                    let (_, par_tys): (Vec<Ident>, Vec<UnifyType>) =
                        pars.iter().map(|(par, typ)| (par, typ.into())).unzip();
                    let res_ty: UnifyType = res.into();
                    let func_ty = UnifyType::Func(par_tys, Box::new(res_ty));
                    self.val_ctx.insert(
                        *func,
                        ValType {
                            polys: polys.clone(),
                            typ: func_ty,
                        },
                    );
                }
                Decl::Data {
                    ident,
                    polys,
                    vars,
                    span: _,
                } => {
                    let res = UnifyType::Cons(
                        *ident,
                        polys.iter().map(|poly| UnifyType::Var(*poly)).collect(),
                    );

                    for var in vars {
                        let flds = var
                            .flds
                            .iter()
                            .map(|fld| {
                                let Labeled { label, data, span } = fld;
                                Labeled {
                                    label: *label,
                                    data: data.into(),
                                    span: span.clone(),
                                }
                            })
                            .collect();
                        self.cons_ctx.insert(
                            var.cons,
                            ConsType {
                                polys: polys.clone(),
                                pars: flds,
                                res: res.clone(),
                            },
                        );
                    }
                    self.data_ctx
                        .insert(*ident, vars.iter().map(|var| var.cons).collect());
                }
            }
        }
        for decl in decls {
            self.check_decl(decl)?;
        }
        Ok(())
    }
}

pub fn check_expr<'diag>(expr: &Expr, diags: &'diag mut Vec<Diagnostic>) -> CheckResult<UnifyType> {
    let mut pass = TypeChecker::new(diags);
    let res = pass.check_expr(expr)?;
    Ok(pass.solver.merge(&res))
}

pub fn check_module<'diag>(modl: &Module, diags: &'diag mut Vec<Diagnostic>) -> CheckResult<()> {
    let mut pass = TypeChecker::new(diags);
    pass.check_module(modl)?;
    Ok(())
}

#[test]
#[ignore = "just to see result"]
fn check_test() {
    let s = r#"
module Test where
datatype List[T] where
| Nil
| Cons(T, List[T])
end
function map[T, U](f: fn(T) -> U, xs: List[T]) -> List[U]
begin
    match xs with
    | Nil => Nil
    | Cons(x, xs) => Cons(f(x), map(f,xs))
    end
end
datatype List2[T] where
| Nil2
| Cons2 { head: T, tail: List2[T] }
end
function map2[T, U](f: fn(T) -> U, xs: List2[T]) -> List2[U]
begin
    match xs with
    | Nil2 => Nil2
    | Cons2 { head, tail } => 
        Cons2 { head: f(head), tail: map2(f,tail) }
    end
end
function f(x: Int) -> Int
begin
    let f = fn(x) => @iadd(x,1);
    let res = f(42);
    let test = if @icmpls(1, 2) then 3 else 4;
    res
end
function g(x: Int) -> Int
begin
    let r = @iadd(x, 1);
    r
end
function id[T, U](x: U) -> T
begin
    let r = ref 42;
    r := ^r;
    x
end
"#;
    let mut diags = Vec::new();
    let mut modl = crate::syntax::parser::parse_module(s, &mut diags).unwrap();
    assert!(diags.is_empty());
    println!("{:#?}", &modl);
    crate::syntax::rename::rename_module(&mut modl, &mut diags).unwrap();
    println!("{:#?}", &modl);
    check_module(&modl, &mut diags).unwrap();
    for diag in diags {
        println!("{}", diag.report(s, 10));
    }
}
