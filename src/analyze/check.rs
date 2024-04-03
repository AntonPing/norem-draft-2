use crate::analyze::unify::{self, UnifySolver, UnifyType};
use crate::syntax::ast::*;
use crate::syntax::prim::Prim;
use crate::utils::ident::Ident;
use std::collections::HashMap;
use std::ops::DerefMut;

use super::diagnostic::Diagnostic;

#[derive(Clone, Debug)]
struct ValType {
    polys: Vec<Ident>,
    typ: UnifyType,
}

#[derive(Clone, Debug)]
struct ConsType {
    polys: Vec<Ident>,
    pars: Vec<Labeled<(bool, UnifyType)>>,
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
            let pars = cons
                .pars
                .iter()
                .map(|par| Labeled {
                    label: par.label,
                    data: par.data.1.clone(),
                    span: par.span.clone(),
                })
                .collect();
            let res = cons.res.clone();
            (pars, res)
        } else {
            let map = self.make_instantiate_map(&cons.polys);
            let pars = cons
                .pars
                .iter()
                .map(|par| Labeled {
                    label: par.label,
                    data: unify::substitute(&map, &par.data.1),
                    span: par.span.clone(),
                })
                .collect();
            let res = unify::substitute(&map, &cons.res);
            (pars, res)
        }
    }

    fn get_prim_type(&mut self, prim: &Prim) -> UnifyType {
        fn op0(res: LitType) -> UnifyType {
            UnifyType::Func(Vec::new(), Box::new(UnifyType::Lit(res)))
        }
        fn op1(par: LitType, res: LitType) -> UnifyType {
            UnifyType::Func(vec![UnifyType::Lit(par)], Box::new(UnifyType::Lit(res)))
        }
        fn op2(pars: LitType, res: LitType) -> UnifyType {
            UnifyType::Func(
                vec![UnifyType::Lit(pars), UnifyType::Lit(pars)],
                Box::new(UnifyType::Lit(res)),
            )
        }
        match prim {
            Prim::IAdd | Prim::ISub | Prim::IMul | Prim::IDiv | Prim::IRem => {
                op2(LitType::TyInt, LitType::TyInt)
            }
            Prim::INeg => op1(LitType::TyInt, LitType::TyInt),
            Prim::FAdd | Prim::FSub | Prim::FMul | Prim::FDiv => {
                op2(LitType::TyFloat, LitType::TyFloat)
            }
            Prim::FNeg => op1(LitType::TyFloat, LitType::TyFloat),
            Prim::ICmp(_) => op2(LitType::TyInt, LitType::TyBool),
            Prim::FCmp(_) => op2(LitType::TyFloat, LitType::TyBool),
            Prim::BAnd | Prim::BOr => op2(LitType::TyBool, LitType::TyBool),
            Prim::BNot => op1(LitType::TyBool, LitType::TyBool),
            Prim::Move => {
                let ty = self.fresh();
                UnifyType::Func(vec![ty.clone()], Box::new(ty))
            }
            Prim::Alloc => {
                let ty = self.fresh();
                UnifyType::Func(
                    vec![UnifyType::Lit(LitType::TyInt)],
                    Box::new(UnifyType::Cons(Ident::fresh(&"Array"), vec![ty])),
                )
            }
            Prim::Load => {
                let ty = self.fresh();
                UnifyType::Func(
                    vec![
                        UnifyType::Cons(Ident::fresh(&"Array"), vec![ty.clone()]),
                        UnifyType::Lit(LitType::TyInt),
                    ],
                    Box::new(ty),
                )
            }
            Prim::Store => {
                let ty = self.fresh();
                UnifyType::Func(
                    vec![
                        UnifyType::Cons(Ident::fresh(&"Array"), vec![ty.clone()]),
                        UnifyType::Lit(LitType::TyInt),
                        ty,
                    ],
                    Box::new(UnifyType::Lit(LitType::TyUnit)),
                )
            }
            Prim::IPrint => op1(LitType::TyInt, LitType::TyUnit),
            Prim::IScan => op0(LitType::TyInt),
            Prim::FPrint => op1(LitType::TyFloat, LitType::TyUnit),
            Prim::FScan => op0(LitType::TyFloat),
            Prim::CPrint => op1(LitType::TyChar, LitType::TyUnit),
            Prim::CScan => op0(LitType::TyChar),
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

    fn check_expr(&mut self, expr: &mut Expr) -> CheckResult<UnifyType> {
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
            Expr::Prim {
                prim,
                args,
                span: _,
            } => {
                let args_ty: Vec<UnifyType> = args
                    .iter_mut()
                    .map(|arg| self.check_expr(arg))
                    .collect::<CheckResult<Vec<_>>>()?;
                let prim_ty = self.get_prim_type(prim);
                let res_ty = self.fresh();
                self.unify(
                    &prim_ty,
                    &UnifyType::Func(args_ty, Box::new(res_ty.clone())),
                );
                Ok(res_ty)
            }
            Expr::Cons { cons, flds, span } => {
                if let Some(cons_ty) = self.cons_ctx.get(cons).cloned() {
                    let (pars, res) = self.instantiate_cons(&cons_ty);
                    for par in pars.iter() {
                        if let Some(fld) = flds.iter_mut().find(|fld| fld.label == par.label) {
                            let typ = self.check_expr(&mut fld.data)?;
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
                    .iter_mut()
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
                for rule in rules.iter_mut() {
                    self.check_rule(rule, &lhs, &rhs)?;
                }
                Ok(rhs)
            }
            Expr::Field { .. } => self.check_field_access(expr),
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
            } => match stmt.deref_mut() {
                Stmt::Let {
                    ident,
                    typ: ty_anno,
                    expr,
                    span: _,
                } => {
                    let typ = self.check_expr(expr)?;
                    if let Some(typ_anno) = ty_anno {
                        self.unify(&typ, &<UnifyType as From<&Type>>::from(typ_anno));
                    }
                    self.intro_val(ident, typ);
                    let res = self.check_expr(cont)?;
                    Ok(res)
                }
                Stmt::RefSet { lhs, rhs, span: _ } => {
                    let lhs = self.check_expr(lhs)?;
                    let rhs = self.check_expr(rhs)?;
                    self.unify(&lhs, &UnifyType::Cons(Ident::dummy(&"Ref"), vec![rhs]));
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
                Stmt::Assign { lhs, rhs, span: _ } => {
                    let typ1 = self.check_field_access(lhs)?;
                    let typ2 = self.check_expr(rhs)?;
                    self.unify(&typ1, &typ2);
                    let res_ty = self.check_expr(cont)?;

                    let Expr::Field {
                        expr: _,
                        field,
                        cons_info: Some(cons),
                        span: _,
                    } = lhs
                    else {
                        unreachable!()
                    };
                    let is_mut = self.cons_ctx[&cons]
                        .pars
                        .iter()
                        .find(|par| par.label == *field)
                        .map(|par| par.data.0)
                        .unwrap();
                    if is_mut {
                        Ok(res_ty)
                    } else {
                        self.diags.push(Diagnostic::error("not a mutable field!"));
                        Err("not a mutable field!".to_string())
                    }
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

    fn check_field_access(&mut self, expr: &mut Expr) -> CheckResult<UnifyType> {
        let Expr::Field {
            expr,
            field,
            cons_info,
            span,
        } = expr
        else {
            panic!("field access check with a non-field-access expression!")
        };

        assert!(cons_info.is_none());
        let typ = self.check_expr(expr)?;

        // rule 1: if it was as-binded in pattern matching, allow to access
        if let Expr::Var { ident, span: _ } = expr.deref_mut() {
            if let Some(cons) = self.as_bind.get(ident).cloned() {
                let cons_ty = self.cons_ctx[&cons].clone();
                let (pars, res) = self.instantiate_cons(&cons_ty);
                self.unify(&typ, &res);
                let par = pars.iter().find(|par| par.label == *field);
                if let Some(par) = par {
                    *cons_info = Some(cons);
                    return Ok(par.data.clone());
                }
            }
        }

        // rule 2: if the datatype is infered, and contains only one varient, allow to access
        let typ = self.solver.merge(&typ);
        if let UnifyType::Cons(data, _) = typ {
            let conss = self.data_ctx[&data].clone();
            if conss.len() == 1 {
                let cons = conss[0];
                let cons_ty = self.cons_ctx[&cons].clone();
                let (pars, res) = self.instantiate_cons(&cons_ty);
                self.unify(&typ, &res);
                let par = pars.iter().find(|par| par.label == *field);
                if let Some(par) = par {
                    *cons_info = Some(cons);
                    return Ok(par.data.clone());
                }
            }
        }

        self.diags.push(
            Diagnostic::error("cannot infer field access constructor!")
                .line_span(span.clone(), "here is the field access"),
        );

        Err("cannot infer field access constructor!".to_string())
    }

    fn check_rule(&mut self, rule: &mut Rule, lhs: &UnifyType, rhs: &UnifyType) -> CheckResult<()> {
        self.check_pattern(&mut rule.patn, lhs)?;
        let typ = self.check_expr(&mut rule.body)?;
        self.unify(&typ, rhs);
        Ok(())
    }

    fn check_pattern(&mut self, patn: &mut Pattern, lhs: &UnifyType) -> CheckResult<()> {
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
                        if let Some(patn) = patns.iter_mut().find(|patn| patn.label == par.label) {
                            self.check_pattern(&mut patn.data, &par.data)?;
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

    fn check_decl(&mut self, decl: &mut Decl) -> CheckResult<()> {
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
                    self.intro_val(par, <UnifyType as From<&Type>>::from(typ));
                }
                let res_ty = self.check_expr(body)?;
                self.unify(&res_ty, &<UnifyType as From<&Type>>::from(res));
                Ok(())
            }
            Decl::Data { .. } => Ok(()),
        }
    }

    fn check_module(&mut self, modl: &mut Module) -> CheckResult<()> {
        let Module { name: _, decls } = modl;
        for decl in decls.iter() {
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
                                    data: (data.0, UnifyType::from(&data.1)),
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
        for decl in decls.iter_mut() {
            self.check_decl(decl)?;
        }
        Ok(())
    }
}

pub fn check_expr<'diag>(
    expr: &mut Expr,
    diags: &'diag mut Vec<Diagnostic>,
) -> CheckResult<UnifyType> {
    let mut pass = TypeChecker::new(diags);
    let res = pass.check_expr(expr)?;
    Ok(pass.solver.merge(&res))
}

pub fn check_module<'diag>(
    modl: &mut Module,
    diags: &'diag mut Vec<Diagnostic>,
) -> CheckResult<()> {
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
    check_module(&mut modl, &mut diags).unwrap();
    for diag in diags {
        println!("{}", diag.report(s, 10));
    }
}
