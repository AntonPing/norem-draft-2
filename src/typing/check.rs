use crate::syntax::ast::*;
use crate::typing::unify::{self, UnifySolver, UnifyType};
use crate::utils::ident::Ident;
use std::collections::HashMap;
use std::ops::Deref;

struct TypeChecker {
    val_ctx: HashMap<Ident, (Vec<Ident>, UnifyType)>,
    cons_ctx: HashMap<Ident, (Vec<Ident>, Vec<Labeled<UnifyType>>, UnifyType)>,
    solver: UnifySolver,
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker {
            val_ctx: HashMap::new(),
            cons_ctx: HashMap::new(),
            solver: UnifySolver::new(),
        }
    }
}

type CheckResult<T> = Result<T, String>;

impl TypeChecker {
    fn check_expr(&mut self, expr: &Expr) -> CheckResult<UnifyType> {
        match expr {
            Expr::Lit { lit, span: _ } => {
                let typ = UnifyType::Lit(lit.get_lit_type());
                Ok(typ)
            }
            Expr::Var { ident, span: _ } => {
                if let Some((polys, typ)) = self.val_ctx.get(&ident) {
                    Ok(self.solver.instantiate(polys, typ))
                } else {
                    Err("Can't find variable in scope!".to_string())
                }
            }
            Expr::Prim {
                prim,
                args,
                span: _,
            } => {
                if args.len() != prim.get_arity() {
                    return Err("Primitive with wrong number of arguments!".to_string());
                }
                match prim {
                    PrimOpr::IAdd | PrimOpr::ISub | PrimOpr::IMul => {
                        let arg0 = self.check_expr(&args[0])?;
                        self.solver.unify(&arg0, &UnifyType::Lit(LitType::TyInt))?;
                        let arg1 = self.check_expr(&args[1])?;
                        self.solver.unify(&arg1, &UnifyType::Lit(LitType::TyInt))?;
                        Ok(UnifyType::Lit(LitType::TyInt))
                    }
                    PrimOpr::ICmpLs | PrimOpr::ICmpEq | PrimOpr::ICmpGr => {
                        let arg0 = self.check_expr(&args[0])?;
                        self.solver.unify(&arg0, &UnifyType::Lit(LitType::TyInt))?;
                        let arg1 = self.check_expr(&args[1])?;
                        self.solver.unify(&arg1, &UnifyType::Lit(LitType::TyInt))?;
                        Ok(UnifyType::Lit(LitType::TyBool))
                    }
                }
            }
            Expr::Cons {
                cons,
                flds,
                span: _,
            } => {
                if let Some((polys, args, res)) = self.cons_ctx.get(cons).cloned() {
                    if flds.len() == args.len() {
                        let map = self.solver.make_instantiate_map(&polys);
                        for arg in args {
                            if let Some(fld) = flds.iter().find(|fld| fld.label == arg.label) {
                                let typ1 = self.check_expr(&fld.data)?;
                                let typ2 = unify::substitute(&map, &arg.data);
                                self.solver.unify(&typ1, &typ2)?;
                            } else {
                                return Err("Construct application with wrong label!".to_string());
                            }
                        }
                        let res = unify::substitute(&map, &res);
                        Ok(res)
                    } else {
                        Err("Construct application with wrong argument length!".to_string())
                    }
                } else {
                    Err(format!("Can't find constructor {} in scope!", cons))
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
                        let cell = self.solver.new_cell();
                        self.val_ctx.insert(*par, (Vec::new(), cell.clone()));
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
                let res_ty = self.solver.new_cell();
                self.solver.unify(
                    &func_ty,
                    &UnifyType::Func(args_ty, Box::new(res_ty.clone())),
                )?;
                Ok(res_ty)
            }
            Expr::Ifte {
                cond,
                trbr,
                flbr,
                span: _,
            } => {
                let cond_ty = self.check_expr(cond)?;
                self.solver
                    .unify(&cond_ty, &UnifyType::Lit(LitType::TyBool))?;
                let trbr_ty = self.check_expr(trbr)?;
                let flbr_ty = self.check_expr(flbr)?;
                self.solver.unify(&trbr_ty, &flbr_ty)?;
                Ok(trbr_ty)
            }
            Expr::Case {
                expr,
                rules,
                span: _,
            } => {
                let lhs = self.check_expr(expr)?;
                let rhs = self.solver.new_cell();
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
                let cell = self.solver.new_cell();
                self.solver.unify(
                    &typ,
                    &UnifyType::Cons(Ident::dummy(&"Ref"), vec![cell.clone()]),
                )?;
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
                    let ty = self.check_expr(expr)?;
                    if let Some(ty_anno) = ty_anno {
                        self.solver.unify(&ty, &ty_anno.into())?;
                    }
                    self.val_ctx.insert(*ident, (Vec::new(), ty));
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
                Stmt::Assign { lhs, rhs, span: _ } => {
                    let lhs = self.check_expr(lhs)?;
                    let rhs = self.check_expr(rhs)?;
                    self.solver
                        .unify(&lhs, &UnifyType::Cons(Ident::dummy(&"Ref"), vec![rhs]))?;
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
                Stmt::While {
                    cond,
                    body,
                    span: _,
                } => {
                    let cond_ty = self.check_expr(cond)?;
                    self.solver
                        .unify(&cond_ty, &UnifyType::Lit(LitType::TyBool))?;
                    let body_ty = self.check_expr(body)?;
                    self.solver
                        .unify(&body_ty, &UnifyType::Lit(LitType::TyUnit))?;
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
                Stmt::Do { expr, span: _ } => {
                    let ty = self.check_expr(expr)?;
                    self.solver.unify(&ty, &UnifyType::Lit(LitType::TyUnit))?;
                    let res_ty = self.check_expr(cont)?;
                    Ok(res_ty)
                }
            },
        }
    }

    fn check_rule(&mut self, rule: &Rule, lhs: &UnifyType, rhs: &UnifyType) -> CheckResult<()> {
        self.check_pattern(&rule.patn, lhs)?;
        let typ = self.check_expr(&rule.body)?;
        self.solver.unify(&typ, rhs)?;
        Ok(())
    }

    fn check_pattern(&mut self, patn: &Pattern, lhs: &UnifyType) -> CheckResult<()> {
        match patn {
            Pattern::Var { ident, span: _ } => {
                self.val_ctx.insert(*ident, (Vec::new(), lhs.clone()));
                Ok(())
            }
            Pattern::Lit { lit, span: _ } => {
                self.solver
                    .unify(&UnifyType::Lit(lit.get_lit_type()), lhs)?;
                Ok(())
            }
            Pattern::Cons {
                cons,
                patns,
                span: _,
            } => {
                if let Some((polys, args, res)) = self.cons_ctx.get(cons).cloned() {
                    if patns.len() == args.len() {
                        let map = self.solver.make_instantiate_map(&polys);
                        for arg in args {
                            if let Some(patn) = patns.iter().find(|patn| patn.label == arg.label) {
                                let typ = unify::substitute(&map, &arg.data);
                                self.check_pattern(&patn.data, &typ)?;
                            } else {
                                return Err("Construct application with wrong label!".to_string());
                            }
                        }
                        let res = unify::substitute(&map, &res);
                        self.solver.unify(&res, lhs)
                    } else {
                        Err("Construct application with wrong argument length!".to_string())
                    }
                } else {
                    Err(format!("Can't find constructor {} in scope!", cons))
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
                    self.val_ctx.insert(*par, (Vec::new(), typ.into()));
                }
                let res_ty = self.check_expr(body)?;
                self.solver.unify(&res_ty, &res.into())?;
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
                    self.val_ctx.insert(*func, (polys.clone(), func_ty));
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
                        self.cons_ctx
                            .insert(var.cons, (polys.clone(), flds, res.clone()));
                    }
                }
            }
        }
        for decl in decls {
            self.check_decl(decl)?;
        }
        Ok(())
    }
}

pub fn check_expr(expr: &Expr) -> CheckResult<UnifyType> {
    let mut pass = TypeChecker::new();
    let res = pass.check_expr(expr)?;
    Ok(pass.solver.merge(&res))
}

pub fn check_module(modl: &Module) -> CheckResult<()> {
    let mut pass = TypeChecker::new();
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
function id[T](x: T) -> T
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
    check_module(&modl).unwrap();
}
