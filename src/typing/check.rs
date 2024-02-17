use crate::syntax::ast::*;
use crate::typing::unify::{UnifySolver, UnifyType};
use crate::utils::ident::Ident;
use std::collections::HashMap;
use std::ops::Deref;

struct TypeChecker {
    context: HashMap<Ident, UnifyType>,
    solver: UnifySolver,
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker {
            context: HashMap::new(),
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
                if let Some(typ) = self.context.get(&ident) {
                    Ok(typ.clone())
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
                    PrimOpr::Move => {
                        let arg0 = self.check_expr(&args[0])?;
                        Ok(arg0)
                    }
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
                        self.context.insert(*par, cell.clone());
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
                    self.context.insert(*ident, ty);
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

    fn check_decl(&mut self, decl: &Decl) -> CheckResult<()> {
        match decl {
            Decl::Func {
                pars, res, body, ..
            } => {
                for (par, typ) in pars {
                    self.context.insert(*par, typ.into());
                }
                let res_ty = self.check_expr(body)?;
                self.solver.unify(&res_ty, &res.into())?;
                Ok(())
            }
        }
    }

    fn check_module(&mut self, modl: &Module) -> CheckResult<()> {
        let Module { name: _, decls } = modl;
        for decl in decls {
            match decl {
                Decl::Func {
                    func, pars, res, ..
                } => {
                    let (_, par_tys): (Vec<Ident>, Vec<UnifyType>) =
                        pars.iter().map(|(par, typ)| (par, typ.into())).unzip();
                    let res_ty: UnifyType = res.into();
                    let func_ty = UnifyType::Func(par_tys, Box::new(res_ty));
                    self.context.insert(*func, func_ty);
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
module test where
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
"#;

    let mut modl = crate::syntax::parser::parse_module(s).unwrap();
    crate::syntax::rename::rename_module(&mut modl).unwrap();
    check_module(&modl).unwrap();
}
