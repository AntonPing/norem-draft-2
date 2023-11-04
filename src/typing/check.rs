use crate::syntax::ast::*;
use crate::typing::unify::{UnifySolver, UnifyType};
use crate::utils::ident::Ident;
use std::collections::HashMap;

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
    fn infer_expr(&mut self, expr: &Expr) -> CheckResult<UnifyType> {
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
                        let arg0 = self.infer_expr(&args[0])?;
                        self.solver.unify(&arg0, &UnifyType::Lit(LitType::TyInt))?;
                        let arg1 = self.infer_expr(&args[1])?;
                        self.solver.unify(&arg1, &UnifyType::Lit(LitType::TyInt))?;
                        Ok(UnifyType::Lit(LitType::TyInt))
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
                let body_ty = Box::new(self.infer_expr(body)?);
                Ok(UnifyType::Func(pars_ty, body_ty))
            }
            Expr::App {
                func,
                args,
                span: _,
            } => {
                let func_ty = self.infer_expr(func)?;
                let args_ty = args
                    .iter()
                    .map(|arg| self.infer_expr(arg))
                    .collect::<CheckResult<Vec<_>>>()?;
                let res_ty = self.solver.new_cell();
                self.solver.unify(
                    &func_ty,
                    &UnifyType::Func(args_ty, Box::new(res_ty.clone())),
                )?;
                Ok(res_ty)
            }
        }
    }
}

pub fn expr_infer(expr: &Expr) -> CheckResult<UnifyType> {
    let mut pass = TypeChecker::new();
    let res = pass.infer_expr(expr)?;
    Ok(pass.solver.merge(&res))
}

#[test]
#[ignore = "just to see result"]
fn check_test() {
    use crate::syntax::parser::parse_expr;
    use crate::syntax::rename::rename_expr;
    let s = r#"
fn(f) => fn(g) => fn(x) => (f(x))(g(x))
"#;
    let mut res = parse_expr(s).unwrap();
    rename_expr(&mut res).unwrap();
    let ty = expr_infer(&res).unwrap();
    println!("{:#?}", ty);
}
