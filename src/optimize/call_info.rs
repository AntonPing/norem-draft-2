use super::anf::*;
use crate::utils::ident::Ident;
use std::collections::HashMap;

struct Info {
    use_times: usize,
    call_times: usize,
    tail_call_times: usize,
}

pub struct CallInfoScan {
    info_map: HashMap<Ident, Info>,
}

impl CallInfoScan {
    pub fn run(modl: &mut Module) {
        let mut pass = CallInfoScan {
            info_map: HashMap::new(),
        };
        pass.visit_module(modl);
    }

    fn visit_atom(&mut self, atom: &Atom) {
        if let Atom::Var(x) = atom {
            let res = self.info_map.get_mut(x);
            if let Some(info) = res {
                info.use_times += 1;
            }
        }
    }

    fn visit_module(&mut self, modl: &mut Module) {
        let Module { name: _, decls } = modl;
        for decl in decls.iter() {
            self.info_map.insert(
                decl.func,
                Info {
                    use_times: 0,
                    call_times: 0,
                    tail_call_times: 0,
                },
            );
        }
        for decl in decls.iter_mut() {
            let Decl {
                func: _,
                pars: _,
                body,
                info: _,
            } = decl;
            self.visit_expr(body);
        }
        for decl in decls.iter_mut() {
            let res = self.info_map.remove(&decl.func).unwrap();
            if res.use_times == res.call_times {
                if res.call_times == res.tail_call_times {
                    decl.info = CallInfo::JoinPoint;
                } else {
                    decl.info = CallInfo::Static;
                }
            } else {
                decl.info = CallInfo::NoInfo;
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Decls { decls, cont } => {
                for decl in decls.iter() {
                    self.info_map.insert(
                        decl.func,
                        Info {
                            use_times: 0,
                            call_times: 0,
                            tail_call_times: 0,
                        },
                    );
                }
                self.visit_expr(cont);
                for decl in decls.iter_mut() {
                    let Decl {
                        func: _,
                        pars: _,
                        body,
                        info: _,
                    } = decl;
                    self.visit_expr(body);
                }
                for decl in decls.iter_mut() {
                    let res = self.info_map.remove(&decl.func).unwrap();
                    if res.use_times == res.call_times {
                        if res.call_times == res.tail_call_times {
                            decl.info = CallInfo::JoinPoint;
                        } else {
                            decl.info = CallInfo::Static;
                        }
                    } else {
                        decl.info = CallInfo::NoInfo;
                    }
                }
            }
            Expr::Prim {
                bind,
                prim: _,
                args,
                cont,
            } => {
                self.visit_expr(cont);
                args.iter().for_each(|arg| self.visit_atom(arg));
                self.info_map.remove(bind);
            }
            Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                self.visit_expr(cont);
                args.iter().for_each(|arg| self.visit_atom(arg));
                if let Atom::Var(func) = func {
                    let res = self.info_map.get_mut(&func);
                    if let Some(info) = res {
                        info.use_times += 1;
                        info.call_times += 1;
                        match **cont {
                            Expr::Retn {
                                res: Atom::Var(bind2),
                            } if bind2 == *bind => {
                                info.tail_call_times += 1;
                            }
                            _ => {}
                        }
                    }
                } else {
                    unreachable!()
                }
                self.info_map.remove(bind);
            }
            Expr::Ifte {
                cond,
                args,
                trbr,
                flbr,
            } => todo!(),
            Expr::Switch { arg, brchs, dflt } => todo!(),
            Expr::Retn { res } => {
                self.visit_atom(res);
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn call_info_test() {
    let s = r#"
module Test where
fn f(x) begin
    let y = @iadd(x, 1);
    return y;
end
fn g(z) begin
    let a = f(z);
    let b = @iadd(a, 1);
    return b;
end
fn top() begin
    let r = g(42);
    return r;
end
"#;
    let mut modl = super::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    CallInfoScan::run(&mut modl);
    println!("{}\n", modl);
}
