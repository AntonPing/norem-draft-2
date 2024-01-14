use super::instr::{Block, Instr, Reg};
use crate::optimize::anf::*;
use crate::utils::ident::Ident;
use std::collections::HashMap;

pub struct Codegen {
    code: Vec<Instr>,
    blocks: Vec<Block>,
    max_reg: usize,
    reg_map: HashMap<Ident, Reg>,
}
impl Codegen {
    pub fn run(decls: &Vec<Decl>) -> Vec<Block> {
        let mut pass = Codegen {
            code: Vec::new(),
            blocks: Vec::new(),
            max_reg: 0,
            reg_map: HashMap::new(),
        };
        for decl in decls {
            pass.visit_decl(decl);
        }

        pass.blocks
    }

    fn new_reg(&mut self) -> Reg {
        let res = self.max_reg;
        self.max_reg += 1;
        Reg(res)
    }

    fn lookup_var(&self, var: &Ident) -> Result<Reg, Ident> {
        if let Some(res) = self.reg_map.get(&var) {
            Ok(*res)
        } else {
            // if not assigned to a register, it should be a label
            Err(*var)
        }
    }

    fn visit_atom(&mut self, atom: &Atom) -> Reg {
        if let Atom::Var(var) = atom {
            match self.lookup_var(var) {
                Ok(reg2) => {
                    return reg2;
                }
                Err(addr) => {
                    let reg = self.new_reg();
                    self.code.push(Instr::LitAu(reg, addr));
                    reg
                }
            }
        } else {
            let reg = self.new_reg();
            match atom {
                Atom::Var(_) => unreachable!(),
                Atom::Int(val) => {
                    self.code.push(Instr::LitI(reg, *val));
                }
                Atom::Float(val) => {
                    self.code.push(Instr::LitF(reg, *val));
                }
                Atom::Bool(false) => {
                    self.code.push(Instr::LitI(reg, 0));
                }
                Atom::Bool(true) => {
                    self.code.push(Instr::LitI(reg, 1));
                }
                Atom::Char(val) => {
                    self.code.push(Instr::LitC(reg, *val));
                }
                Atom::Unit => {}
            }
            reg
        }
    }

    fn visit_decl(&mut self, decl: &Decl) {
        let Decl { func, pars, body } = decl;
        self.max_reg = 0;

        for par in pars.iter() {
            let reg = self.new_reg();
            self.code.push(Instr::Pop(reg));
            self.reg_map.insert(*par, reg);
        }

        self.visit_expr(body);

        let mut code = Vec::new();
        std::mem::swap(&mut code, &mut self.code);

        let block = Block {
            func: *func,
            max_reg: self.max_reg,
            code,
        };
        self.blocks.push(block);
    }

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Decls { decls: _, cont: _ } => {
                panic!("code generation should be done after closure convertion!");
            }
            Expr::Prim {
                bind,
                prim,
                args,
                cont,
            } => {
                let ret = self.new_reg();
                match prim.get_arity() {
                    Some(1) => {
                        assert_eq!(args.len(), 1);
                        match (prim, args[0]) {
                            (PrimOpr::Move, arg1) => {
                                let arg1 = self.visit_atom(&arg1);
                                self.code.push(Instr::Move(ret, arg1));
                            }
                            _ => unreachable!(),
                        }
                    }
                    Some(2) => {
                        assert_eq!(args.len(), 2);
                        match (prim, args[0], args[1]) {
                            (PrimOpr::IAdd, arg1, arg2) => {
                                let arg1 = self.visit_atom(&arg1);
                                let arg2 = self.visit_atom(&arg2);
                                self.code.push(Instr::IAdd(ret, arg1, arg2));
                            }
                            (PrimOpr::ISub, arg1, arg2) => {
                                let arg1 = self.visit_atom(&arg1);
                                let arg2 = self.visit_atom(&arg2);
                                self.code.push(Instr::ISub(ret, arg1, arg2));
                            }
                            (PrimOpr::IMul, arg1, arg2) => {
                                let arg1 = self.visit_atom(&arg1);
                                let arg2 = self.visit_atom(&arg2);
                                self.code.push(Instr::IMul(ret, arg1, arg2));
                            }
                            (PrimOpr::Select, arg1, arg2) => {
                                let arg1 = self.visit_atom(&arg1);
                                let arg2 = self.visit_atom(&arg2);
                                self.code.push(Instr::Load(ret, arg1, arg2));
                            }
                            _ => unreachable!(),
                        }
                        assert_eq!(args.len(), 2);
                    }
                    Some(_) => unreachable!(),
                    None => match prim {
                        PrimOpr::Record => {
                            self.code.push(Instr::Alloc(ret, args.len()));
                            for (i, arg) in args.iter().enumerate() {
                                let idx = self.visit_atom(&Atom::Int(i as i64));
                                let arg = self.visit_atom(arg);
                                self.code.push(Instr::Store(ret, idx, arg));
                            }
                        }
                        _ => unreachable!(),
                    },
                }
                self.reg_map.insert(*bind, ret);
                self.visit_expr(cont);
            }
            Expr::Call {
                bind,
                func,
                args,
                cont,
            } => {
                for arg in args.iter().rev() {
                    let reg = self.visit_atom(arg);
                    self.code.push(Instr::Push(reg));
                }
                match self.lookup_var(&func.unwrap_var()) {
                    Ok(reg) => {
                        self.code.push(Instr::CallInd(reg));
                    }
                    Err(addr) => {
                        self.code.push(Instr::Callu(addr));
                    }
                }
                let ret = self.new_reg();
                self.code.push(Instr::Pop(ret));
                self.reg_map.insert(*bind, ret);
                self.visit_expr(cont);
            }
            Expr::Retn { res } => {
                let reg = self.visit_atom(res);
                self.code.push(Instr::Ret(reg));
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn codegen_test() {
    let s = r#"
decl
    fn f(x) begin
        let a = @iadd(x, 1);
        let b = @iadd(a, 1);
        let c = @iadd(b, 1);
        let y = @iadd(c, 1);
        return y;
    end
    fn main() begin
        let z = f(42);
        return z;
    end
in
    return 42;
end
"#;
    let expr = crate::optimize::parser::parse_expr(s).unwrap();
    println!("{}\n", expr);
    let (decls, expr) = crate::optimize::closure::ClosConv::run(expr);
    for decl in decls.iter() {
        println!("{}\n", decl);
    }
    println!("{}\n", expr);

    let blks = Codegen::run(&decls);
    for blk in blks.iter() {
        println!("{}", blk);
    }
}