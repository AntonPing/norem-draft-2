use crate::compile::instr::{Block, Instr};
use crate::utils::ident::Ident;
use std::collections::HashMap;
pub struct Linker {
    code: Vec<Instr>,
    addr_map: HashMap<Ident, usize>,
}

impl Linker {
    pub fn run(blks: &Vec<Block>) -> (Vec<Instr>, HashMap<Ident, usize>) {
        let mut pass = Linker {
            code: Vec::new(),
            addr_map: HashMap::new(),
        };

        pass.scan_addr(blks);
        pass.replace_addr();
        (pass.code, pass.addr_map)
    }

    fn scan_addr(&mut self, blks: &Vec<Block>) {
        for blk in blks {
            self.addr_map.insert(blk.func, self.code.len());
            self.code.push(Instr::Bump(blk.max_reg));
            for ins in blk.code.iter() {
                match ins {
                    Instr::Label(label) => {
                        assert!(!self.addr_map.contains_key(&label));
                        self.addr_map.insert(*label, self.code.len());
                    }
                    _ => {
                        self.code.push(*ins);
                    }
                }
            }
        }
    }

    fn replace_addr(&mut self) {
        for ins in self.code.iter_mut() {
            match ins {
                Instr::LitAu(reg, addr) => {
                    let addr = self.addr_map.get(addr).unwrap();
                    *ins = Instr::LitA(*reg, *addr);
                }
                Instr::Callu(addr) => {
                    let addr = self.addr_map.get(addr).unwrap();
                    *ins = Instr::Call(*addr);
                }
                _ => {}
            }
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn linking_test() {
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

    let blks = crate::compile::codegen::Codegen::run(&decls);
    for blk in blks.iter() {
        println!("{}", blk);
    }

    let (code, _) = Linker::run(&blks);
    for line in code {
        println!("{:?}", line);
    }
}
