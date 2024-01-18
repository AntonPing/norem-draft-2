use crate::compile::instr::{Block, Instr};
use crate::utils::ident::Ident;
use std::collections::HashMap;

use super::instr::Module;
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
        for blk in blks.iter() {
            pass.scan_addr(blk);
        }
        pass.replace_addr();
        (pass.code, pass.addr_map)
    }

    pub fn run_module(modl: &Module) -> (Vec<Instr>, HashMap<Ident, usize>) {
        let mut pass = Linker {
            code: Vec::new(),
            addr_map: HashMap::new(),
        };
        for (_, blk) in modl.blks.iter() {
            pass.scan_addr(blk);
        }
        pass.replace_addr();
        (pass.code, pass.addr_map)
    }

    fn scan_addr(&mut self, blk: &Block) {
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
module test where
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
"#;
    let modl = crate::optimize::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let modl = crate::compile::codegen::Codegen::run_module(&modl);
    println!("{}\n", modl);
    let (code, _) = Linker::run_module(&modl);
    for line in code {
        println!("{:?}", line);
    }
}
