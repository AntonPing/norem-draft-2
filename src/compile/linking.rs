use crate::compile::instr::{Block, Instr};
use crate::utils::ident::Ident;
use std::collections::HashMap;

use super::instr::Module;
pub struct Linker {
    code_before: Vec<Instr<Ident>>,
    code_after: Vec<Instr<usize>>,
    addr_map: HashMap<Ident, usize>,
}

impl Linker {
    pub fn run(modl: &Module) -> (Vec<Instr<usize>>, HashMap<Ident, usize>) {
        let mut pass = Linker {
            code_before: Vec::new(),
            code_after: Vec::new(),
            addr_map: HashMap::new(),
        };
        for (_, blk) in modl.blks.iter() {
            pass.scan_addr(blk);
        }
        pass.replace_addr();
        (pass.code_after, pass.addr_map)
    }

    fn scan_addr(&mut self, blk: &Block) {
        self.addr_map.insert(blk.func, self.code_before.len());
        self.code_before.push(Instr::Bump(blk.max_reg));
        for ins in blk.code.iter() {
            match *ins {
                Instr::Label(label) => {
                    assert!(!self.addr_map.contains_key(&label));
                    self.addr_map.insert(label, self.code_before.len());
                }
                _ => {
                    self.code_before.push(*ins);
                }
            }
        }
    }

    fn replace_addr(&mut self) {
        for ins in self.code_before.iter() {
            let ins2 = match *ins {
                Instr::Label(_) => unreachable!(),
                Instr::LitI(reg, val) => Instr::LitI(reg, val),
                Instr::LitF(reg, val) => Instr::LitF(reg, val),
                Instr::LitC(reg, val) => Instr::LitC(reg, val),
                Instr::LitA(reg, addr) => Instr::LitA(reg, self.addr_map[&addr]),
                Instr::Move(reg1, reg2) => Instr::Move(reg1, reg2),
                Instr::Bump(len) => Instr::Bump(len),
                Instr::Alloc(reg, len) => Instr::Alloc(reg, len),
                Instr::Load(reg1, reg2, reg3) => Instr::Load(reg1, reg2, reg3),
                Instr::Store(reg1, reg2, reg3) => Instr::Store(reg1, reg2, reg3),
                Instr::ICmpGr(reg1, reg2, reg3) => Instr::ICmpGr(reg1, reg2, reg3),
                Instr::ICmpEq(reg1, reg2, reg3) => Instr::ICmpEq(reg1, reg2, reg3),
                Instr::ICmpLs(reg1, reg2, reg3) => Instr::ICmpLs(reg1, reg2, reg3),
                Instr::IAdd(reg1, reg2, reg3) => Instr::IAdd(reg1, reg2, reg3),
                Instr::ISub(reg1, reg2, reg3) => Instr::ISub(reg1, reg2, reg3),
                Instr::IMul(reg1, reg2, reg3) => Instr::IMul(reg1, reg2, reg3),
                Instr::Push(reg) => Instr::Push(reg),
                Instr::Pop(reg) => Instr::Pop(reg),
                Instr::JmpTr(reg, addr) => Instr::JmpTr(reg, self.addr_map[&addr]),
                Instr::JmpFl(reg, addr) => Instr::JmpFl(reg, self.addr_map[&addr]),
                Instr::Jmp(addr) => Instr::Jmp(self.addr_map[&addr]),
                Instr::Call(addr) => Instr::Call(self.addr_map[&addr]),
                Instr::CallInd(reg) => Instr::CallInd(reg),
                Instr::Ret(reg) => Instr::Ret(reg),
                Instr::Nop => Instr::Nop,
            };
            self.code_after.push(ins2);
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn linking_test() {
    let s = r#"
module test where
func f(k, x):
    let y = @iadd(x, 1);
    jump k(y);

func main(top):
    decls
        cont k(x):
            return x;
    in
        call f(k, 42);
    end
"#;
    let modl = crate::core::parser::parse_module(s).unwrap();
    println!("{}\n", modl);
    let modl = crate::compile::codegen::Codegen::run(&modl);
    println!("{}\n", modl);
    let (code, _) = Linker::run(&modl);
    for line in code {
        println!("{:?}", line);
    }
}
