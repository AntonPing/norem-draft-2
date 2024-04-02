use super::tac::*;
use crate::syntax::prim::Compare;
use crate::utils::ident::Ident;
use core::fmt;
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Write;
use std::iter;

pub struct CodegenMap {
    var_id: usize,
    blk_map: HashMap<Ident, usize>,
    var_map: HashMap<Ident, usize>,
    var_count: HashMap<Ident, usize>,
}

impl CodegenMap {
    fn new() -> CodegenMap {
        CodegenMap {
            var_id: 0,
            blk_map: HashMap::new(),
            var_map: HashMap::new(),
            var_count: HashMap::new(),
        }
    }

    fn visit_var(&mut self, var: &Ident) {
        if !self.var_map.contains_key(var) {
            let id = self.var_id;
            self.var_map.insert(*var, id);
            self.var_id += 1;
        }
    }

    fn visit_module(&mut self, modl: &Module) {
        for (_name, func) in modl.funcs.iter() {
            self.visit_function(func);
        }
    }

    fn visit_function(&mut self, func: &Function) {
        for (i, blk) in func.blks.iter().enumerate() {
            self.blk_map.insert(blk.name, i);
        }
        self.var_id = 0;
        for par in func.pars.iter() {
            self.visit_var(par);
        }
        for blk in func.blks.iter() {
            self.visit_block(blk);
        }
        self.var_count.insert(func.name, self.var_id + 1);
    }

    fn visit_block(&mut self, blk: &BasicBlock) {
        self.visit_last_instr(blk.last.as_ref().unwrap());
        for code in blk.codes.iter() {
            self.visit_instr(&code);
        }
    }

    fn visit_instr(&mut self, code: &Instr) {
        match code {
            Instr::LitI(r, _)
            | Instr::LitF(r, _)
            | Instr::LitC(r, _)
            | Instr::LitA(r, _)
            | Instr::Alloc(r, _)
            | Instr::IPrint(r)
            | Instr::IScan(r)
            | Instr::FPrint(r)
            | Instr::FScan(r)
            | Instr::CPrint(r)
            | Instr::CScan(r) => {
                self.visit_var(r);
            }
            Instr::BNot(r1, r2) | Instr::Move(r1, r2) => {
                self.visit_var(r1);
                self.visit_var(r2);
            }
            Instr::Load(r1, r2, r3)
            | Instr::Store(r1, r2, r3)
            | Instr::ICmp(_, r1, r2, r3)
            | Instr::FCmp(_, r1, r2, r3)
            | Instr::IAdd(r1, r2, r3)
            | Instr::ISub(r1, r2, r3)
            | Instr::IMul(r1, r2, r3)
            | Instr::IDiv(r1, r2, r3)
            | Instr::IRem(r1, r2, r3)
            | Instr::FAdd(r1, r2, r3)
            | Instr::FSub(r1, r2, r3)
            | Instr::FMul(r1, r2, r3)
            | Instr::FDiv(r1, r2, r3)
            | Instr::BAnd(r1, r2, r3)
            | Instr::BOr(r1, r2, r3) => {
                self.visit_var(r1);
                self.visit_var(r2);
                self.visit_var(r3);
            }
        }
    }

    fn visit_last_instr(&mut self, last: &LastInstr) {
        match last {
            LastInstr::TailCall(_, args) => {
                for arg in args {
                    self.visit_var(arg);
                }
            }
            LastInstr::Call(bind, _, _, args) => {
                self.visit_var(bind);
                for arg in args {
                    self.visit_var(arg);
                }
            }
            LastInstr::Return(r) => {
                self.visit_var(r);
            }
            LastInstr::Jump(_) => {}
            LastInstr::BrIf(cond, _, _) => self.visit_var(cond),
        }
    }
}

pub struct Codegen {
    text: String,
    map: CodegenMap,
}

impl Codegen {
    pub fn new() -> Codegen {
        Codegen {
            text: String::new(),
            map: CodegenMap::new(),
        }
    }

    pub fn run(modl: &Module) -> String {
        let mut pass = Codegen::new();
        pass.visit_module(modl).unwrap();
        pass.text
    }

    pub fn visit_module(&mut self, modl: &Module) -> fmt::Result {
        // initialize variable mapping
        self.map.visit_module(modl);
        // for each function generator c code
        for (_name, func) in modl.funcs.iter() {
            self.visit_function(func)?;
        }
        Ok(())
    }

    pub fn visit_function(&mut self, func: &Function) -> fmt::Result {
        // print function signature
        let pars = func
            .pars
            .iter()
            .map(|par| format!("value_t r{}", self.map.var_map[par]))
            .format(&", ")
            .to_string();
        let func_name = func.name.as_str();
        write!(self.text, "value_t {func_name}({pars}) {{\n")?;

        // declare local variables
        let count: usize = self.map.var_count[&func.name];
        let mut i: usize = func.pars.len();
        loop {
            if i >= count {
                break;
            } else {
                let len = std::cmp::min(10, count - i);
                write!(self.text, "    value_t ")?;
                for j in i..(i + len) {
                    if j == i {
                        write!(self.text, "r{j}")?;
                    } else {
                        write!(self.text, ", r{j}")?;
                    }
                }
                write!(self.text, ";\n")?;
                i += len;
            }
        }

        // print function blocks
        let names: Vec<_> = func
            .blks
            .iter()
            .map(|blk| Some(blk.name))
            .chain([None].into_iter())
            .collect();
        for (blk, next_blk) in func.blks.iter().zip(names.iter().skip(1)) {
            self.visit_block(blk, *next_blk)?;
        }
        write!(self.text, "}}\n")
    }

    fn visit_block(&mut self, blk: &BasicBlock, next_blk: Option<Ident>) -> fmt::Result {
        let label = self.map.blk_map[&blk.name];
        write!(self.text, "label_{label}:\n")?;
        for code in blk.codes.iter() {
            self.visit_instr(&code)?;
        }
        self.visit_last_instr(blk.last.as_ref().unwrap(), next_blk)?;
        Ok(())
    }

    fn visit_instr(&mut self, code: &Instr) -> fmt::Result {
        match code {
            Instr::LitI(r, v) => {
                let r = self.map.var_map[r];
                write!(self.text, "    r{r}.i = {v}\n")
            }
            Instr::LitF(r, v) => {
                let r = self.map.var_map[r];
                write!(self.text, "    r{r}.f = {v}\n")
            }
            Instr::LitC(r, v) => {
                let r = self.map.var_map[r];
                write!(self.text, "    r{r}.c = {v}\n")
            }
            Instr::LitA(r, v) => {
                let r = self.map.var_map[r];
                let v = v.as_str();
                write!(self.text, "    r{r}.p = {v}\n")
            }
            Instr::IAdd(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.i + r{r3}.i;\n")
            }
            Instr::ISub(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.i - r{r3}.i;\n")
            }
            Instr::IMul(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.i * r{r3}.i;\n")
            }
            Instr::IDiv(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.i / r{r3}.i;\n")
            }
            Instr::IRem(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.i % r{r3}.i;\n")
            }
            Instr::FAdd(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.f + r{r3}.f;\n")
            }
            Instr::FSub(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.f - r{r3}.f;\n")
            }
            Instr::FMul(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.f * r{r3}.f;\n")
            }
            Instr::FDiv(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.f / r{r3}.f;\n")
            }
            Instr::BAnd(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.b && r{r3}.b;\n")
            }
            Instr::BOr(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.i = r{r2}.b || r{r3}.b;\n")
            }
            Instr::BNot(r1, r2) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                write!(self.text, "    r{r1}.i = !r{r2}.b;\n")
            }
            Instr::ICmp(cmp, r1, r2, r3) => {
                let cmp = match cmp {
                    Compare::Lt => "<",
                    Compare::Le => "<=",
                    Compare::Eq => "==",
                    Compare::Ge => ">=",
                    Compare::Gt => ">",
                    Compare::Ne => "!=",
                };
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.b = r{r2}.i {cmp} r{r3}.i;\n")
            }
            Instr::FCmp(cmp, r1, r2, r3) => {
                let cmp = match cmp {
                    Compare::Lt => "<",
                    Compare::Le => "<=",
                    Compare::Eq => "==",
                    Compare::Ge => ">=",
                    Compare::Gt => ">",
                    Compare::Ne => "!=",
                };
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1}.b = r{r2}.f {cmp} r{r3}.f;\n")
            }
            Instr::Move(r1, r2) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                write!(self.text, "    r{r1} = r{r2}\n")
            }
            Instr::Alloc(r1, r2) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                write!(
                    self.text,
                    "    r{r1}.p = malloc(r{r2}.i * sizeof(value_t))\n"
                )
            }
            Instr::Load(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    r{r1} = ((value_t*)r{r2}.p)[r{r3}.i];\n")
            }
            Instr::Store(r1, r2, r3) => {
                let r1 = self.map.var_map[r1];
                let r2 = self.map.var_map[r2];
                let r3 = self.map.var_map[r3];
                write!(self.text, "    ((value_t*)r{r1}.p)[r{r2}.i] = r{r3};\n")
            }
            Instr::IPrint(r) => {
                let r = self.map.var_map[r];
                write!(self.text, "    printf(\"\\%ld\n\", r{r}.i);\n")
            }
            Instr::IScan(r) => {
                let r = self.map.var_map[r];
                write!(self.text, "    scanf(\"\\%ld\n\", &r{r}.i);\n")
            }
            Instr::FPrint(r) => {
                let r = self.map.var_map[r];
                write!(self.text, "    printf(\"\\%lf\n\", r{r}.f);\n")
            }
            Instr::FScan(r) => {
                let r = self.map.var_map[r];
                write!(self.text, "    scanf(\"\\%lf\n\", &r{r}.f);\n")
            }
            Instr::CPrint(r) => {
                let r = self.map.var_map[r];
                write!(self.text, "    printf(\"\\%c\n\", r{r}.c);\n")
            }
            Instr::CScan(r) => {
                let r = self.map.var_map[r];
                write!(self.text, "    scanf(\"\\%c\n\", &r{r}.c);\n")
            }
        }
    }

    fn visit_last_instr(&mut self, last: &LastInstr, next_blk: Option<Ident>) -> fmt::Result {
        match last {
            LastInstr::TailCall(func, args) => {
                let func = if self.map.var_map.contains_key(&func) {
                    let i = self.map.var_map[func];
                    let args_typ = iter::repeat("value_t").take(args.len()).format(&", ");
                    format!("(value_t(*)({args_typ}) r{i}.f)")
                } else {
                    func.to_string()
                };
                let args = args
                    .iter()
                    .map(|arg| format!("r{}", self.map.var_map[arg]))
                    .format(&", ")
                    .to_string();
                write!(self.text, "    return {func}({args});\n")
            }
            LastInstr::Call(bind, func, cont, args) => {
                let bind = self.map.var_map[bind];
                let func = if self.map.var_map.contains_key(&func) {
                    let func = self.map.var_map[func];
                    let args_typ = iter::repeat("value_t").take(args.len()).format(&", ");
                    format!("(value_t(*)({args_typ}) r{func}.p)")
                } else {
                    func.to_string()
                };
                let args = args
                    .iter()
                    .map(|arg| format!("r{}", self.map.var_map[arg]))
                    .format(&", ")
                    .to_string();
                write!(self.text, "    r{bind} = {func}({args});\n")?;
                if next_blk == Some(*cont) {
                    Ok(())
                } else {
                    let label = self.map.blk_map[cont];
                    write!(self.text, "    goto label_{label};\n")
                }
            }
            LastInstr::Return(arg) => {
                let arg = self.map.var_map[arg];
                write!(self.text, "    return r{arg};\n")
            }
            LastInstr::Jump(cont) => {
                let cont = self.map.blk_map[cont];
                write!(self.text, "    goto label_{cont};\n")
            }
            LastInstr::BrIf(cond, trbr, flbr) => {
                let cond = self.map.var_map[cond];
                if next_blk == Some(*trbr) {
                    let flbr = self.map.blk_map[flbr];
                    write!(self.text, "    if !r{cond}.b {{ goto label_{flbr}; }}\n")
                } else if next_blk == Some(*flbr) {
                    let trbr = self.map.blk_map[trbr];
                    write!(self.text, "    if r{cond}.b {{ goto label_{trbr}; }}\n")
                } else {
                    let flbr = self.map.blk_map[flbr];
                    let trbr = self.map.blk_map[trbr];
                    write!(
                        self.text,
                        "    if r{cond}.b {{ goto label_{trbr}; }} else {{ goto label_{flbr}; }}\n"
                    )
                }
            }
        }
    }
}

pub static C_PROLOGUE: &'static str = r#"
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

typedef union value_t {
    int64_t i;
    double f;
    bool b;
    char c;
    void* p;
} value_t;
"#;

pub static C_EPILOGUE: &'static str = r#"/*
    this file is generated by norem compiler,
    reading and editing are not recommanded.
*/
"#;

pub static C_SYS_CHECK: &'static str = r#"if(sizeof(void*) != 8)
{
puts("check failed: 'void*' is not 64-bits!");
exit(1);
}
if(sizeof(int64_t) != 8)
{
puts("check failed: 'int64_t' is not 64-bits!");
exit(1);
}
if(sizeof(double) != 8)
{
puts("check failed: 'double' is not 64-bits!");
exit(1);
}
"#;

#[test]
#[ignore = "just to see result"]
fn codegen_test() {
    let s = r#"
module Pattern where
datatype List[T] where
| Nil
| Cons(T, List[T])
end
function length[T](xs: List[T]) -> Int
begin
    match xs with
    | Nil => 0
    | Cons(x, xs) => @iadd(length(xs), 1)
    end
end
function main() -> Int
begin
    length(Cons(1, Cons(2, Cons(3, Nil))))
end
"#;
    let mut diags = Vec::new();
    let modl = crate::syntax::parser::parse_module(s, &mut diags).unwrap();
    println!("{:#?}\n", modl);
    let modl = crate::core::cps_trans::Translator::run(&modl);
    println!("{}\n", modl);
    let modl = crate::core::optimize::Optimizer::run(modl);
    let mark = crate::core::inline::InlineScan::run(&modl);
    let modl = crate::core::inline::InlinePerform::run(modl, mark);
    let modl = crate::core::optimize::Optimizer::run(modl);
    let modl = crate::core::closure::ClosConv::run(modl);
    let modl = crate::core::optimize::Optimizer::run(modl);
    let modl = super::lowering::Lowering::run(&modl);
    println!("{:#?}\n", modl);
    let res = super::codegen_c::Codegen::run(&modl);
    println!("{res}");
}
