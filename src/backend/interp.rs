use crate::syntax::prim::Compare;
use crate::utils::ident::Ident;
use std::collections::HashMap;

use super::tac::*;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    Addr(Ident),
    Unit,
    Ptr(*mut Value),
}

impl Value {
    fn unwrap_int(&self) -> i64 {
        if let Value::Int(x) = self {
            *x
        } else {
            panic!("failed to unwrap Value::Int!");
        }
    }
    fn unwrap_float(&self) -> f64 {
        if let Value::Float(x) = self {
            *x
        } else {
            panic!("failed to unwrap Value::Float!");
        }
    }
    fn unwrap_bool(&self) -> bool {
        if let Value::Bool(x) = self {
            *x
        } else {
            panic!("failed to unwrap Value::Bool!");
        }
    }
    fn unwrap_char(&self) -> char {
        if let Value::Char(x) = self {
            *x
        } else {
            panic!("failed to unwrap Value::Char!");
        }
    }
    fn unwrap_addr(&self) -> Ident {
        if let Value::Addr(x) = self {
            *x
        } else {
            panic!("failed to unwrap Value::Addr!");
        }
    }
    fn unwrap_ptr(&self) -> *mut Value {
        if let Value::Ptr(x) = self {
            *x
        } else {
            panic!("failed to unwrap Value::Ptr!");
        }
    }
}

fn alloc_memory(size: usize) -> Value {
    let mut vec = Vec::with_capacity(size as usize);
    for _ in 0..size {
        vec.push(Value::Unit);
    }
    let boxed = Box::new(vec);
    let ptr = boxed.leak();
    Value::Ptr(ptr.as_mut_ptr())
}

struct CallSave {
    bind: Ident,
    cont: Ident,
    local: HashMap<Ident, Value>,
}

pub struct Interpreter<'a> {
    // map block names (or function name) to block references
    code_map: HashMap<Ident, &'a BasicBlock>,
    // map function names to function parameters
    pars_map: HashMap<Ident, &'a Vec<Ident>>,
    stack: Vec<CallSave>,
    local: HashMap<Ident, Value>,
}

impl<'a> Interpreter<'a> {
    pub fn new(modl: &'a Module) -> Interpreter {
        let mut code_map = HashMap::new();
        let mut pars_map = HashMap::new();
        for func in modl.funcs.values() {
            for blk in func.blks.iter() {
                code_map.insert(blk.name, blk);
            }
            code_map.insert(func.name, &func.blks[0]);
            pars_map.insert(func.name, &func.pars);
        }
        Interpreter {
            code_map,
            pars_map,
            stack: Vec::new(),
            local: HashMap::new(),
        }
    }
    pub unsafe fn run(&mut self, func: Ident, args: Vec<Value>) -> Value {
        let mut run_blk: &BasicBlock = self.code_map[&func];
        for (par, arg) in self.pars_map[&func].iter().zip(args.iter()) {
            self.local.insert(*par, *arg);
        }
        loop {
            for code in run_blk.codes.iter() {
                match code {
                    Instr::LitI(r, v) => {
                        self.local.insert(*r, Value::Int(*v));
                    }
                    Instr::LitF(r, v) => {
                        self.local.insert(*r, Value::Float(*v));
                    }
                    Instr::LitB(r, v) => {
                        self.local.insert(*r, Value::Bool(*v));
                    }
                    Instr::LitC(r, v) => {
                        self.local.insert(*r, Value::Char(*v));
                    }
                    Instr::LitA(r, v) => {
                        self.local.insert(*r, Value::Addr(*v));
                    }
                    Instr::IAdd(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_int() + self.local[r3].unwrap_int();
                        self.local.insert(*r1, Value::Int(value));
                    }
                    Instr::ISub(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_int() - self.local[r3].unwrap_int();
                        self.local.insert(*r1, Value::Int(value));
                    }
                    Instr::IMul(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_int() * self.local[r3].unwrap_int();
                        self.local.insert(*r1, Value::Int(value));
                    }
                    Instr::IDiv(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_int() / self.local[r3].unwrap_int();
                        self.local.insert(*r1, Value::Int(value));
                    }
                    Instr::IRem(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_int() % self.local[r3].unwrap_int();
                        self.local.insert(*r1, Value::Int(value));
                    }
                    Instr::INeg(r1, r2) => {
                        let value = -self.local[r2].unwrap_int();
                        self.local.insert(*r1, Value::Int(value));
                    }
                    Instr::FAdd(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_float() + self.local[r3].unwrap_float();
                        self.local.insert(*r1, Value::Float(value));
                    }
                    Instr::FSub(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_float() - self.local[r3].unwrap_float();
                        self.local.insert(*r1, Value::Float(value));
                    }
                    Instr::FMul(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_float() * self.local[r3].unwrap_float();
                        self.local.insert(*r1, Value::Float(value));
                    }
                    Instr::FDiv(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_float() / self.local[r3].unwrap_float();
                        self.local.insert(*r1, Value::Float(value));
                    }
                    Instr::FNeg(r1, r2) => {
                        let value = -self.local[r2].unwrap_float();
                        self.local.insert(*r1, Value::Float(value));
                    }
                    Instr::BAnd(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_bool() && self.local[r3].unwrap_bool();
                        self.local.insert(*r1, Value::Bool(value));
                    }
                    Instr::BOr(r1, r2, r3) => {
                        let value = self.local[r2].unwrap_bool() || self.local[r3].unwrap_bool();
                        self.local.insert(*r1, Value::Bool(value));
                    }
                    Instr::BNot(r1, r2) => {
                        let value = !self.local[r2].unwrap_bool();
                        self.local.insert(*r1, Value::Bool(value));
                    }
                    Instr::ICmp(cmp, r1, r2, r3) => {
                        let lhs = self.local[r2].unwrap_int();
                        let rhs = self.local[r3].unwrap_int();
                        let value = match cmp {
                            Compare::Lt => lhs < rhs,
                            Compare::Le => lhs <= rhs,
                            Compare::Eq => lhs == rhs,
                            Compare::Ge => lhs >= rhs,
                            Compare::Gt => lhs > rhs,
                            Compare::Ne => lhs != rhs,
                        };
                        self.local.insert(*r1, Value::Bool(value));
                    }
                    Instr::FCmp(cmp, r1, r2, r3) => {
                        let lhs = self.local[r2].unwrap_float();
                        let rhs = self.local[r3].unwrap_float();
                        let value = match cmp {
                            Compare::Lt => lhs < rhs,
                            Compare::Le => lhs <= rhs,
                            Compare::Eq => lhs == rhs,
                            Compare::Ge => lhs >= rhs,
                            Compare::Gt => lhs > rhs,
                            Compare::Ne => lhs != rhs,
                        };
                        self.local.insert(*r1, Value::Bool(value));
                    }
                    Instr::Move(r1, r2) => {
                        let v = self.local[r2];
                        self.local.insert(*r1, v);
                    }
                    Instr::Alloc(reg1, arg2) => {
                        let len = self.local[arg2].unwrap_int();
                        let ptr = alloc_memory(len as usize);
                        self.local.insert(*reg1, ptr);
                    }
                    Instr::Load(reg, mem, idx) => {
                        let ptr = self.local[mem].unwrap_ptr();
                        let ptr = ptr.add(self.local[idx].unwrap_int() as usize);
                        self.local.insert(*reg, *ptr);
                    }
                    Instr::Store(mem, idx, reg) => {
                        let ptr = self.local[mem].unwrap_ptr();
                        let ptr = ptr.add(self.local[idx].unwrap_int() as usize);
                        *ptr = *self.local.get(reg).unwrap();
                    }
                    Instr::IPrint(r) => {
                        let value = self.local[r].unwrap_int();
                        print!("{}", value);
                    }
                    Instr::IScan(r) => {
                        let mut s = String::new();
                        std::io::stdin().read_line(&mut s).unwrap();
                        self.local
                            .insert(*r, Value::Int(s.trim().parse().unwrap_or(0)));
                    }
                    Instr::FPrint(r) => {
                        let value = self.local[r].unwrap_float();
                        print!("{}", value);
                    }
                    Instr::FScan(r) => {
                        let mut s = String::new();
                        std::io::stdin().read_line(&mut s).unwrap();
                        self.local
                            .insert(*r, Value::Float(s.trim().parse().unwrap_or(0.0)));
                    }
                    Instr::CPrint(r) => {
                        let value = self.local[r].unwrap_char();
                        print!("{}", value);
                    }
                    Instr::CScan(r) => {
                        let mut s = String::new();
                        std::io::stdin().read_line(&mut s).unwrap();
                        self.local
                            .insert(*r, Value::Char(s.trim().parse().unwrap_or('0')));
                    }
                    Instr::Assert(r) => {
                        let value = self.local[r].unwrap_bool();
                        if !value {
                            panic!("assert failed!");
                        }
                    }
                }
            }
            match run_blk.last.as_ref().unwrap() {
                LastInstr::TailCall(func, args) => {
                    let func = self.local[&func].unwrap_addr();
                    let pars = self.pars_map[&func];
                    let args: Vec<_> = args.iter().map(|arg| self.local[arg]).collect();
                    assert_eq!(pars.len(), args.len());
                    let mut temp = HashMap::new();
                    for (par, arg) in pars.iter().zip(args.iter()) {
                        temp.insert(*par, *arg);
                    }
                    // jump to new function with new local variables
                    self.local = temp;
                    run_blk = self.code_map[&func];
                }
                LastInstr::Call(bind, func, cont, args) => {
                    let func = self.local[&func].unwrap_addr();
                    // introduce function parameters
                    let pars = self.pars_map[&func];
                    let args: Vec<_> = args.iter().map(|arg| self.local[arg]).collect();
                    assert_eq!(pars.len(), args.len());
                    let mut temp = HashMap::new();
                    for (par, arg) in pars.iter().zip(args.iter()) {
                        temp.insert(*par, *arg);
                    }
                    // push current local variables and call function
                    std::mem::swap(&mut self.local, &mut temp);
                    self.stack.push(CallSave {
                        bind: *bind,
                        cont: *cont,
                        local: temp,
                    });
                    run_blk = self.code_map[&func];
                }
                LastInstr::Return(ret) => {
                    if let Some(save) = self.stack.pop() {
                        let CallSave { bind, cont, local } = save;
                        let ret = self.local[ret];
                        self.local = local;
                        self.local.insert(bind, ret);
                        run_blk = self.code_map[&cont];
                    } else {
                        return self.local[ret];
                    }
                }
                LastInstr::Jump(cont) => {
                    run_blk = self.code_map[&cont];
                }
                LastInstr::BrIf(cond, trbr, flbr) => {
                    if let Value::Bool(cond) = self.local[cond] {
                        if cond {
                            run_blk = self.code_map[trbr];
                        } else {
                            run_blk = self.code_map[flbr];
                        }
                    } else {
                        panic!("non-boolean value for if-then-else!");
                    }
                }
            }
        }
    }
}
