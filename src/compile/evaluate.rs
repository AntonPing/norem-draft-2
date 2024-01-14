use super::instr::{Instr, Reg};

#[derive(Copy, Clone, Debug)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Char(char),
    Unit,
    Addr(usize),
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

    fn unwrap_addr(&self) -> usize {
        if let Value::Addr(x) = self {
            *x
        } else {
            panic!("failed to unwrap Value::Ptr!");
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

pub struct Runner {
    code: Vec<Instr>,
    code_ptr: usize,
    base_ptr: usize,
    stack: Vec<Value>,
    locals: Vec<Value>,
    // save code_ptr and base_ptr for each call
    frames: Vec<(usize, usize)>,
}

impl std::fmt::Display for Runner {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "-----code-----\n")?;
        for i in self.code_ptr..self.code_ptr + 5 {
            if i >= self.code.len() {
                break;
            } else {
                write!(f, "{i}:\t{:?}\n", self.code[i])?;
            }
        }
        write!(
            f,
            "code_ptr={}, base_ptr={}\n",
            self.code_ptr, self.base_ptr
        )?;
        write!(f, "-----stack-----\n")?;
        for val in self.stack.iter() {
            write!(f, "{:?}\n", val)?;
        }
        write!(f, "-----locals-----\n")?;
        for i in self.base_ptr..self.locals.len() {
            write!(f, "{} {:?}\n", i - self.base_ptr, self.locals[i])?;
        }
        write!(f, "-----frames-----\n")?;
        for (code_ptr, base_ptr) in self.frames.iter() {
            write!(f, "code_ptr={}, base_ptr={}\n", code_ptr, base_ptr)?;
        }
        write!(f, "---------------\n")?;
        Ok(())
    }
}

impl Runner {
    pub fn new(code: Vec<Instr>, code_ptr: usize) -> Runner {
        Runner {
            code,
            code_ptr,
            base_ptr: 0,
            stack: vec![Value::Unit],
            locals: Vec::new(),
            frames: Vec::new(),
        }
    }
    fn local(&self, reg: Reg) -> &Value {
        &self.locals[self.base_ptr + reg.as_usize()]
    }

    fn local_mut(&mut self, reg: Reg) -> &mut Value {
        &mut self.locals[self.base_ptr + reg.as_usize()]
    }

    pub unsafe fn run(&mut self) {
        loop {
            println!("{}", self);
            match self.code[self.code_ptr] {
                Instr::LitI(reg, val) => {
                    *self.local_mut(reg) = Value::Int(val as i64);
                }
                Instr::LitF(reg, val) => {
                    *self.local_mut(reg) = Value::Float(val as f64);
                }
                Instr::LitC(reg, val) => {
                    *self.local_mut(reg) = Value::Char(val);
                }
                Instr::LitA(reg, val) => {
                    *self.local_mut(reg) = Value::Addr(val);
                }
                Instr::Bump(len) => {
                    self.locals.reserve(len as usize);
                    for _ in 0..len {
                        self.locals.push(Value::Unit);
                    }
                }
                Instr::Move(r1, r2) => {
                    *self.local_mut(r1) = *self.local(r2);
                }
                Instr::Alloc(reg, len) => {
                    let vec = alloc_memory(len as usize);
                    *self.local_mut(reg) = vec;
                }
                Instr::Load(reg, mem, idx) => {
                    let ptr = self.local(mem).unwrap_ptr();
                    let ptr = ptr.add(self.local(idx).unwrap_int() as usize);
                    *self.local_mut(reg) = *ptr;
                }
                Instr::Store(mem, idx, reg) => {
                    let ptr = self.local(mem).unwrap_ptr();
                    let ptr = ptr.add(self.local(idx).unwrap_int() as usize);
                    *ptr = *self.local_mut(reg);
                }
                Instr::IAdd(r1, r2, r3) => {
                    let value = self.local(r2).unwrap_int() + self.local(r3).unwrap_int();
                    *self.local_mut(r1) = Value::Int(value);
                }
                Instr::ISub(r1, r2, r3) => {
                    let value = self.local(r2).unwrap_int() - self.local(r3).unwrap_int();
                    *self.local_mut(r1) = Value::Int(value);
                }
                Instr::IMul(r1, r2, r3) => {
                    let value = self.local(r2).unwrap_int() * self.local(r3).unwrap_int();
                    *self.local_mut(r1) = Value::Int(value);
                }
                Instr::Push(reg) => {
                    self.stack.push(*self.local(reg));
                }
                Instr::Pop(reg) => {
                    *self.local_mut(reg) = self.stack.pop().unwrap();
                }
                Instr::Call(addr) => {
                    self.frames.push((self.code_ptr, self.base_ptr));
                    self.code_ptr = addr;
                    self.base_ptr = self.locals.len();
                    continue;
                }
                Instr::CallInd(reg) => {
                    let addr = self.local(reg).unwrap_addr();
                    self.frames.push((self.code_ptr, self.base_ptr));
                    self.code_ptr = addr;
                    self.base_ptr = self.locals.len();
                    continue;
                }
                Instr::Ret(reg) => {
                    self.stack.push(*self.local(reg));
                    for _ in 0..(self.locals.len() - self.base_ptr) {
                        self.locals.pop();
                    }
                    if let Some((code, base)) = self.frames.pop() {
                        self.code_ptr = code;
                        self.base_ptr = base;
                    } else {
                        break;
                    }
                }
                Instr::Label(_) | Instr::LitAu(_, _) | Instr::Callu(_) => {
                    panic!("can't evaluate an unlinked instruction!")
                }
                Instr::Nop => {}
            }
            self.code_ptr += 1;
        }
    }
}

#[test]
#[ignore = "just to see result"]
fn execute_test() {
    let s = r#"
decl
    fn f(x) begin
        let y = @iadd(x, 1);
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

    let mut blks = crate::compile::codegen::Codegen::run(&decls);
    for blk in blks.iter() {
        println!("{}", blk);
    }

    blks.iter_mut()
        .for_each(|blk| super::reg_alloc::RegAlloc::run(blk));
    for blk in blks.iter() {
        println!("{}", blk);
    }

    let (code, map) = super::linking::Linker::run(&blks);
    for (i, line) in code.iter().enumerate() {
        println!("{i}:\t{:?}", line);
    }

    let (_, entry) = map.iter().find(|(k, _)| k.as_str() == "main").unwrap();
    let mut rnr = Runner::new(code, *entry);
    unsafe {
        rnr.run();
    }
    println!("{}", rnr);
}
