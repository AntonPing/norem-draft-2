use std::fs;

use crate::{compile, optimize, syntax, typing};

pub fn compile_file(path: &String) {
    let source = fs::read_to_string(path).expect("failed to read file!");
    let mut modl = syntax::parser::parse_module(&source).expect("failed to parse module!");
    syntax::rename::rename_module(&mut modl).expect("failed in identifier renaming phase!");
    typing::check::check_module(&modl).expect("failed in type checking phase!");

    let modl = optimize::normalize::Normalizer::run(&modl);
    let modl = optimize::optimize::Optimizer::run(modl);
    let mark = optimize::inline::InlineScan::run(&modl);
    let modl = optimize::inline::InlinePerform::run(modl, mark);
    let modl = optimize::optimize::Optimizer::run(modl);
    let modl = optimize::closure::ClosConv::run(modl);
    let modl = optimize::optimize::Optimizer::run(modl);

    let mut modl = compile::codegen::Codegen::run(&modl);
    compile::reg_alloc::RegAlloc::run(&mut modl);
    let (code, map) = compile::linking::Linker::run(&modl);
    let (_, entry) = map.iter().find(|(k, _)| k.as_str() == "main").unwrap();
    let mut evl = compile::evaluate::Evaluator::new(code, *entry);
    unsafe { evl.run() };
}
