use std::fs;

use crate::backend::evaluate::Value;
use crate::{analyze, backend, core, syntax};

pub fn compile_file(path: &String) -> Value {
    let src = fs::read_to_string(path).expect("failed to read file!");
    let mut diags = Vec::new();
    let mut modl = syntax::parser::parse_module(&src, &mut diags).expect("failed to parse module!");
    syntax::rename::rename_module(&mut modl, &mut diags)
        .expect("failed in identifier renaming phase!");
    analyze::check::check_module(&modl, &mut diags).expect("failed in type checking phase!");

    let modl = core::cps_trans::Translator::run(&modl);
    let modl = core::optimize::Optimizer::run(modl);
    let mark = core::inline::InlineScan::run(&modl);
    let modl = core::inline::InlinePerform::run(modl, mark);
    let modl = core::optimize::Optimizer::run(modl);
    let modl = core::closure::ClosConv::run(modl);
    let modl = core::optimize::Optimizer::run(modl);

    let modl = backend::codegen::Codegen::run(&modl);
    // compile::reg_alloc::RegAlloc::run(&mut modl);
    let (code, map) = backend::linking::Linker::run(&modl);
    let (_, entry) = map.iter().find(|(k, _)| k.as_str() == "main").unwrap();
    let mut evl = backend::evaluate::Evaluator::new(code, *entry);
    let val = unsafe { evl.run() };
    val
}
