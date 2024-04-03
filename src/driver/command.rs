use crate::analyze::diagnostic::Diagnostic;
use crate::backend::tac;
use crate::{analyze, backend, core, syntax};
use std::{fs, io, path, vec};

#[derive(Clone, Debug)]
pub enum Backend {
    Interp,
    C,
}

#[derive(Clone, Debug)]
pub struct CompilerFlag {
    pub debug_mode: bool,
    pub verbose: u8,
    pub input: Box<path::Path>,
    pub output: Option<Box<path::Path>>,
    pub backend: Backend,
}

#[derive(Debug)]
pub enum CompileError {
    SyntaxError,
    ScopeError,
    SemanticError,
    IOError(std::io::Error),
}

impl From<io::Error> for CompileError {
    fn from(value: std::io::Error) -> Self {
        CompileError::IOError(value)
    }
}

pub fn compile_file<T>(
    path: &path::Path,
    flag: &CompilerFlag,
    cout: &mut T,
) -> Result<(), CompileError>
where
    T: io::Write,
{
    let src = fs::read_to_string(&path)?;
    let mut diags: Vec<Diagnostic> = Vec::new();
    let res = compile_with(&src, flag, &mut diags);
    for diag in diags.iter() {
        writeln!(cout, "{}", diag.report(&src, flag.verbose))?;
        println!("{}", diag.report(&src, flag.verbose));
    }
    let modl = res?;
    match flag.backend {
        Backend::Interp => {
            let entry = modl
                .funcs
                .iter()
                .map(|(name, _)| name)
                .find(|name| name.as_str() == "main")
                .unwrap();
            let mut eval = backend::interp::Interpreter::new(&modl);
            let res = unsafe { eval.run(*entry, vec![backend::interp::Value::Unit]) };
            writeln!(cout, "{res:?}")?;
            println!("{res:?}");
            Ok(())
        }
        Backend::C => {
            let s = backend::codegen_c::Codegen::run(&modl);
            let out = flag
                .output
                .clone()
                .unwrap_or_else(|| flag.input.clone().with_extension("c").into());
            fs::write(out, s)?;
            Ok(())
        }
    }
}

pub fn compile_with<'src>(
    src: &'src str,
    flag: &CompilerFlag,
    diags: &mut Vec<Diagnostic>,
) -> Result<tac::Module, CompileError> {
    let mut modl = syntax::parser::parse_module(&src, diags).ok_or(CompileError::SyntaxError)?;
    if flag.debug_mode {
        println!("parser:\n{modl:#?}");
    }
    syntax::rename::rename_module(&mut modl, diags).map_err(|_| CompileError::ScopeError)?;
    analyze::check::check_module(&mut modl, diags).map_err(|_| CompileError::SemanticError)?;

    let modl = core::cps_trans::Translator::run(&modl);
    if flag.debug_mode {
        println!("cps_trans:\n{modl}");
    }
    let modl = core::optimize::Optimizer::run(modl);
    if flag.debug_mode {
        println!("optimize:\n{modl}");
    }
    let mark = core::inline::InlineScan::run(&modl);
    let modl = core::inline::InlinePerform::run(modl, mark);
    if flag.debug_mode {
        println!("inline:\n{modl}");
    }
    let modl = core::optimize::Optimizer::run(modl);
    if flag.debug_mode {
        println!("optimize:\n{modl}");
    }
    let modl = core::closure::ClosConv::run(modl);
    if flag.debug_mode {
        println!("clos_conv:\n{modl}");
    }
    let modl = core::optimize::Optimizer::run(modl);
    if flag.debug_mode {
        println!("optimize:\n{modl}");
    }
    let modl = backend::lowering::Lowering::run(&modl);
    if flag.debug_mode {
        println!("lowering:\n{modl}");
    }
    Ok(modl)
}
