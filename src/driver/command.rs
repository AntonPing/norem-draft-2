use crate::analyze::diagnostic::Diagnostic;
use crate::core::cps;
use crate::{analyze, backend_new, core, syntax};
use std::path::PathBuf;
use std::{fs, io, vec};

#[derive(Clone, Debug)]
pub enum Backend {
    Interp,
}

#[derive(Clone, Debug)]
pub struct CompilerFlag {
    pub debug_mode: bool,
    pub verbosity: u8,
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
    path: &PathBuf,
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
        writeln!(cout, "{}", diag.report(&src, flag.verbosity))?;
    }
    let modl = res?;
    match flag.backend {
        Backend::Interp => {
            let modl = backend_new::lowering::Lowering::run(&modl);
            println!("{modl:#?}");
            let entry = modl
                .funcs
                .iter()
                .map(|(name, _)| name)
                .find(|name| name.as_str() == "main")
                .unwrap();
            let mut eval = backend_new::interp::Interpreter::new(&modl);
            let res = unsafe { eval.run(*entry, vec![backend_new::interp::Value::Unit]) };
            writeln!(cout, "{res:?}")?;
            Ok(())
        }
    }
}

pub fn compile_with<'src>(
    src: &'src str,
    flag: &CompilerFlag,
    diags: &mut Vec<Diagnostic>,
) -> Result<cps::Module, CompileError> {
    let mut modl = syntax::parser::parse_module(&src, diags).ok_or(CompileError::SyntaxError)?;
    if flag.debug_mode {
        println!("parser:\n{modl:#?}");
    }
    syntax::rename::rename_module(&mut modl, diags).map_err(|_| CompileError::ScopeError)?;
    analyze::check::check_module(&modl, diags).map_err(|_| CompileError::SemanticError)?;

    let modl = core::cps_trans::Translator::run(&modl);
    if flag.debug_mode {
        println!("cps_trans:\n{modl}");
    }
    let modl = core::optimize::Optimizer::run(modl);
    if flag.debug_mode {
        println!("optimizer:\n{modl}");
    }
    let mark = core::inline::InlineScan::run(&modl);
    let modl = core::inline::InlinePerform::run(modl, mark);
    if flag.debug_mode {
        println!("inline:\n{modl}");
    }
    let modl = core::optimize::Optimizer::run(modl);
    if flag.debug_mode {
        println!("optimizer:\n{modl}");
    }
    let modl = core::closure::ClosConv::run(modl);
    if flag.debug_mode {
        println!("clos_conv:\n{modl}");
    }
    let modl = core::optimize::Optimizer::run(modl);
    if flag.debug_mode {
        println!("optimizer:\n{modl}");
    }
    Ok(modl)
}
