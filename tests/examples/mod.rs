use std::io::{Read, Seek};
use std::path;

use norem_lang::driver::command;
pub fn test_file<S: AsRef<path::Path>>(module: S) -> String {
    let mut input = path::PathBuf::new();
    input.push("examples");
    input.push(module);
    input.set_extension("nr");
    let flag = command::CompilerFlag {
        debug_mode: false,
        verbosity: 10,
        backend: command::Backend::Interp,
    };
    let mut cout = tempfile::tempfile().unwrap();
    let _ = command::compile_file(&input, &flag, &mut cout);
    cout.rewind().unwrap();
    let mut actual = String::new();
    cout.read_to_string(&mut actual).unwrap();
    actual
}
