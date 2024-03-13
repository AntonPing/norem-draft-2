use clap::{command, Arg, ArgAction};
use std::path;

use crate::driver::command::{Backend, CompilerFlag};

pub fn run_cli() {
    let matches = command!()
        .arg(Arg::new("input").required(true))
        // .arg(Arg::new("compile").short('c').long("compile"))
        .arg(Arg::new("output").short('o').long("output"))
        .arg(
            Arg::new("verbose")
                .short('v')
                .long("verbose")
                .default_value("10"),
        )
        .arg(
            Arg::new("debug")
                .short('d')
                .long("debug")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("backend")
                .short('b')
                .long("backend")
                .default_value("c"),
        )
        .get_matches();

    let input = matches.get_one::<String>("input").unwrap();
    let output = matches.get_one::<String>("output");
    // let compile = matches.get_one::<String>("compile").unwrap();
    let verbose = matches
        .get_one::<String>("verbose")
        .unwrap()
        .parse::<usize>()
        .unwrap();
    let debug = matches.get_flag("debug");

    let backend = matches.get_one::<String>("backend").unwrap();
    let backend = match &backend[..] {
        "c" => Backend::C,
        "interp" => Backend::Interp,
        _ => panic!("unknown backend!"),
    };

    let flag = CompilerFlag {
        debug_mode: debug,
        verbose: verbose as u8,
        input: path::Path::new(input).into(),
        output: output.map(|out| path::Path::new(out).into()),
        backend,
    };

    let path = std::path::Path::new(&input);

    let res = crate::driver::command::compile_file(path, &flag, &mut std::io::stdout());
    match res {
        Ok(()) => {
            println!("compilation successed!");
        }
        Err(_) => {
            println!("compilation failed!");
        }
    }
}
