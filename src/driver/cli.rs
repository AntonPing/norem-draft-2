use clap::{command, Arg, ArgAction};

pub fn run_cli() {
    let matches = command!()
        .arg(Arg::new("input").action(ArgAction::Set).required(true))
        .arg(Arg::new("compile").short('c'))
        .arg(Arg::new("output").short('o'))
        .get_matches();

    let input = matches.get_one::<String>("input").unwrap();
    let val = super::command::compile_file(input);
    println!("{:?}", val);
}
