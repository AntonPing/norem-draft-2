use norem_lang::compile::evaluate::Value;

pub fn test_file(module: &'static str, expected: Value) {
    let mut input = String::new();
    input.push_str("examples/");
    input.push_str(module);
    input.push_str(".nr");
    let res = norem_lang::driver::command::compile_file(&input);
    assert_eq!(res, expected);
}
