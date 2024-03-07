mod examples;
use norem_lang::backend::evaluate::Value;

#[test]
fn test_curried() {
    examples::test_file("Curried", Value::Int(3))
}
