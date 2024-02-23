mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_curried() {
    examples::test_file("curried", Value::Int(3))
}
