mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_trivial() {
    examples::test_file("trivial", Value::Int(42))
}
