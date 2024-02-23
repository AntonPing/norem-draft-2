mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_trivial() {
    examples::test_file("Trivial", Value::Int(42))
}
