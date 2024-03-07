mod examples;
use norem_lang::backend::evaluate::Value;

#[test]
fn test_trivial() {
    examples::test_file("Trivial", Value::Int(42))
}
