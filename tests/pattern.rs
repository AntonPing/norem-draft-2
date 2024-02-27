mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_pattern() {
    examples::test_file("Pattern", Value::Int(3))
}
