mod examples;
use norem_lang::backend::evaluate::Value;

#[test]
fn test_pattern() {
    examples::test_file("Pattern", Value::Int(3))
}
