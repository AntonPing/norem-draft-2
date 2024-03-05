mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_reference() {
    examples::test_file("Reference", Value::Int(87))
}
