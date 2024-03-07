mod examples;
use norem_lang::backend::evaluate::Value;

#[test]
fn test_reference() {
    examples::test_file("Reference", Value::Int(87))
}
