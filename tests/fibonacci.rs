mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_fibonacci() {
    examples::test_file("fibonacci", Value::Int(55))
}
