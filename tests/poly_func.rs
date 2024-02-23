mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_poly_func() {
    examples::test_file("PolyFunc", Value::Int(8))
}
