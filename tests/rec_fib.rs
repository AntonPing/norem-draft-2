mod examples;
use norem_lang::compile::evaluate::Value;

#[test]
fn test_rec_fib() {
    examples::test_file("RecFib", Value::Int(55))
}
