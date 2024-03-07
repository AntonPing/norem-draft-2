mod examples;
use norem_lang::backend::evaluate::Value;

#[test]
fn test_loop_fib() {
    examples::test_file("LoopFib", Value::Int(55))
}
