mod examples;

#[test]
fn test_loop_fib() {
    let actual = examples::test_file("LoopFib");
    let expect = expect_test::expect![[r#"
        Int(55)
    "#]];
    expect.assert_eq(&actual)
}
