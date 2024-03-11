mod examples;

#[test]
fn test_rec_fib() {
    let actual = examples::test_file("RecFib");
    let expect = expect_test::expect![[r#"
        Int(55)
    "#]];
    expect.assert_eq(&actual)
}
