mod examples;

#[test]
fn test_trivial() {
    let actual = examples::test_file("Trivial");
    let expect = expect_test::expect![[r#"
        Int(42)
    "#]];
    expect.assert_eq(&actual)
}
