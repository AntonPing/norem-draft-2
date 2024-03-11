mod examples;

#[test]
fn test_pattern() {
    let actual = examples::test_file("Pattern");
    let expect = expect_test::expect![[r#"
        Int(3)
    "#]];
    expect.assert_eq(&actual)
}
