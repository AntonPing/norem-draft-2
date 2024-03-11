mod examples;

#[test]
fn test_reference() {
    let actual = examples::test_file("Reference");
    let expect = expect_test::expect![[r#"
        Int(87)
    "#]];
    expect.assert_eq(&actual)
}
