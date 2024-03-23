mod examples;

#[test]
fn test_fields() {
    let actual = examples::test_file("Fields");
    let expect = expect_test::expect![[r#"
        Int(9)
    "#]];
    expect.assert_eq(&actual)
}
