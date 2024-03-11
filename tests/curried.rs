mod examples;
#[test]
fn test_curried() {
    let actual = examples::test_file("Curried");
    let expect = expect_test::expect![[r#"
        Int(3)
    "#]];
    expect.assert_eq(&actual)
}
