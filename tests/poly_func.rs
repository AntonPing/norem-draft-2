mod examples;

#[test]
fn test_poly_func() {
    let actual = examples::test_file("PolyFunc");
    let expect = expect_test::expect![[r#"
        Int(8)
    "#]];
    expect.assert_eq(&actual)
}
