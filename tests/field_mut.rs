mod examples;

#[test]
fn test_field_mut() {
    let actual = examples::test_file("FieldMut");
    let expect = expect_test::expect![[r#"
        Int(85)
    "#]];
    expect.assert_eq(&actual)
}
