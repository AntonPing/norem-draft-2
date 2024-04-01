mod examples;

#[test]
fn test_record_opt() {
    let actual = examples::test_file("RecordOpt");
    let expect = expect_test::expect![[r#"
        Int(43)
    "#]];
    expect.assert_eq(&actual)
}
