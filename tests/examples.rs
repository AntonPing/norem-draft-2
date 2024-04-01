use std::io::{Read, Seek};
use std::path;

use norem_lang::driver::command;
pub fn test_file<S: AsRef<path::Path>>(module: S) -> String {
    let mut input = path::PathBuf::new();
    input.push("examples");
    input.push(module);
    input.set_extension("nr");
    let flag = command::CompilerFlag {
        debug_mode: false,
        verbose: 10,
        backend: command::Backend::Interp,
        input: input.clone().into(),
        output: None,
    };
    let mut cout = tempfile::tempfile().unwrap();
    let _ = command::compile_file(&input, &flag, &mut cout);
    cout.rewind().unwrap();
    let mut actual = String::new();
    cout.read_to_string(&mut actual).unwrap();
    actual
}

#[test]
fn test_curried() {
    let actual = test_file("Curried");
    let expect = expect_test::expect![[r#"
        Int(3)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_field_mut() {
    let actual = test_file("FieldMut");
    let expect = expect_test::expect![[r#"
        Int(85)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_fields() {
    let actual = test_file("Fields");
    let expect = expect_test::expect![[r#"
        Int(9)
    "#]];
    expect.assert_eq(&actual)
}
#[test]
fn test_loop_fib() {
    let actual = test_file("LoopFib");
    let expect = expect_test::expect![[r#"
        Int(55)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_pattern() {
    let actual = test_file("Pattern");
    let expect = expect_test::expect![[r#"
        Int(3)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_poly_func() {
    let actual = test_file("PolyFunc");
    let expect = expect_test::expect![[r#"
        Int(8)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_rec_fib() {
    let actual = test_file("RecFib");
    let expect = expect_test::expect![[r#"
        Int(55)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_record_opt() {
    let actual = test_file("RecordOpt");
    let expect = expect_test::expect![[r#"
        Int(43)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_reference() {
    let actual = test_file("Reference");
    let expect = expect_test::expect![[r#"
        Int(87)
    "#]];
    expect.assert_eq(&actual)
}

#[test]
fn test_trivial() {
    let actual = test_file("Trivial");
    let expect = expect_test::expect![[r#"
        Int(42)
    "#]];
    expect.assert_eq(&actual)
}
