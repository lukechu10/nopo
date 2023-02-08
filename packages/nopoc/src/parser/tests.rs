use expect_test::{expect, Expect};

use super::*;

fn check_root(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let root = parser.parse_root().expect("could not parse root");
    expected.assert_debug_eq(&root);
}

fn check_item(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let item = parser.parse_item().expect("could not parse item");
    expected.assert_debug_eq(&item);
}

fn check_stmt(input: &str, expected: Expect) {
    let mut parser = Parser::new(input);
    let stmt = parser
        .parse_stmt_with_semi(false)
        .expect("could not parse stmt");
    expected.assert_debug_eq(&stmt);
}

#[test]
fn test_parse_root() {
    check_root(
        r#"
fn a() {}
fn b() {}"#,
        expect![[r#"
            Root {
                items: [
                    (1..10) Fn(
                        (1..10) FnItem {
                            ident: (4..5) "a",
                            args: (5..7) FnArgs {
                                args: [],
                            },
                            ret_ty: None,
                            body: (8..10) BlockExpr {
                                stmts: [],
                            },
                        },
                    ),
                    (11..20) Fn(
                        (11..20) FnItem {
                            ident: (14..15) "b",
                            args: (15..17) FnArgs {
                                args: [],
                            },
                            ret_ty: None,
                            body: (18..20) BlockExpr {
                                stmts: [],
                            },
                        },
                    ),
                ],
            }
        "#]],
    );
}

#[test]
fn test_parse_item() {
    check_item(
        r#"fn main() {}"#,
        expect![[r#"
            (0..12) Fn(
                (0..12) FnItem {
                    ident: (3..7) "main",
                    args: (7..9) FnArgs {
                        args: [],
                    },
                    ret_ty: None,
                    body: (10..12) BlockExpr {
                        stmts: [],
                    },
                },
            )
        "#]],
    );
    check_item(
        r#"fn foo(bar: i32) {}"#,
        expect![[r#"
            (0..19) Fn(
                (0..19) FnItem {
                    ident: (3..6) "foo",
                    args: (6..16) FnArgs {
                        args: [
                            (7..15) Binding {
                                ident: (7..10) "bar",
                                ty: Some(
                                    (12..15) "i32",
                                ),
                            },
                        ],
                    },
                    ret_ty: None,
                    body: (17..19) BlockExpr {
                        stmts: [],
                    },
                },
            )
        "#]],
    );
}

#[test]
fn test_parse_lits() {
    check_stmt(
        r#"true"#,
        expect![[r#"
            (0..4) ExprStmt(
                (0..4) LitBool(
                    true,
                ),
            )
        "#]],
    );
    check_stmt(
        r#"false"#,
        expect![[r#"
            (0..5) ExprStmt(
                (0..5) LitBool(
                    false,
                ),
            )
        "#]],
    );
    check_stmt(
        r#"1"#,
        expect![[r#"
            (0..1) ExprStmt(
                (0..1) LitInt(
                    1,
                ),
            )
        "#]],
    );
    check_stmt(
        r#"1.23"#,
        expect![[r#"
            (0..4) ExprStmt(
                (0..4) LitFloat(
                    "1.23",
                ),
            )
        "#]],
    );
    check_stmt(
        r#""Hello, World!""#,
        expect![[r#"
            (0..15) ExprStmt(
                (0..15) LitStr(
                    "Hello, World!",
                ),
            )
        "#]],
    );
    check_stmt(
        r#"'a'"#,
        expect![[r#"
            (0..3) ExprStmt(
                (0..3) LitChar(
                    'a',
                ),
            )
        "#]],
    );
}

#[test]
fn test_parse_bin_expr() {
    check_stmt(
        r#"1 + 1"#,
        expect![[r#"
            (0..5) ExprStmt(
                (0..5) Binary(
                    (0..5) BinaryExpr {
                        lhs: (0..1) LitInt(
                            1,
                        ),
                        op: (2..3) Plus,
                        rhs: (4..5) LitInt(
                            1,
                        ),
                    },
                ),
            )
        "#]],
    );
    check_stmt(
        r#"1 + 2 + 3"#,
        expect![[r#"
            (0..9) ExprStmt(
                (0..9) Binary(
                    (0..9) BinaryExpr {
                        lhs: (0..5) Binary(
                            (0..5) BinaryExpr {
                                lhs: (0..1) LitInt(
                                    1,
                                ),
                                op: (2..3) Plus,
                                rhs: (4..5) LitInt(
                                    2,
                                ),
                            },
                        ),
                        op: (6..7) Plus,
                        rhs: (8..9) LitInt(
                            3,
                        ),
                    },
                ),
            )
        "#]],
    );
    check_stmt(
        r#"1 + 2 * 3"#,
        expect![[r#"
            (0..9) ExprStmt(
                (0..9) Binary(
                    (0..9) BinaryExpr {
                        lhs: (0..1) LitInt(
                            1,
                        ),
                        op: (2..3) Plus,
                        rhs: (4..9) Binary(
                            (4..9) BinaryExpr {
                                lhs: (4..5) LitInt(
                                    2,
                                ),
                                op: (6..7) Mul,
                                rhs: (8..9) LitInt(
                                    3,
                                ),
                            },
                        ),
                    },
                ),
            )
        "#]],
    );
    check_stmt(
        r#"(1 + 2) * 3"#,
        expect![[r#"
            (0..11) ExprStmt(
                (0..11) Binary(
                    (0..11) BinaryExpr {
                        lhs: (1..6) Binary(
                            (1..6) BinaryExpr {
                                lhs: (1..2) LitInt(
                                    1,
                                ),
                                op: (3..4) Plus,
                                rhs: (5..6) LitInt(
                                    2,
                                ),
                            },
                        ),
                        op: (8..9) Mul,
                        rhs: (10..11) LitInt(
                            3,
                        ),
                    },
                ),
            )
        "#]],
    );
    check_stmt(
        r#"a.b.c"#,
        expect![[r#"
            (0..5) ExprStmt(
                (0..5) Binary(
                    (0..5) BinaryExpr {
                        lhs: (0..1) Ident(
                            (0..1) "a",
                        ),
                        op: (1..2) Dot,
                        rhs: (2..5) Binary(
                            (2..5) BinaryExpr {
                                lhs: (2..3) Ident(
                                    (2..3) "b",
                                ),
                                op: (3..4) Dot,
                                rhs: (4..5) Ident(
                                    (4..5) "c",
                                ),
                            },
                        ),
                    },
                ),
            )
        "#]],
    );
}
