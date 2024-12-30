use expect_test::{expect, Expect};
use nopo_diagnostics::span::FileIdMap;
use nopo_diagnostics::Diagnostics;

use crate::parser::Parser;

#[track_caller]
fn check_root(input: &str, expect: Expect) {
    let mut map = FileIdMap::new();
    let diagnostics = Diagnostics::default();
    let id = map.create_virtual_file("<test>", input.to_string());

    let mut parser = Parser::new(id, input, diagnostics.clone());
    let root = parser.parse_root();
    assert!(diagnostics.eprint(&map));
    expect.assert_debug_eq(&root);
}

#[track_caller]
fn check_expr(input: &str, expect: Expect) {
    let mut map = FileIdMap::new();
    let diagnostics = Diagnostics::default();
    let id = map.create_virtual_file("<test>", input.to_string());

    let mut parser = Parser::new(id, input, diagnostics.clone());
    let root = parser.parse_expr();
    assert!(diagnostics.eprint(&map));
    expect.assert_debug_eq(&root);
}

#[test]
fn test_parse_root() {
    check_root(
        r#"
let x = 1
let double x = 2 * x
type list 'a = Nil | Cons of 'a (list 'a)
"#,
        expect![[r#"
            Root {
                let_items: Arena {
                    len: 2,
                    data: [
                        (1..10) LetItem {
                            attrs: (1..0) Attributes {
                                attrs: [],
                            },
                            vis: (1..0) Priv,
                            ident: (5..6) "x",
                            params: [],
                            ret_ty: None,
                            expr: (9..10) Lit(
                                (9..8) Int(
                                    1,
                                ),
                            ),
                        },
                        (11..31) LetItem {
                            attrs: (11..10) Attributes {
                                attrs: [],
                            },
                            vis: (11..10) Priv,
                            ident: (15..21) "double",
                            params: [
                                (22..23) Param {
                                    ident: (22..23) "x",
                                    ty: None,
                                },
                            ],
                            ret_ty: None,
                            expr: (26..31) Binary(
                                (26..31) BinaryExpr {
                                    lhs: (26..27) Lit(
                                        (26..25) Int(
                                            2,
                                        ),
                                    ),
                                    op: (28..29) Mul,
                                    rhs: (30..31) Ident(
                                        (30..31) IdentExpr {
                                            ident: (30..31) "x",
                                        },
                                    ),
                                },
                            ),
                        },
                    ],
                },
                type_items: Arena {
                    len: 1,
                    data: [
                        (32..73) TypeItem {
                            attrs: (32..31) Attributes {
                                attrs: [],
                            },
                            vis: (32..31) Priv,
                            ident: (37..41) "list",
                            ty_params: [
                                (42..44) TypeParam {
                                    ident: (43..44) "a",
                                },
                            ],
                            def: (47..73) Adt(
                                (47..73) AdtDef {
                                    data_constructors: [
                                        (47..50) DataConstructor {
                                            ident: (47..50) "Nil",
                                            of: [],
                                        },
                                        (53..73) DataConstructor {
                                            ident: (53..57) "Cons",
                                            of: [
                                                (61..63) Param(
                                                    (61..63) TypeParam {
                                                        ident: (62..63) "a",
                                                    },
                                                ),
                                                (65..72) Constructed(
                                                    (65..72) ConstructedType {
                                                        constructor: (65..69) Path(
                                                            (65..69) Path {
                                                                path: [
                                                                    (65..69) "list",
                                                                ],
                                                            },
                                                        ),
                                                        arg: (70..72) Param(
                                                            (70..72) TypeParam {
                                                                ident: (71..72) "a",
                                                            },
                                                        ),
                                                    },
                                                ),
                                            ],
                                        },
                                    ],
                                },
                            ),
                        },
                    ],
                },
                items: [
                    Let(
                        Idx::<LetItem>>(0),
                    ),
                    Let(
                        Idx::<LetItem>>(1),
                    ),
                    Type(
                        Idx::<TypeItem>>(0),
                    ),
                ],
            }
        "#]],
    );
}

#[test]
fn test_parse_literals() {
    check_expr(
        r#"true"#,
        expect![[r#"
            (0..4) Lit(
                (0..0) Bool(
                    true,
                ),
            )
        "#]],
    );
    check_expr(
        r#"false"#,
        expect![[r#"
            (0..5) Lit(
                (0..0) Bool(
                    false,
                ),
            )
        "#]],
    );
    check_expr(
        r#"1"#,
        expect![[r#"
            (0..1) Lit(
                (0..0) Int(
                    1,
                ),
            )
        "#]],
    );
    check_expr(
        r#"1.23"#,
        expect![[r#"
            (0..4) Lit(
                (0..0) Float(
                    "1.23",
                ),
            )
        "#]],
    );
    check_expr(
        r#""Hello, World!""#,
        expect![[r#"
            (0..15) Lit(
                (0..0) String(
                    "Hello, World!",
                ),
            )
        "#]],
    );
    check_expr(
        r#"'a'"#,
        expect![[r#"
            (0..3) Lit(
                (0..0) Char(
                    'a',
                ),
            )
        "#]],
    );
}

#[test]
fn test_parse_bin_expr() {
    check_expr(
        r#"1 + 1"#,
        expect![[r#"
            (0..5) Binary(
                (0..5) BinaryExpr {
                    lhs: (0..1) Lit(
                        (0..0) Int(
                            1,
                        ),
                    ),
                    op: (2..3) Plus,
                    rhs: (4..5) Lit(
                        (4..3) Int(
                            1,
                        ),
                    ),
                },
            )
        "#]],
    );
    check_expr(
        r#"1 + 2 + 3"#,
        expect![[r#"
            (0..9) Binary(
                (0..9) BinaryExpr {
                    lhs: (0..5) Binary(
                        (0..5) BinaryExpr {
                            lhs: (0..1) Lit(
                                (0..0) Int(
                                    1,
                                ),
                            ),
                            op: (2..3) Plus,
                            rhs: (4..5) Lit(
                                (4..3) Int(
                                    2,
                                ),
                            ),
                        },
                    ),
                    op: (6..7) Plus,
                    rhs: (8..9) Lit(
                        (8..7) Int(
                            3,
                        ),
                    ),
                },
            )
        "#]],
    );
    check_expr(
        r#"1 + 2 * 3"#,
        expect![[r#"
            (0..9) Binary(
                (0..9) BinaryExpr {
                    lhs: (0..1) Lit(
                        (0..0) Int(
                            1,
                        ),
                    ),
                    op: (2..3) Plus,
                    rhs: (4..9) Binary(
                        (4..9) BinaryExpr {
                            lhs: (4..5) Lit(
                                (4..3) Int(
                                    2,
                                ),
                            ),
                            op: (6..7) Mul,
                            rhs: (8..9) Lit(
                                (8..7) Int(
                                    3,
                                ),
                            ),
                        },
                    ),
                },
            )
        "#]],
    );
    check_expr(
        r#"(1 + 2) * 3"#,
        expect![[r#"
            (0..11) Binary(
                (0..11) BinaryExpr {
                    lhs: (1..6) Binary(
                        (1..6) BinaryExpr {
                            lhs: (1..2) Lit(
                                (1..1) Int(
                                    1,
                                ),
                            ),
                            op: (3..4) Plus,
                            rhs: (5..6) Lit(
                                (5..4) Int(
                                    2,
                                ),
                            ),
                        },
                    ),
                    op: (8..9) Mul,
                    rhs: (10..11) Lit(
                        (10..9) Int(
                            3,
                        ),
                    ),
                },
            )
        "#]],
    );
    check_expr(
        r#"a.b.c"#,
        expect![[r#"
            (0..5) Binary(
                (0..5) BinaryExpr {
                    lhs: (0..3) Binary(
                        (0..3) BinaryExpr {
                            lhs: (0..1) Ident(
                                (0..1) IdentExpr {
                                    ident: (0..1) "a",
                                },
                            ),
                            op: (1..2) Dot,
                            rhs: (2..3) Ident(
                                (2..3) IdentExpr {
                                    ident: (2..3) "b",
                                },
                            ),
                        },
                    ),
                    op: (3..4) Dot,
                    rhs: (4..5) Ident(
                        (4..5) IdentExpr {
                            ident: (4..5) "c",
                        },
                    ),
                },
            )
        "#]],
    );
}

#[test]
fn test_parse_fn_application() {
    check_expr(
        r#"foo"#,
        expect![[r#"
            (0..3) Ident(
                (0..3) IdentExpr {
                    ident: (0..3) "foo",
                },
            )
        "#]],
    );
    check_expr(
        r#"a.foo"#,
        expect![[r#"
            (0..5) Binary(
                (0..5) BinaryExpr {
                    lhs: (0..1) Ident(
                        (0..1) IdentExpr {
                            ident: (0..1) "a",
                        },
                    ),
                    op: (1..2) Dot,
                    rhs: (2..5) Ident(
                        (2..5) IdentExpr {
                            ident: (2..5) "foo",
                        },
                    ),
                },
            )
        "#]],
    );
    check_expr(
        r#"foo a"#,
        expect![[r#"
            (0..5) Binary(
                (0..5) BinaryExpr {
                    lhs: (0..3) Ident(
                        (0..3) IdentExpr {
                            ident: (0..3) "foo",
                        },
                    ),
                    op: (4..3) FnCall,
                    rhs: (4..5) Ident(
                        (4..5) IdentExpr {
                            ident: (4..5) "a",
                        },
                    ),
                },
            )
        "#]],
    );
    check_expr(
        r#"foo a b c"#,
        expect![[r#"
            (0..9) Binary(
                (0..9) BinaryExpr {
                    lhs: (0..7) Binary(
                        (0..7) BinaryExpr {
                            lhs: (0..5) Binary(
                                (0..5) BinaryExpr {
                                    lhs: (0..3) Ident(
                                        (0..3) IdentExpr {
                                            ident: (0..3) "foo",
                                        },
                                    ),
                                    op: (4..3) FnCall,
                                    rhs: (4..5) Ident(
                                        (4..5) IdentExpr {
                                            ident: (4..5) "a",
                                        },
                                    ),
                                },
                            ),
                            op: (6..5) FnCall,
                            rhs: (6..7) Ident(
                                (6..7) IdentExpr {
                                    ident: (6..7) "b",
                                },
                            ),
                        },
                    ),
                    op: (8..7) FnCall,
                    rhs: (8..9) Ident(
                        (8..9) IdentExpr {
                            ident: (8..9) "c",
                        },
                    ),
                },
            )
        "#]],
    );
}
