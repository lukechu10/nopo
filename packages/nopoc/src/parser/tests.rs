use expect_test::{expect, Expect};
use nopo_diagnostics::span::FileIdMap;

use super::*;

#[track_caller]
fn check_root(input: &str, expect: Expect) {
    let mut map = FileIdMap::new();
    let diagnostics = Diagnostics::default();
    let id = map.create_virtual_file("<test>", input.to_string());

    let mut parser = Parser::new(id, input, diagnostics.clone());
    assert!(diagnostics.eprint(&map));

    let root = parser.parse_root();
    expect.assert_debug_eq(&root);
}

#[track_caller]
fn check_expr(input: &str, expect: Expect) {
    let mut map = FileIdMap::new();
    let diagnostics = Diagnostics::default();
    let id = map.create_virtual_file("<test>", input.to_string());

    let mut parser = Parser::new(id, input, diagnostics.clone());
    assert!(diagnostics.eprint(&map));

    let root = parser.parse_expr();
    expect.assert_debug_eq(&root);
}

#[test]
fn test_parse_root() {
    check_root(
        r#"
let x = 1;
let double x = 2 * x;
type list 'a = Nil | Cons of 'a (list 'a)
"#,
        expect![[r#"
            Root {
                let_items: Arena {
                    len: 2,
                    data: [
                        (1..11) LetItem {
                            attrs: (1..0) Attributes {
                                attrs: [],
                            },
                            vis: (1..0) Priv,
                            ident: (5..6) "x",
                            params: [],
                            ret_ty: None,
                            expr: (9..10) LitInt(
                                1,
                            ),
                        },
                        (12..33) LetItem {
                            attrs: (12..11) Attributes {
                                attrs: [],
                            },
                            vis: (12..11) Priv,
                            ident: (16..22) "double",
                            params: [
                                (23..24) Param {
                                    ident: (23..24) "x",
                                    ty: None,
                                },
                            ],
                            ret_ty: None,
                            expr: (27..32) Binary(
                                (27..32) BinaryExpr {
                                    lhs: (27..28) LitInt(
                                        2,
                                    ),
                                    op: (29..30) Mul,
                                    rhs: (31..32) Ident(
                                        (31..32) IdentExpr {
                                            ident: (31..32) "x",
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
                        (34..75) TypeItem {
                            attrs: (34..33) Attributes {
                                attrs: [],
                            },
                            vis: (34..33) Priv,
                            ident: (39..43) "list",
                            ty_params: [
                                (44..46) TypeParam {
                                    ident: (45..46) "a",
                                },
                            ],
                            def: (49..75) Adt(
                                (49..75) AdtDef {
                                    data_constructors: [
                                        (49..52) DataConstructor {
                                            ident: (49..52) "Nil",
                                            of: [],
                                        },
                                        (55..75) DataConstructor {
                                            ident: (55..59) "Cons",
                                            of: [
                                                (63..75) Constructed(
                                                    (63..75) ConstructedType {
                                                        constructor: (63..65) Param(
                                                            (63..65) TypeParam {
                                                                ident: (64..65) "a",
                                                            },
                                                        ),
                                                        arg: (67..74) Constructed(
                                                            (67..74) ConstructedType {
                                                                constructor: (67..71) Path(
                                                                    (67..71) PathType {
                                                                        path: [
                                                                            (67..71) "list",
                                                                        ],
                                                                    },
                                                                ),
                                                                arg: (72..74) Param(
                                                                    (72..74) TypeParam {
                                                                        ident: (73..74) "a",
                                                                    },
                                                                ),
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
                mod_items: [],
                use_items: [],
            }
        "#]],
    );
}

#[test]
fn test_parse_literals() {
    check_expr(
        r#"true"#,
        expect![[r#"
            (0..4) LitBool(
                true,
            )
        "#]],
    );
    check_expr(
        r#"false"#,
        expect![[r#"
            (0..5) LitBool(
                false,
            )
        "#]],
    );
    check_expr(
        r#"1"#,
        expect![[r#"
            (0..1) LitInt(
                1,
            )
        "#]],
    );
    check_expr(
        r#"1.23"#,
        expect![[r#"
            (0..4) LitFloat(
                "1.23",
            )
        "#]],
    );
    check_expr(
        r#""Hello, World!""#,
        expect![[r#"
            (0..15) LitStr(
                "Hello, World!",
            )
        "#]],
    );
    check_expr(
        r#"'a'"#,
        expect![[r#"
            (0..3) LitChar(
                'a',
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
                    lhs: (0..1) LitInt(
                        1,
                    ),
                    op: (2..3) Plus,
                    rhs: (4..5) LitInt(
                        1,
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
            )
        "#]],
    );
    check_expr(
        r#"1 + 2 * 3"#,
        expect![[r#"
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
