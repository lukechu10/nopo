use std::io::Write;

use expect_test::Expect;
use nopo_diagnostics::span::FileIdMap;
use nopo_diagnostics::Diagnostics;
use nopo_parser::parser::Parser;

use crate::run_resolution_passes;

pub fn check(input: &str) {
    let mut map = FileIdMap::new();
    let diagnostics = Diagnostics::default();
    let id = map.create_virtual_file("<test>", input.to_string());

    let mut parser = Parser::new(id, input, diagnostics.clone());
    assert!(diagnostics.eprint(&map));

    let root = parser.parse_root();
    let _ = run_resolution_passes(&root, diagnostics.clone());
    assert!(diagnostics.eprint(&map));
}

pub fn check_types(input: &str, expect: Expect) {
    let mut map = FileIdMap::new();
    let diagnostics = Diagnostics::default();
    let id = map.create_virtual_file("<test>", input.to_string());

    let mut parser = Parser::new(id, input, diagnostics.clone());
    assert!(diagnostics.eprint(&map));

    let root = parser.parse_root();
    let db = run_resolution_passes(&root, diagnostics.clone());
    assert!(diagnostics.eprint(&map));

    let mut actual = String::new();
    let mut binding_types = db.binding_types_map.into_iter().collect::<Vec<_>>();
    binding_types.sort_by_key(|(idx, _)| idx.into_raw());
    for (id, ty) in binding_types {
        let binding = &db.bindings[id];
        let ident = &binding.ident;
        actual.push_str(&format!("{ident}: {}\n", ty.pretty(&db.types_map.items)));
    }

    expect.assert_eq(&actual.trim());
}

pub fn check_fail(input: &str, expect: Expect) {
    concolor::set(concolor::ColorChoice::Never);
    let mut map = FileIdMap::new();
    let diagnostics = Diagnostics::default();
    let id = map.create_virtual_file("<test>", input.to_string());

    let mut parser = Parser::new(id, input, diagnostics.clone());
    assert!(diagnostics.eprint(&map));

    let root = parser.parse_root();
    run_resolution_passes(&root, diagnostics.clone());

    let mut buf = Vec::new();
    diagnostics.write(&map, buf.by_ref());
    let actual = String::from_utf8_lossy(&buf);
    expect.assert_eq(&actual);
}
