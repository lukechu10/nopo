//! Example usage.

use std::path::PathBuf;

use nopo_diagnostics::span::{FileIdMap, Span};
use nopo_diagnostics::{FileCache, IntoReport};

#[derive(IntoReport)]
#[kind("error")]
#[message("expected an expression, found {token}")]
pub struct ExpectedExpr {
    span: Span,
    #[label(message = "expected an expression")]
    found: Span,
    token: String,
}

fn main() {
    let mut map = FileIdMap::new();
    let file_id = map.insert_new_file(PathBuf::from("../../README.md"));
    let err = ExpectedExpr {
        span: Span {
            start: 5,
            end: 10,
            file_id,
        },
        found: Span {
            start: 5,
            end: 12,
            file_id,
        },
        token: "abcdef".to_string(),
    };
    let report = err.into_report();
    let cache = FileCache::new(&map);
    report.print(cache).unwrap();
}
