//! REPL for nopo.

use std::error::Error;
use std::io::{BufRead, Write};

use nopo_diagnostics::span::FileIdMap;
use nopo_diagnostics::Diagnostics;
use nopo_passes::run_resolution_passes;
use nopo_vm::compile_and_run;

pub fn start_repl() -> Result<(), Box<dyn Error>> {
    let mut map = FileIdMap::new();

    let mut stdin = std::io::stdin().lock();
    let mut stdout = std::io::stdout().lock();
    loop {
        print!("(nopo) ");
        stdout.flush()?;
        let mut line = String::new();
        stdin.read_line(&mut line)?;
        let line = line.trim();
        match line {
            "" => continue,
            ".quit" | ".q" => break,
            _ => {}
        };

        let diagnostics = Diagnostics::default();
        let repl_id = map.create_virtual_file("<repl>", line.to_string());
        let mut parser = nopo_parser::parser::Parser::new(repl_id, line, diagnostics.clone());
        let root = parser.parse_root();
        if !diagnostics.eprint(&map) {
            continue;
        }

        let unify = run_resolution_passes(&root, diagnostics.clone());
        if !diagnostics.eprint(&map) {
            continue;
        }

        compile_and_run(&root, unify.unwrap());
    }

    Ok(())
}
