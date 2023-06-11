//! REPL for nopo.

use std::error::Error;
use std::io::{BufRead, Write};

use crate::passes::resolution::run_resolution_passes;
use nopo_diagnostics::span::FileIdMap;
use nopo_diagnostics::Diagnostics;

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
        let mut parser = crate::parser::Parser::new(repl_id, line, diagnostics.clone());

        if !diagnostics.eprint(&map) {
            continue;
        }

        let root = match parser.parse_root() {
            Ok(root) => root,
            Err(err) => {
                eprintln!("Error: {err}");
                continue;
            }
        };
        eprintln!("Root: {root:#?}");
        run_resolution_passes(&root);
    }

    Ok(())
}
