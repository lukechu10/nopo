//! REPL for nopo.

use std::error::Error;
use std::io::{BufRead, Write};

use crate::span::FileId;

pub fn start_repl() -> Result<(), Box<dyn Error>> {
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

        let mut parser = crate::parser::Parser::new(FileId::DUMMY, line); // FIXME: Do not use
                                                                          // FileId::DUMMY
        let root = match parser.parse_expr() {
            Ok(root) => root,
            Err(err) => {
                eprintln!("Error: {err}");
                continue;
            }
        };
        eprintln!("Root: {root:#?}");
    }

    Ok(())
}
