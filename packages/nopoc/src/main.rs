use clap::Parser;
use std::error::Error;
use std::path::PathBuf;

use crate::passes::parse_files_recursive;

pub mod ast;
pub mod parser;
pub mod passes;
pub mod repl;
pub mod span;

/// The Nopo CLI.
#[derive(Debug, Parser)]
pub struct Args {
    /// The entrypoint to the program.
    #[arg(short = 'i', long)]
    input: Option<PathBuf>,
}

fn main() {
    match entry() {
        Ok(_) => {}
        Err(err) => eprintln!("{err}"),
    }
}

fn entry() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    if let Some(input) = args.input {
        let parse_result = parse_files_recursive(&input)?;
        parse_result.check();
        println!("Compiled successfully!");
        Ok(())
    } else {
        repl::start_repl()
    }
}
