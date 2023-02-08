use clap::Parser;
use std::error::Error;
use std::path::PathBuf;

pub mod ast;
pub mod compile;
pub mod parser;
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
        let package = compile::gather_file_graph(&input)?;
        let metadata = package.get_metadata();
        println!("{metadata:#?}");
        Ok(())
    } else {
        repl::start_repl()
    }
}
