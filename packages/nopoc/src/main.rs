use clap::Parser;
use std::error::Error;
use std::path::PathBuf;

pub mod ast;
pub mod parser;
pub mod passes;
pub mod repl;

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
        passes::compile(&input)?;
        println!("Done!");
        Ok(())
    } else {
        repl::start_repl()
    }
}
