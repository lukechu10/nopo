//! Nopo CLI.

use std::path::PathBuf;

use clap::Parser;

/// The Nopo CLI.
#[derive(Debug, Parser)]
pub struct Args {
    /// The entrypoint to the program.
    #[arg(short = 'i', long)]
    input: PathBuf,
}

fn main() {
    let args = Args::parse();

    eprintln!("Options: {args:#?}");
}
