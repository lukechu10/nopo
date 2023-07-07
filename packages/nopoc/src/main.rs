use clap::Parser;
use nopo_diagnostics::Diagnostics;
use nopo_passes::{parse_files_recursive, run_resolution_passes};
use nopo_vm::compile_and_run;
use std::error::Error;
use std::path::PathBuf;

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
        let diagnostics = Diagnostics::default();
        let parse_result = parse_files_recursive(&input, diagnostics.clone())?;
        if !diagnostics.eprint(&parse_result.file_id_map) {
            return Ok(());
        }
        let db = run_resolution_passes(parse_result.get_entry_root(), diagnostics.clone());
        if !diagnostics.eprint(&parse_result.file_id_map) {
            return Ok(());
        }
        compile_and_run(parse_result.get_entry_root(), &db);
        Ok(())
    } else {
        repl::start_repl()
    }
}
