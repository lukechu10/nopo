use clap::Parser;
use nopo_diagnostics::Diagnostics;
use nopo_passes::collect_module_graph;
use nopo_passes::db::Db;
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
        let mut db = Db::new(diagnostics.clone());
        let graph = collect_module_graph(&input, &mut db)?;
        if !diagnostics.eprint(&graph.file_id_map) {
            return Ok(());
        }
        graph.check(&mut db);
        if !diagnostics.eprint(&graph.file_id_map) {
            return Ok(());
        }
        // compile_and_run(graph.get_entry_root(), &db);
        Ok(())
    } else {
        repl::start_repl()
    }
}
