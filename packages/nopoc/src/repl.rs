//! REPL for nopo.

use std::error::Error;

use nopo_diagnostics::span::FileIdMap;
use nopo_diagnostics::Diagnostics;
use nopo_parser::parser::Parser;
use nopo_passes::run_resolution_passes;
use nopo_vm::compile_and_run;
use reedline::{DefaultPrompt, DefaultPromptSegment, FileBackedHistory, Reedline, Signal};

pub fn start_repl() -> Result<(), Box<dyn Error>> {
    let mut map = FileIdMap::new();

    let cache_dir = dirs::cache_dir().expect("could not get cache dir");
    let path = cache_dir.join("nopo/.nopo-history");
    let history = Box::new(
        FileBackedHistory::with_file(100, path).expect("could not create repl history file"),
    );

    let mut line_editor = Reedline::create().with_history(history);
    let prompt = DefaultPrompt::new(
        DefaultPromptSegment::Basic("nopo".to_string()),
        DefaultPromptSegment::Empty,
    );

    for line in 0.. {
        let sig = line_editor.read_line(&prompt);
        let buf = match sig {
            Ok(Signal::Success(buf)) => buf,
            Ok(Signal::CtrlC | Signal::CtrlD) => {
                println!(".quit");
                return Ok(());
            }
            Err(err) => {
                eprintln!("{err}");
                continue;
            }
        };

        let diagnostics = Diagnostics::default();
        let repl_id = map.create_virtual_file(&format!("<repl-{line}>"), buf.clone());

        let mut parser = Parser::new(repl_id, &buf, diagnostics.clone());
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
