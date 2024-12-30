pub mod check_records;
pub mod collect_modules;
pub mod db;
pub mod gen_module_type;
pub mod map;
pub mod resolve;
pub mod unify;

#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use indexmap::IndexMap;
use nopo_diagnostics::span::{FileId, FileIdMap};
use nopo_diagnostics::Diagnostics;
use nopo_parser::ast::Root;
use nopo_parser::parser::Parser;
use nopo_parser::visitor::Visitor;
use thiserror::Error;

use self::collect_modules::CollectModules;
use self::db::Db;
use self::gen_module_type::GenModuleType;
use self::resolve::ResolveSymbols;
use self::unify::UnifyTypes;

#[derive(Error, Debug)]
pub enum CompileError {
    #[error("IO error: {0}.")]
    Io(#[from] std::io::Error),
    #[error("File `{0}` has wrong file extension. Nopo source files should end with the `.nopo` extension.")]
    BadFileExtension(PathBuf),
    #[error("Circular module declarations.")]
    CircularModDeclarations,
}

/// A file that has been parsed.
#[derive(Debug)]
pub struct ParsedFile {
    pub path: PathBuf,
    /// The name of the file without the extension.
    pub name: String,
    /// The complete source code of the file.
    pub source: String,
    pub ast: Root,
}

/// Parses a file at the specified path and returns a [`ParsedFile`] result.
///
/// # Params
/// * `path` - The path of the file to be parsed.
/// * `file_id` - The [`FileId`] of the file. This information is inlcuded in the spans produced by
///   the parser.
fn parse_file(
    path: &Path,
    file_id: FileId,
    diagnostics: Diagnostics,
) -> Result<ParsedFile, CompileError> {
    let source = std::fs::read_to_string(path)?;

    let extension = path.extension().map(|s| s.to_string_lossy().to_string());
    if extension.as_deref() != Some("nopo") {
        return Err(CompileError::BadFileExtension(path.into()));
    }
    let name = path.file_stem().unwrap().to_string_lossy().to_string();

    let mut parser = Parser::new(file_id, &source, diagnostics);
    let ast = parser.parse_root();
    Ok(ParsedFile {
        path: path.to_path_buf(),
        name,
        source,
        ast,
    })
}

/// A DAG of all the modules in the program.
pub struct ModuleGraph {
    pub files: IndexMap<FileId, ParsedFile>,
    pub file_id_map: FileIdMap,
}

impl ModuleGraph {
    /// Runs resolution passes on the module graph. The leaf modules are checked first and then the
    /// modules that depend on them are checked and so on.
    pub fn check(&self, db: &mut Db) {
        // Files should be sorted in topological order.
        for file in self.files.values() {
            run_resolution_passes(&file.ast, db);
            let mut gen_module_type = GenModuleType::new(file.path.clone(), db);
            gen_module_type.visit_root(&file.ast);
        }
    }
}

/// Recursively parse all files that can be reached from `entry` (including `entry` itself).
///
/// Uses Depth-First-Search to sort the modules in topological order.
pub fn collect_module_graph(entry: &Path, db: &mut Db) -> Result<ModuleGraph, CompileError> {
    fn get_imports(
        parent_dir: &Path,
        root: &Root,
        db: &mut Db,
    ) -> Result<Vec<PathBuf>, std::io::Error> {
        let mut collect_modules = CollectModules::new(parent_dir.to_owned(), db);
        collect_modules.visit_root(root);
        collect_modules
            .modules
            .into_iter()
            .map(|path| path.unspan().resolve(parent_dir))
            .collect::<Result<Vec<_>, _>>()
    }

    enum Mark {
        Temporary,
        Permanent,
    }

    fn visit(
        graph: &mut ModuleGraph,
        marks: &mut HashMap<PathBuf, Mark>,
        path: PathBuf,
        db: &mut Db,
    ) -> Result<(), CompileError> {
        if let Some(Mark::Permanent) = marks.get(&path) {
            return Ok(());
        }
        if let Some(Mark::Temporary) = marks.get(&path) {
            return Err(CompileError::CircularModDeclarations);
        }
        marks.insert(path.clone(), Mark::Temporary);

        // Parse the file.
        let file_id = graph.file_id_map.insert_new_file(path.clone());
        let parsed_file = parse_file(&path, file_id, db.diagnostics.clone())?;

        // Recursively visit all the modules that this module imports.
        let parent_dir = path.parent().expect("file has no parent dir");
        for import in get_imports(parent_dir, &parsed_file.ast, db)? {
            visit(graph, marks, import, db)?;
        }

        graph.files.insert(file_id, parsed_file);
        marks.insert(path, Mark::Permanent);

        Ok(())
    }

    let entry = entry.canonicalize()?;
    let mut graph = ModuleGraph {
        files: IndexMap::new(),
        file_id_map: FileIdMap::new(),
    };
    let mut marks: HashMap<PathBuf, Mark> = HashMap::new();
    visit(&mut graph, &mut marks, entry, db)?;

    Ok(graph)
}

/// Run the resolution passes on the root of the AST. Stores the results in `db`.
///
/// Not guaranteed to have complete information if there are errors.
///
/// Should only be run if there are no errors in `db`.
pub fn run_resolution_passes(root: &Root, db: &mut Db) {
    assert!(db.diagnostics.is_empty());
    let mut resolve = ResolveSymbols::new(db);
    resolve.visit_root(root);
    if !db.diagnostics.is_empty() {
        return;
    }
    let mut unify = UnifyTypes::new(db);
    unify.visit_root(root);
    if !db.diagnostics.is_empty() {
        #[expect(
            clippy::needless_return,
            reason = "we do not have other passes implemented yet"
        )]
        return;
    }
}
