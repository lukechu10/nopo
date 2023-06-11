pub mod map;
pub mod resolution;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use nopo_diagnostics::Diagnostics;
use thiserror::Error;

use crate::ast::{Ident, Root};
use nopo_diagnostics::span::{FileId, FileIdMap};

use self::resolution::run_resolution_passes;

#[derive(Error, Debug)]
pub enum CompileError {
    #[error("IO error: {0}.")]
    Io(#[from] std::io::Error),
    #[error("File `{0}` has wrong file extension. Nopo source files should end with the `.nopo` extension.")]
    BadFileExtension(PathBuf),
    #[error("Circular module declarations.")]
    CircularModDeclarations,
}

/// The main entry point for compiling nopo source code.
///
/// # Params
/// * `entry` - The path to the entry point file.
pub fn compile(entry: &Path) -> Result<(), CompileError> {
    let diagnostics = Diagnostics::default();
    let parse_result = parse_files_recursive(entry, diagnostics.clone())?;
    if !diagnostics.eprint(&parse_result.file_id_map) {
        return Ok(());
    }
    parse_result.check(diagnostics.clone());
    if !diagnostics.eprint(&parse_result.file_id_map) {
        return Ok(());
    }
    Ok(())
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
/// the parser.
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

    let mut parser = crate::parser::Parser::new(file_id, &source, diagnostics);
    let ast = parser.parse_root();
    Ok(ParsedFile {
        path: path.to_path_buf(),
        name,
        source,
        ast,
    })
}

/// Represents the module path. The entrypoint module is represented by an empty path.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModPath(Vec<String>);

impl ModPath {
    /// The [`ModPath`] for the entry file.
    pub fn entry() -> Self {
        Self(Vec::new())
    }

    pub fn extend(mut self, ident: String) -> Self {
        self.0.push(ident);
        self
    }
}

impl fmt::Display for ModPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(first) = self.0.first() {
            write!(f, "{first}")?;
        }
        for segment in self.0.iter().skip(1) {
            write!(f, ".{segment}")?;
        }
        Ok(())
    }
}

impl fmt::Debug for ModPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{self}\"")
    }
}

/// Stores all the ASTs.
pub struct ParseResult {
    pub files: BTreeMap<FileId, ParsedFile>,
    pub mod_path_map: BTreeMap<ModPath, FileId>,
    pub file_id_map: FileIdMap,
    pub entry_file_id: FileId,
}

impl ParseResult {
    /// Get the [`Root`] for the entry file.
    pub fn get_entry_root(&self) -> &Root {
        &self.files[&self.entry_file_id].ast
    }
}

/// Stores additional information extracted from the AST in various compilation passes.
pub struct CheckResult {}

/// Get the name of the modules that are declared within this [`Root`].
fn get_mod_names(ast: &Root) -> Vec<Ident> {
    ast.mod_items.iter().map(|m| &*m.ident).cloned().collect()
}

/// Recursively parse all files that can be reached from `entry` (including `entry` itself).
pub fn parse_files_recursive(
    entry: &Path,
    diagnostics: Diagnostics,
) -> Result<ParseResult, CompileError> {
    let mut mod_paths = BTreeSet::<ModPath>::new();
    let mut mod_path_map = BTreeMap::new();
    let mut files = BTreeMap::new();
    let mut file_id_map = FileIdMap::new();
    let mut entry_file_id = None;

    // A queue of files that are to be parsed. We start with the entry file.
    let mut queue = vec![(ModPath(Vec::new()), entry.to_path_buf())];

    while let Some((mod_path, fs_path)) = queue.pop() {
        // Check if we've already parsed this file.
        if mod_paths.contains(&mod_path) {
            return Err(CompileError::CircularModDeclarations);
        }

        let file_id = file_id_map.insert_new_file(fs_path.clone());
        // Check if `entry_file_id` has been set. If not, this is the entry file so we will set it
        // now.
        if entry_file_id == None {
            entry_file_id = Some(file_id);
        }

        let parsed_file = parse_file(&fs_path, file_id, diagnostics.clone())?;

        let file_dir = parsed_file
            .path
            .parent()
            .expect("file should have parent directory");
        let is_main = &parsed_file.name == "main"; // FIXME: allow nested main mod.

        // Get all the mod statements and parse the files they reference.
        let child_mod_names = get_mod_names(&parsed_file.ast);
        for child_mod_name in child_mod_names {
            let child_fs_name = format!("{child_mod_name}.nopo");
            let child_fs_path: PathBuf = if is_main {
                [file_dir, Path::new(&child_fs_name)].into_iter().collect()
            } else {
                [
                    file_dir,
                    Path::new(&parsed_file.name),
                    Path::new(&child_fs_name),
                ]
                .into_iter()
                .collect()
            };
            let child_mod_path = ModPath(
                mod_path
                    .clone()
                    .0
                    .into_iter()
                    .chain(Some(child_mod_name.to_string()))
                    .collect(),
            );
            queue.push((child_mod_path, child_fs_path));
        }

        files.insert(file_id, parsed_file);
        mod_path_map.insert(mod_path.clone(), file_id);
        mod_paths.insert(mod_path);
    }
    Ok(ParseResult {
        files,
        mod_path_map,
        file_id_map,
        entry_file_id: entry_file_id.expect("should have an entry file"),
    })
}

impl ParseResult {
    pub fn check(&self, diagnostics: Diagnostics) -> CheckResult {
        run_resolution_passes(self.get_entry_root(), diagnostics);
        CheckResult {}
    }
}
