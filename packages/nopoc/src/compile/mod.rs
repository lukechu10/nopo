pub mod metadata;

use std::collections::HashMap;
use std::fmt;
use std::path::{Path, PathBuf};

use thiserror::Error;

use crate::ast::Root;

use self::metadata::PackageMetadata;

#[derive(Error, Debug)]
pub enum CompileError {
    #[error("IO error: {0}.")]
    Io(#[from] std::io::Error),
    #[error("Parse error: {0}.")]
    Parse(#[from] crate::parser::ParseError),
    #[error("File `{0}` has wrong file extension. Nopo source files should end with the `.nopo` extension.")]
    BadFileExtension(PathBuf),
    #[error("Circular module declarations.")]
    CircularModDeclarations,
}

pub fn compile(entry: &Path) -> Result<Package, CompileError> {
    gather_file_graph(entry)
}

/// A file that has been parsed.
#[derive(Debug)]
pub struct ParsedFile {
    pub path: PathBuf,
    /// The name of the file without the extension.
    pub name: String,
    pub source: String,
    pub ast: Root,
}

/// Parses a file at the specified path and returns a [`ParsedFile`] result.
pub fn parse_file(path: &Path) -> Result<ParsedFile, CompileError> {
    let source = std::fs::read_to_string(path)?;

    let extension = path.extension().map(|s| s.to_string_lossy().to_string());
    if extension.as_deref() != Some("nopo") {
        return Err(CompileError::BadFileExtension(path.into()));
    }
    let name = path.file_stem().unwrap().to_string_lossy().to_string();

    let mut parser = crate::parser::Parser::new(&source);
    let ast = parser.parse_root()?;
    Ok(ParsedFile {
        path: path.to_path_buf(),
        name,
        source,
        ast,
    })
}

/// Represents the module path. The entrypoint module is represented by an empty path.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ModPath(Vec<String>);

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

pub struct Package {
    pub files: HashMap<ModPath, ParsedFile>,
}

fn get_mod_names(ast: &Root) -> Vec<&str> {
    ast.items
        .iter()
        .filter_map(|item| match &**item {
            crate::ast::Item::Mod(mod_item) => Some(mod_item.path.as_str()),
            _ => None,
        })
        .collect()
}

pub fn gather_file_graph(entry: &Path) -> Result<Package, CompileError> {
    let mut files = HashMap::new();
    let mut queue = vec![(ModPath(Vec::new()), entry.to_path_buf())];
    while let Some((mod_path, fs_path)) = queue.pop() {
        // Check if we've already parsed this file.
        if files.contains_key(&mod_path) {
            return Err(CompileError::CircularModDeclarations);
        }

        let file = parse_file(&fs_path)?;
        let file_dir = file
            .path
            .parent()
            .expect("file should have parent directory");
        let is_main = &file.name == "main";

        // Get all the mod statements and parse the files they reference.
        let child_mod_names = get_mod_names(&file.ast);
        for child_mod_name in child_mod_names {
            let child_fs_name = format!("{child_mod_name}.nopo");
            let child_fs_path: PathBuf = if is_main {
                [file_dir, Path::new(&child_fs_name)].into_iter().collect()
            } else {
                [file_dir, Path::new(&file.name), Path::new(&child_fs_name)]
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

        files.insert(mod_path, file);
    }
    Ok(Package { files })
}

impl Package {
    pub fn get_metadata(&self) -> PackageMetadata {
        let mut metadata = PackageMetadata::default();
        for (mod_path, file) in &self.files {
            metadata.extract_from_ast(mod_path.clone(), &file.ast);
        }
        metadata
    }
}
