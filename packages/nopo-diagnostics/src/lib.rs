//! Diagnostics for `nopoc`.

pub mod span;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::{fmt, io};

pub use ariadne;

use ariadne::Source;
pub use nopo_diagnostics_derive::Report;

use span::{FileId, FileIdMap, Span};

pub type Report = ariadne::Report<'static, Span>;
pub type ReportBuilder = ariadne::ReportBuilder<'static, Span>;
pub type Label = ariadne::Label<Span>;

impl ariadne::Span for Span {
    type SourceId = FileId;

    fn source(&self) -> &Self::SourceId {
        &self.file_id
    }

    fn start(&self) -> usize {
        self.start as usize
    }

    fn end(&self) -> usize {
        self.end as usize
    }
}

pub struct FileCache<'a> {
    map: &'a FileIdMap,
    sources: HashMap<FileId, Source>,
}

impl<'a> FileCache<'a> {
    pub fn new(map: &'a FileIdMap) -> Self {
        Self {
            map,
            sources: HashMap::new(),
        }
    }
}

impl ariadne::Cache<FileId> for FileCache<'_> {
    fn fetch(&mut self, id: &FileId) -> Result<&Source, Box<dyn fmt::Debug + '_>> {
        if !self.sources.contains_key(id) {
            let str = if self.map.is_virtual(*id) {
                self.map.get_virtual_source(*id).to_string()
            } else {
                // Read file from FS.
                let path = self.map.get_file_path(*id);
                std::fs::read_to_string(path)
                    .unwrap_or_else(|_| panic!("could not read file at path `{}`", path.display()))
            };
            self.sources.insert(*id, Source::from(str));
        }
        Ok(&self.sources[id])
    }

    fn display<'b>(&self, id: &'b FileId) -> Option<Box<dyn fmt::Display + 'b>> {
        Some(Box::new(self.map.get_file_display(*id)))
    }
}

pub trait IntoReport {
    fn into_report(self) -> ReportBuilder;
}

impl IntoReport for ReportBuilder {
    fn into_report(self) -> ReportBuilder {
        self
    }
}

#[derive(Debug, Default, Clone)]
pub struct Diagnostics(Arc<Mutex<DiagnosticsData>>);

#[derive(Debug, Default)]
pub struct DiagnosticsData {
    reports: Vec<Report>,
}

impl Diagnostics {
    pub fn add(&self, report: impl IntoReport) {
        let report = report.into_report().finish();
        self.0.lock().unwrap().reports.push(report);
    }

    /// Prints all the reports to the output stream. Color is disabled. Returns `false` if not
    /// empty.
    pub fn write(&self, map: &FileIdMap, mut w: impl io::Write) -> bool {
        let mut cache = FileCache::new(map);
        for report in &self.0.lock().unwrap().reports {
            report.write(&mut cache, &mut w).unwrap();
        }
        self.is_empty()
    }

    /// Prints all the reports to `stderr`. Returns `false` if not empty.
    pub fn eprint(&self, map: &FileIdMap) -> bool {
        let mut cache = FileCache::new(map);
        for report in &self.0.lock().unwrap().reports {
            report.eprint(&mut cache).unwrap();
        }
        self.is_empty()
    }

    pub fn is_empty(&self) -> bool {
        self.0.lock().unwrap().reports.is_empty()
    }
}
