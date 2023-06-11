//! Diagnostics for `nopoc`.

pub mod span;
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex};

pub use ariadne;

use ariadne::Source;
pub use nopo_diagnostics_derive::IntoReport;

use span::{FileId, FileIdMap, Span};

pub type Report = ariadne::Report<'static, Span>;
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

impl<'a> ariadne::Cache<FileId> for FileCache<'a> {
    fn fetch(&mut self, id: &FileId) -> Result<&Source, Box<dyn fmt::Debug + '_>> {
        if !self.sources.contains_key(id) {
            // Read file from FS.
            let path = self.map.get_file_id(*id);
            let str = std::fs::read_to_string(path)
                .unwrap_or_else(|_| panic!("could not read file at path `{}`", path.display()));
            self.sources.insert(*id, Source::from(str));
        }
        Ok(&self.sources[id])
    }

    fn display<'b>(&self, id: &'b FileId) -> Option<Box<dyn fmt::Display + 'b>> {
        Some(Box::new(self.map.get_file_id(*id).display().to_string()))
    }
}

pub trait IntoReport {
    fn into_report(self) -> Report;
}

impl IntoReport for Report {
    fn into_report(self) -> Report {
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
        let report = report.into_report();
        self.0.lock().unwrap().reports.push(report);
    }

    pub fn eprint(&self, map: &FileIdMap) {
        let mut cache = FileCache::new(map);
        for report in &self.0.lock().unwrap().reports {
            report.eprint(&mut cache).unwrap();
        }
    }

    pub fn is_empty(&self) -> bool {
        self.0.lock().unwrap().reports.is_empty()
    }
}
