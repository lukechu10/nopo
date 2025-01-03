use codegen::Codegen;
use nopo_parser::ast::Root;
use nopo_parser::visitor::Visitor;
use nopo_passes::db::Db;

use crate::vm::Vm;

pub mod codegen;
pub mod print;
pub mod types;
pub mod vm;

pub fn compile_and_run(root: &Root, db: &Db) {
    let mut codegen = Codegen::new(db);
    codegen.visit_root(root);

    let closure = codegen.root_closure();

    let mut vm = Vm::new(closure);
    vm.run();
    eprintln!("== STACK");
    for value in &vm.stack {
        eprintln!("{value}");
    }
    eprintln!();
}
