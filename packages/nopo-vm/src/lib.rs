use codegen::Codegen;
use nopo_parser::ast::Root;
use nopo_parser::visitor::Visitor;
use nopo_passes::unify::UnifyTypes;

use crate::vm::Vm;

pub mod codegen;
pub mod types;
pub mod vm;

pub fn compile_and_run(root: &Root, unify: UnifyTypes) {
    let mut codegen = Codegen::new(unify);
    codegen.visit_root(root);

    let closure = codegen.root_closure();
    dbg!(&closure);

    let mut vm = Vm::new(closure);
    vm.run();
    dbg!(vm.stack);
}
