//! Symbol resolution.

use nopo_diagnostics::span::{spanned, Span, Spanned};
use nopo_diagnostics::{IntoReport, Report};

use nopo_parser::ast::{
    BinaryExpr, ConstructedType, Expr, FnType, Ident, IdentExpr, IfExpr, ItemId, LambdaExpr,
    LetExpr, LetId, LetItem, MatchExpr, Path, Pattern, TupleType, Type, TypeDef, TypeId, TypeItem,
    TypeParam,
};
use nopo_parser::lexer::BinOp;
use nopo_parser::visitor::{walk_expr, walk_let_item, walk_pattern, walk_type_item, Visitor};

use crate::db::{
    AdtSymbol, AdtVariant, Binding, BindingId, DataDef, Db, RecordSymbol, ResolvedBinding,
    ResolvedType, ResolvedTypePretty, TypeKind, TypeSymbol,
};

#[derive(Report)]
#[kind("error")]
#[message("unresolved type parameter `'{param}`")]
struct UnresolvedTypeParam {
    span: Span,
    #[label(message = "Type param `'{param}` not found in current scope")]
    param: Spanned<Ident>,
}

#[derive(Report)]
#[kind("error")]
#[message("unresolved type `{ty}`")]
struct UnresolvedType {
    span: Span,
    #[label(message = "Type `{ty}` not found in current scope")]
    ty: Spanned<Type>,
}

#[derive(Report)]
#[kind("error")]
#[message("unresolved binding `{ident}`")]
struct UnresolvedBinding {
    span: Span,
    #[label(message = "Binding `{ident}` not found in current scope")]
    ident: Spanned<Ident>,
}

#[derive(Report)]
#[kind("error")]
#[message("wrong number of type parameters for type `{ty}`")]
struct WrongNumberOfTypeParams {
    span: Span,
    #[label(
        message = "{expected} type parameter(s) expected but {found} found",
        order = 1
    )]
    ty: Spanned<Ident>,
    #[label(message = "`{ty}` defined here", order = 2)]
    def_site: Spanned<Ident>,
    expected: usize,
    found: usize,
}

#[derive(Report)]
#[kind("error")]
#[message("`{ty}` is not a kind")]
struct NotAKind<'a> {
    span: Span,
    #[label(message = "`{ty}` is a type, not a kind")]
    ty: Spanned<ResolvedTypePretty<'a>>,
}

#[derive(Report)]
#[kind("error")]
#[message("wrong number of arguments found for data-constructor `{ident}` in this pattern")]
struct WrongNumberOfArgsForDataConstructorInPattern {
    span: Span,
    #[label(message = "{expected} argument(s) expected but {found} found")]
    ident: Spanned<Ident>,
    expected: usize,
    found: usize,
}

#[derive(Report)]
#[kind("error")]
#[message("`{path}` is not a data-constructor")]
struct NotADataConstructor {
    span: Span,
    #[label(message = "Pattern match must be on a data-constructor")]
    path: Spanned<Path>,
}

/// AST pass for resolving symbols. Does not resolve record fields since that requires type
/// information.
#[derive(Debug)]
pub struct ResolveSymbols<'a> {
    db: &'a mut Db,

    /// Stack of current bindings in scope.
    bindings_stack: Vec<BindingId>,
    /// Stack of current types in scope.
    types_stack: Vec<(TypeSymbol, ResolvedType)>,
    /// Temporary state of current item being visited. This is used for creating implicit type
    /// params.
    current_item_id: Option<ItemId>,
}

#[derive(Clone, Copy)]
struct StackState {
    bindings_stack: usize,
    types_stack: usize,
}

impl<'a> ResolveSymbols<'a> {
    pub fn new(db: &'a mut Db) -> Self {
        Self {
            db,
            bindings_stack: Vec::new(),
            types_stack: Vec::new(),
            current_item_id: None,
        }
    }

    fn get_stack_state(&self) -> StackState {
        StackState {
            bindings_stack: self.bindings_stack.len(),
            types_stack: self.types_stack.len(),
        }
    }

    fn restore_stack_state(&mut self, state: StackState) {
        self.bindings_stack.truncate(state.bindings_stack);
        self.types_stack.truncate(state.types_stack);
    }

    fn resolve_type(&mut self, ty: &Spanned<Type>) -> ResolvedType {
        let resolved = self.resolve_type_inner(ty);
        let data_def = self.data_def_of_constructed(&resolved);
        let expected = self.num_of_ty_params(&resolved);
        if let ResolvedType::Constructed {
            constructor,
            arg: _,
        } = &resolved
        {
            let found = resolved.num_of_constructed();
            // Check that resolved is not a kind.
            match (expected, found) {
                (Some(expected), found) if expected == found => resolved,
                (Some(expected), found) => {
                    self.db.diagnostics.add(WrongNumberOfTypeParams {
                        span: ty.span(),
                        ty: data_def.unwrap().ident.clone().respan(ty.span()),
                        def_site: data_def.unwrap().ident.clone(),
                        expected,
                        found,
                    });
                    ResolvedType::Err
                }
                (None, _found) => {
                    self.db.diagnostics.add(NotAKind {
                        span: ty.span(),
                        ty: spanned(
                            ty.span(),
                            constructor.pretty(&self.db.types_map.items_by_id),
                        ),
                    });
                    ResolvedType::Err
                }
            }
        } else if let Some(expected) = expected {
            if expected != 0 {
                self.db.diagnostics.add(WrongNumberOfTypeParams {
                    span: ty.span(),
                    ty: data_def.unwrap().ident.clone().respan(ty.span()),
                    def_site: data_def.unwrap().ident.clone(),
                    expected,
                    found: 0,
                });
                ResolvedType::Err
            } else {
                resolved
            }
        } else {
            resolved
        }
    }

    /// Resolve a type or kind.
    fn resolve_type_inner(&mut self, ty: &Type) -> ResolvedType {
        // TODO: check modules
        match ty {
            Type::Path(ty) => self.resolve_path_type(ty),
            Type::Fn(Spanned(FnType { arg_ty, ret_ty }, _)) => ResolvedType::Fn {
                arg: Box::new(self.resolve_type(arg_ty)),
                ret: Box::new(self.resolve_type(ret_ty)),
            },
            Type::Tuple(Spanned(TupleType { fields }, _)) => {
                ResolvedType::Tuple(fields.iter().map(|ty| self.resolve_type(ty)).collect())
            }
            Type::Constructed(Spanned(ConstructedType { constructor, arg }, _)) => {
                ResolvedType::Constructed {
                    constructor: Box::new(self.resolve_type_inner(constructor)),
                    arg: Box::new(self.resolve_type(arg)),
                }
            }
            Type::Param(Spanned(TypeParam { ident }, span)) => {
                let symbol = TypeSymbol::Param(ident.as_ref().clone());
                if let Some(resolved) = self.try_resolve_type_symbol(&symbol) {
                    resolved
                } else if let Some(ItemId::Let(_)) = self.current_item_id {
                    // If we are inside a let, we can create type parameter implicitly.
                    let resolved = ResolvedType::Param(ident.as_ref().clone().into());
                    self.types_stack.push((symbol, resolved.clone()));
                    resolved
                } else {
                    self.db.diagnostics.add(UnresolvedTypeParam {
                        span: *span,
                        param: ident.clone(),
                    });
                    ResolvedType::Err
                }
            }
            Type::Err => unreachable!(),
        }
    }

    fn resolve_path_type(&self, ty: &Spanned<Path>) -> ResolvedType {
        if ty.path.len() != 1 {
            todo!("modules");
        }
        // Lookup type with name ty.path[0]
        if let Some(resolved) =
            self.try_resolve_type_symbol(&TypeSymbol::Path(ty.path[0].as_ref().clone()))
        {
            resolved
        } else {
            // TODO: do not hardcode built-in types in type resolution.
            match ty.path[0].to_string().as_str() {
                "bool" => ResolvedType::Bool,
                "int" => ResolvedType::Int,
                "float" => ResolvedType::Float,
                "string" => ResolvedType::String,
                "char" => ResolvedType::Char,
                _ => {
                    let mut report = UnresolvedType {
                        span: ty.span(),
                        ty: spanned(ty.span(), Type::Path(ty.clone())),
                    }
                    .into_report();
                    // Maybe confused with a binding?
                    if self.try_resolve_binding(&ty.path[0]).is_some() {
                        report.set_help("A binding with the same name exists in this scope");
                    }
                    self.db.diagnostics.add(report);
                    ResolvedType::Err
                }
            }
        }
    }

    /// Try to resolve a type symbol in the current scope.
    fn try_resolve_type_symbol(&self, symbol: &TypeSymbol) -> Option<ResolvedType> {
        if let Some((_, resolved)) = self.types_stack.iter().rev().find(|(x, _)| x == symbol) {
            Some(resolved.clone())
        } else {
            None
        }
    }

    /// Get the number of type parameters expected. If the type is not a constructed type of
    /// identifiers, returns `None`.
    fn num_of_ty_params(&self, ty: &ResolvedType) -> Option<usize> {
        self.data_def_of_constructed(ty)
            .map(|def| def.ty_params.len())
    }

    fn data_def_of_constructed(&self, ty: &ResolvedType) -> Option<&DataDef> {
        ty.ident_of_constructed()
            .map(|id| &self.db.types_map.items_by_id[id])
    }

    /// Create a new scope for a binding and return the created binding id.
    #[must_use = "binding should be saved to BindingsMap"]
    fn new_binding_scope(&mut self, binding: Binding) -> BindingId {
        let id = self.db.bindings.alloc(binding);
        self.bindings_stack.push(id);
        id
    }

    fn try_resolve_binding(&self, ident: &Spanned<Ident>) -> Option<BindingId> {
        for id in self.bindings_stack.iter().rev() {
            if self.db.bindings[*id].ident == **ident {
                return Some(*id);
            }
        }
        None
    }

    /// Resolve a binding in the current scope. If binding is not found, produces a diagnostic.
    fn resolve_binding(&self, ident: &Spanned<Ident>) -> ResolvedBinding {
        if let Some(id) = self.try_resolve_binding(ident) {
            return ResolvedBinding::Ok(id);
        }
        // Binding not found.
        let mut report = UnresolvedBinding {
            span: ident.span(),
            ident: ident.clone(),
        }
        .into_report();
        // Maybe confused with a type?
        if self
            .try_resolve_type_symbol(&TypeSymbol::Path(ident.as_ref().clone()))
            .is_some()
        {
            report.set_help("A type with the same name exists in this scope");
        }
        self.db.diagnostics.add(report);
        ResolvedBinding::Err
    }
}

impl Visitor for ResolveSymbols<'_> {
    fn visit_let_item(&mut self, idx: LetId, item: &Spanned<LetItem>) {
        self.current_item_id = Some(ItemId::Let(idx));
        // If no params, then this is a value instead of a function. Don't allow recursive values.
        if item.params.is_empty() {
            walk_let_item(self, item);
        }
        // Create binding for let item itself.
        let let_binding = self.new_binding_scope(Binding::new(item.ident.as_ref().clone()));
        self.db.bindings_map.let_items.insert(item, let_binding);
        // We want the environment to be restored to this state after the let item.
        let state = self.get_stack_state();
        // Create bindings for all params.
        for param in &item.params {
            let param_binding = self.new_binding_scope(Binding::new(param.ident.as_ref().clone()));
            self.db.bindings_map.params.insert(param, param_binding);
        }
        if !item.params.is_empty() {
            walk_let_item(self, item);
        }
        self.restore_stack_state(state);
        self.current_item_id = None;
    }

    fn visit_type_item(&mut self, idx: TypeId, item: &Spanned<TypeItem>) {
        self.current_item_id = Some(ItemId::Type(idx));
        // Create type for type item itself.
        let symbol = TypeSymbol::Path(item.ident.as_ref().clone());
        let resolved = ResolvedType::Data(idx);
        self.types_stack.push((symbol, resolved));

        // Create bindings for all ADT data constructors.
        if let TypeDef::Adt(adt) = &*item.def {
            for (tag, data_constructor) in adt.data_constructors.iter().enumerate() {
                let binding = self.new_binding_scope(Binding::new_data_constructor(
                    data_constructor.ident.as_ref().clone(),
                    data_constructor.of.len(),
                    tag as u32,
                ));
                self.db
                    .bindings_map
                    .data_constructors
                    .insert(data_constructor, binding);
            }
        }

        // We want the environment to be restored to this state after the type item.
        let state = self.get_stack_state();

        // Create type parameters.
        for ty_param in &item.ty_params {
            let symbol = TypeSymbol::Param(ty_param.ident.as_ref().clone());
            let resolved = ResolvedType::Param(ty_param.ident.as_ref().clone().into());
            self.types_stack.push((symbol, resolved));
        }

        // Create a temporary data def since we might access it while resolving the types of the
        // ADT data constructors.
        let data_def = DataDef {
            ident: item.ident.clone(),
            kind: TypeKind::Tmp,
            ty_params: item.ty_params.clone(),
            span: item.span(),
        };
        self.db.types_map.items_by_id.insert(idx, data_def);

        walk_type_item(self, item);

        // Update data def with updated information.
        let kind = match &*item.def {
            TypeDef::Adt(adt) => TypeKind::Adt(AdtSymbol {
                variants: adt
                    .data_constructors
                    .iter()
                    .map(|x| AdtVariant {
                        ident: x.ident.as_ref().clone(),
                        types: x
                            .of
                            .iter()
                            .map(|ty| self.db.types_map.types[ty].clone())
                            .collect(),
                    })
                    .collect(),
            }),
            TypeDef::Record(record) => TypeKind::Record(RecordSymbol {
                fields: record
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        (
                            field.ident.as_ref().clone(),
                            (self.db.types_map.types[&field.ty].clone(), i as u32),
                        )
                    })
                    .collect(),
            }),
            TypeDef::Err => unreachable!(),
        };
        self.db.types_map.items_by_id[idx].kind = kind;

        self.restore_stack_state(state);
        self.current_item_id = None;
    }

    fn visit_type(&mut self, ty: &Spanned<Type>) {
        let resolved = self.resolve_type(ty);
        self.db.types_map.types.insert(ty, resolved);
    }

    fn visit_expr(&mut self, expr: &Spanned<Expr>) {
        match &**expr {
            Expr::Let(Spanned(
                let_expr @ LetExpr {
                    ident,
                    ret_ty,
                    expr,
                    _in,
                },
                _,
            )) => {
                // We cannot access the binding inside the expression itself.
                self.visit_expr(expr);
                // Now we can add the binding.
                let binding = self.new_binding_scope(Binding::new(ident.as_ref().clone()));
                self.db.bindings_map.let_exprs.insert(let_expr, binding);

                self.visit_expr(_in);

                // Resolve the types of ret.
                if let Some(ret_ty) = ret_ty {
                    self.visit_type(ret_ty);
                }
            }
            Expr::Lambda(Spanned(LambdaExpr { params, expr }, _)) => {
                // Lambdas create a new scope.
                let state = self.get_stack_state();
                // Create bindings for all params.
                for param in params {
                    let binding =
                        self.new_binding_scope(Binding::new(param.ident.as_ref().clone()));
                    self.db.bindings_map.lambda_params.insert(param, binding);
                }

                self.visit_expr(expr);

                self.restore_stack_state(state);
            }
            Expr::Binary(Spanned(BinaryExpr { lhs, op, rhs: _ }, _)) if **op == BinOp::Dot => {
                // We only want to visit the LHS of a member access since the RHS will depend on
                // the type of the LHS.
                self.visit_expr(lhs);
            }
            Expr::If(Spanned(IfExpr { cond, then, else_ }, _)) => {
                self.visit_expr(cond);
                let state = self.get_stack_state();
                self.visit_expr(then);
                self.restore_stack_state(state);
                self.visit_expr(else_);
                self.restore_stack_state(state);
            }
            Expr::Match(Spanned(MatchExpr { matched, arms }, _)) => {
                self.visit_expr(matched);
                for arm in arms {
                    let state = self.get_stack_state();
                    // Create bindings for all match arms.
                    self.visit_pattern(&arm.pattern);
                    self.visit_expr(&arm.expr);
                    self.restore_stack_state(state);
                }
            }
            Expr::Ident(Spanned(ident_expr @ IdentExpr { ident }, _)) => {
                // Lookup the binding for this ident.
                let resolved_binding = self.resolve_binding(ident);
                self.db
                    .bindings_map
                    .idents
                    .insert(ident_expr, resolved_binding);
            }
            _ => walk_expr(self, expr),
        }
    }

    fn visit_pattern(&mut self, pattern: &Spanned<Pattern>) {
        match &**pattern {
            Pattern::Path(path) => {
                match &path.path[..] {
                    [ident] => {
                        // Try to resolve this as a data-constructor. If not, then create a new
                        // binding.
                        match self.try_resolve_binding(ident) {
                            Some(symbol) if self.db.bindings[symbol].is_data_constructor => {
                                // Make sure that we have the right number of args.
                                let expected = self.db.bindings[symbol].data_constructor_args;
                                if expected != 0 {
                                    self.db.diagnostics.add(
                                        WrongNumberOfArgsForDataConstructorInPattern {
                                            span: ident.span(),
                                            ident: ident.clone(),
                                            expected,
                                            found: 0,
                                        },
                                    );
                                }
                                self.db
                                    .bindings_map
                                    .pattern_tags
                                    .insert(pattern, ResolvedBinding::Ok(symbol));
                            }
                            _ => {
                                let binding =
                                    self.new_binding_scope(Binding::new(ident.as_ref().clone()));
                                self.db.bindings_map.pattern.insert(pattern, binding);
                            }
                        }
                    }
                    _ => todo!("modules"),
                }
            }
            Pattern::Adt(adt) => match &adt.tag.path[..] {
                [ident] => {
                    let symbol = self.resolve_binding(ident);
                    if let ResolvedBinding::Ok(symbol) = symbol {
                        if !self.db.bindings[symbol].is_data_constructor {
                            self.db.diagnostics.add(NotADataConstructor {
                                span: ident.span(),
                                path: adt.tag.clone(),
                            })
                        }
                        // Make sure that we have the right number of args.
                        let expected = self.db.bindings[symbol].data_constructor_args;
                        if expected != adt.of.len() {
                            self.db
                                .diagnostics
                                .add(WrongNumberOfArgsForDataConstructorInPattern {
                                    span: ident.span(),
                                    ident: ident.clone(),
                                    expected,
                                    found: adt.of.len(),
                                });
                        }
                    }
                    self.db.bindings_map.pattern_tags.insert(pattern, symbol);
                }
                _ => todo!("modules"),
            },
            Pattern::Lit(_) => {}
            Pattern::Err => {}
        }
        walk_pattern(self, pattern);
    }
}

#[cfg(test)]
mod tests {
    use expect_test::expect;

    use crate::tests::{check, check_fail};

    #[test]
    fn resolve_let_items() {
        check(
            "let a = 1
             let b = a
             let c = b",
        );
    }

    #[test]
    fn unresolved_binding() {
        check_fail(
            "let a = unknown",
            expect![[r#"
                Error: unresolved binding `unknown`
                   ╭─[<test>:1:9]
                   │
                 1 │ let a = unknown
                   │         ───┬───  
                   │            ╰───── Binding `unknown` not found in current scope
                ───╯
            "#]],
        );
        check_fail(
            "let x = x",
            expect![[r#"
                Error: unresolved binding `x`
                   ╭─[<test>:1:9]
                   │
                 1 │ let x = x
                   │         ┬  
                   │         ╰── Binding `x` not found in current scope
                ───╯
            "#]],
        );
    }

    #[test]
    fn adt_data_constructors() {
        check(
            "type List 'a = Nil | Cons of 'a (List 'a)
             let my_list = Cons 1 (Cons 2 (Cons 3 Nil))",
        );
    }

    #[test]
    fn wrong_number_of_type_params() {
        check_fail(
            "type Foo 'a 'b = Foo of 'a 'b
             let foo1: Foo int int int = Foo 1 2
             let foo2: Foo = Foo 1 2",
            expect![[r#"
                Error: wrong number of type parameters for type `Foo`
                   ╭─[<test>:2:24]
                   │
                 1 │ type Foo 'a 'b = Foo of 'a 'b
                   │      ─┬─  
                   │       ╰─── `Foo` defined here
                 2 │              let foo1: Foo int int int = Foo 1 2
                   │                        ───────┬───────  
                   │                               ╰───────── 2 type parameter(s) expected but 3 found
                ───╯
                Error: wrong number of type parameters for type `Foo`
                   ╭─[<test>:3:24]
                   │
                 1 │ type Foo 'a 'b = Foo of 'a 'b
                   │      ─┬─  
                   │       ╰─── `Foo` defined here
                   │ 
                 3 │              let foo2: Foo = Foo 1 2
                   │                        ─┬─  
                   │                         ╰─── 2 type parameter(s) expected but 0 found
                ───╯
            "#]],
        );
        check_fail(
            "type Foo = Foo
             let foo: Foo int = Foo",
            expect![[r#"
                Error: wrong number of type parameters for type `Foo`
                   ╭─[<test>:2:23]
                   │
                 1 │ type Foo = Foo
                   │      ─┬─  
                   │       ╰─── `Foo` defined here
                 2 │              let foo: Foo int = Foo
                   │                       ───┬───  
                   │                          ╰───── 0 type parameter(s) expected but 1 found
                ───╯
            "#]],
        );
        check_fail(
            "let x: int int = 1",
            expect![[r#"
                Error: `int` is not a kind
                   ╭─[<test>:1:8]
                   │
                 1 │ let x: int int = 1
                   │        ───┬───  
                   │           ╰───── `int` is a type, not a kind
                ───╯
            "#]],
        );
    }

    #[test]
    fn unresolved_type() {
        check_fail(
            "let x: UnknownType = 1",
            expect![[r#"
                Error: unresolved type `UnknownType`
                   ╭─[<test>:1:8]
                   │
                 1 │ let x: UnknownType = 1
                   │        ─────┬─────  
                   │             ╰─────── Type `UnknownType` not found in current scope
                ───╯
            "#]],
        );
    }

    #[test]
    fn unresolved_type_param() {
        check_fail(
            "type Foo = Foo of 'a",
            expect![[r#"
                Error: unresolved type parameter `'a`
                   ╭─[<test>:1:19]
                   │
                 1 │ type Foo = Foo of 'a
                   │                    ┬  
                   │                    ╰── Type param `'a` not found in current scope
                ───╯
            "#]],
        );
    }
}
