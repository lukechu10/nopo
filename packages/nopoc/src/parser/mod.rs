use std::ops::Range;

use la_arena::Arena;
use logos::Logos;
use nopo_diagnostics::span::{spanned, FileId, Span, Spanned};
use nopo_diagnostics::{Diagnostics, Report};
use smol_str::SmolStr;

use self::lexer::{BinOp, PostfixOp, Token, TypeBinOp, UnaryOp};
use crate::ast::*;

pub mod lexer;
#[cfg(test)]
mod tests;

pub struct Parser {
    /// All the tokens.
    tokens: Vec<(Token, Range<usize>)>,
    /// An index into `tokens`, representing the current token.
    /// Initially 0, and incremented by `next_token` after each token is consumed.
    ///
    /// The first token is a dummy token, so when calling `get_next` for the first time, the first
    /// real token is returned.
    cursor: usize,
    /// The current file that is being parsed.
    file_id: FileId,
    diagnostics: Diagnostics,
}

#[derive(Report)]
#[kind("error")]
#[message("expected one of {expected:?}, found {unexpected}")]
struct UnexpectedToken {
    span: Span,
    expected: Vec<Token>,
    #[label(message = "unexpected token")]
    unexpected: Spanned<Token>,
}

#[derive(Report)]
#[kind("error")]
#[message("expected an item, found {unexpected}")]
struct ExpectedItem {
    span: Span,
    #[label(message = "unexpected token")]
    unexpected: Spanned<Token>,
}

#[derive(Report)]
#[kind("error")]
#[message("expected an expression, found {unexpected}")]
struct ExpectedExpr {
    span: Span,
    #[label(message = "unexpected token")]
    unexpected: Spanned<Token>,
}

#[derive(Report)]
#[kind("error")]
#[message("expected a type, found {unexpected}")]
struct ExpectedType {
    span: Span,
    #[label(message = "unexpected token")]
    unexpected: Spanned<Token>,
}

#[derive(Report)]
#[kind("error")]
#[message("expected a type definition, found {unexpected}")]
struct ExpectedTypeDef {
    span: Span,
    #[label(message = "unexpected token")]
    unexpected: Spanned<Token>,
}

#[derive(Report)]
#[kind("error")]
#[message("invalid char literal")]
struct InvalidCharLiteral {
    span: Span,
    #[label(message = "char literal should only contain one character")]
    char: Spanned<String>,
}

/// A temporary struct used to store the start of a span.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SpanStart {
    start: u32,
}

impl Parser {
    pub fn new(file_id: FileId, source: &str, diagnostics: Diagnostics) -> Self {
        let tokens = Some((Token::Start, 0..0))
            .into_iter()
            .chain(Token::lexer(source).spanned())
            .collect();
        Self {
            tokens,
            cursor: 0,
            file_id,
            diagnostics,
        }
    }

    pub fn eof(&self) -> bool {
        self.peek_next() == &Token::Eof
    }

    /// Returns a `SpanStart` that can be used to create a `Span` later.
    #[must_use]
    fn start(&self) -> SpanStart {
        // If we are starting at the end of file, get the last position of the last token.
        let last = self.tokens.last().map(|last| last.1.end).unwrap_or(0);
        let start = self
            .tokens
            .get(self.cursor + 1)
            .map(|x| x.1.start)
            .unwrap_or(last) as u32;
        SpanStart { start }
    }

    /// Returns a `Span` from a `SpanStart`.
    #[must_use]
    fn end(&self, start: SpanStart) -> Span {
        let end = self
            .tokens
            .get(self.cursor)
            .map(|x| x.1.end as u32)
            .unwrap_or(start.start);
        Span {
            start: start.start,
            end,
            file_id: self.file_id,
        }
    }

    #[must_use]
    fn finish<T>(&self, start: SpanStart, node: T) -> Spanned<T> {
        spanned(self.end(start), node)
    }

    fn peek_span(&self) -> Span {
        let start = self.start();
        let end = self
            .tokens
            .get(self.cursor + 1)
            .map(|x| x.1.end as u32)
            .unwrap_or(start.start);
        Span {
            start: start.start,
            end,
            file_id: self.file_id,
        }
    }

    /// Get the current token.
    #[must_use]
    pub fn get_current(&self) -> &Token {
        self.tokens
            .get(self.cursor)
            .map(|x| &x.0)
            .unwrap_or(&Token::Eof)
    }

    /// Get the next token and increments the cursor.
    #[must_use]
    pub fn get_next(&mut self) -> &Token {
        self.cursor += 1;
        self.tokens
            .get(self.cursor)
            .map(|x| &x.0)
            .unwrap_or(&Token::Eof)
    }

    /// Get the next token without incrementing the cursor.
    #[must_use]
    pub fn peek_next(&self) -> &Token {
        self.tokens
            .get(self.cursor + 1)
            .map(|x| &x.0)
            .unwrap_or(&Token::Eof)
    }

    /// Get the token that is `n` tokens ahead without incrementing the cursor.
    /// If `n` is 0, this is equivalent to `get_current`.
    /// If `n` is 1, this is equivalent to `peek_next`.
    ///
    /// If `n` is greater than the number of tokens left, [`Token::Eof`] is returned.
    pub fn peek_nth(&self, n: usize) -> &Token {
        self.tokens
            .get(self.cursor + n)
            .map(|x| &x.0)
            .unwrap_or(&Token::Eof)
    }

    /// Get the next token and expect it to be the same token as `expected`.
    ///
    /// This will always consume a token even if there is a mismatch so as to prevent error
    /// recovery loop.
    pub fn expect(&mut self, expected: Token) {
        let start = self.start();
        if self.get_next() != &expected {
            self.diagnostics.add(UnexpectedToken {
                span: self.end(start),
                expected: vec![expected.clone()],
                unexpected: self.finish(start, self.get_current().clone()),
            });
        }
    }

    /// Create a [`ParseError::UnexpectedToken`] error with the next token as the unexpected token.
    pub fn unexpected(&self, expected: Vec<Token>) {
        self.diagnostics.add(UnexpectedToken {
            span: self.peek_span(),
            expected,
            unexpected: spanned(self.peek_span(), self.peek_next().clone()),
        });
    }

    pub fn parse_root(&mut self) -> Root {
        let mut let_items = Arena::new();
        let mut type_items = Arena::new();
        let mut items = Vec::new();
        let mut mod_items = Vec::new();
        let mut use_items = Vec::new();
        while !self.eof() {
            let attrs = self.parse_attributes();
            // If we see a visibility keyword, look at the token after that to decide which branch
            // to parse.
            let kw = match self.peek_next() {
                Token::KwPub => self.peek_nth(2),
                x => x,
            };
            match kw {
                Token::KwLet => {
                    let item = self.parse_let_item(attrs);
                    let id = let_items.alloc(item);
                    items.push(ItemId::Let(id));
                }
                Token::KwType => {
                    let item = self.parse_type_item(attrs);
                    let id = type_items.alloc(item);
                    items.push(ItemId::Type(id));
                }
                Token::KwMod => {
                    let item = self.parse_mod_item(attrs);
                    mod_items.push(item);
                }
                Token::KwUse => {
                    let item = self.parse_use_item(attrs);
                    use_items.push(item);
                }
                _ => {
                    self.diagnostics.add(ExpectedItem {
                        span: self.peek_span(),
                        unexpected: spanned(self.peek_span(), self.peek_next().clone()),
                    });
                    let _ = self.get_next(); // TODO: better error recovery
                }
            }
        }
        Root {
            let_items,
            type_items,
            items,
            mod_items,
            use_items,
        }
    }

    pub fn parse_attributes(&mut self) -> Spanned<Attributes> {
        let start = self.start();
        let mut attrs = Vec::new();
        while self.peek_next() == &Token::LBracket {
            attrs.push(self.parse_attribute());
        }
        self.finish(start, Attributes { attrs })
    }

    pub fn parse_attribute(&mut self) -> Spanned<Attribute> {
        let start = self.start();
        self.expect(Token::LBracket);
        let ident = self.parse_ident();
        self.expect(Token::RBracket);
        self.finish(start, Attribute { ident })
    }

    pub fn parse_vis(&mut self) -> Spanned<Vis> {
        let start = self.start();
        let vis = match self.peek_next() {
            Token::KwPub => {
                let _ = self.get_next();
                Vis::Pub
            }
            _ => Vis::Priv,
        };
        self.finish(start, vis)
    }

    pub fn parse_let_item(&mut self, attrs: Spanned<Attributes>) -> Spanned<LetItem> {
        let start = self.start();
        let vis = self.parse_vis();
        self.expect(Token::KwLet);
        let ident = self.parse_ident();

        let mut params = Vec::new();
        while let Token::LParen | Token::Ident(_) = self.peek_next() {
            params.push(self.parse_param());
        }

        let ret_ty = if self.peek_next() == &Token::Colon {
            self.expect(Token::Colon);
            Some(self.parse_type())
        } else {
            None
        };

        self.expect(Token::Eq);
        let expr = self.parse_expr();

        self.finish(
            start,
            LetItem {
                attrs,
                vis,
                ident,
                ret_ty,
                params,
                expr: Box::new(expr),
            },
        )
    }

    pub fn parse_param(&mut self) -> Spanned<Param> {
        let start = self.start();
        if self.peek_next() == &Token::LParen {
            self.expect(Token::LParen);
            let ident = self.parse_ident();
            self.expect(Token::Colon);
            let ty = self.parse_type();
            self.expect(Token::RParen);
            self.finish(
                start,
                Param {
                    ident,
                    ty: Some(ty),
                },
            )
        } else {
            let ident = self.parse_ident();
            self.finish(start, Param { ident, ty: None })
        }
    }

    pub fn parse_type_item(&mut self, attrs: Spanned<Attributes>) -> Spanned<TypeItem> {
        let start = self.start();
        let vis = self.parse_vis();
        self.expect(Token::KwType);
        let ident = self.parse_ident();
        let mut ty_params = Vec::new();
        while self.peek_next() == &Token::Prime {
            ty_params.push(self.parse_type_param());
        }
        self.expect(Token::Eq);
        let def = self.parse_type_def();
        self.finish(
            start,
            TypeItem {
                attrs,
                vis,
                ident,
                ty_params,
                def,
            },
        )
    }

    pub fn parse_type_param(&mut self) -> Spanned<TypeParam> {
        let start = self.start();
        self.expect(Token::Prime);
        let ident = self.parse_ident();
        self.finish(start, TypeParam { ident })
    }

    pub fn parse_type_def(&mut self) -> Spanned<TypeDef> {
        let start = self.start();
        match self.peek_next() {
            Token::LBrace => {
                let def = self.parse_record_def();
                self.finish(start, TypeDef::Record(def))
            }
            Token::Ident(_) => {
                let def = self.parse_adt_def();
                self.finish(start, TypeDef::Adt(def))
            }
            token => {
                self.diagnostics.add(ExpectedTypeDef {
                    span: self.peek_span(),
                    unexpected: spanned(self.peek_span(), token.clone()),
                });
                let _ = self.get_next();
                self.finish(start, TypeDef::Err)
            }
        }
    }

    pub fn parse_record_def(&mut self) -> Spanned<RecordDef> {
        let start = self.start();
        self.expect(Token::LBrace);

        let mut fields = Vec::new();
        while let Token::Ident(_) = self.peek_next() {
            fields.push(self.parse_record_field());
            if self.peek_next() != &Token::Comma {
                break;
            } else {
                self.expect(Token::Comma);
            }
        }

        self.expect(Token::RBrace);

        self.finish(start, RecordDef { fields })
    }

    pub fn parse_record_type(&mut self) -> Spanned<RecordDef> {
        let start = self.start();
        self.expect(Token::LBrace);

        let mut fields = Vec::new();
        while let Token::Ident(_) = self.peek_next() {
            fields.push(self.parse_record_field());
        }

        self.expect(Token::RBrace);

        self.finish(start, RecordDef { fields })
    }

    pub fn parse_record_field(&mut self) -> Spanned<RecordField> {
        let start = self.start();
        let ident = self.parse_ident();
        self.expect(Token::Colon);
        let ty = self.parse_type();
        self.finish(
            start,
            RecordField {
                ident,
                ty: Box::new(ty),
            },
        )
    }

    pub fn parse_adt_def(&mut self) -> Spanned<AdtDef> {
        let start = self.start();
        let first = self.parse_data_constructor();
        let mut data_constructors = vec![first];
        while self.peek_next() == &Token::Or {
            self.expect(Token::Or);
            data_constructors.push(self.parse_data_constructor());
        }

        self.finish(start, AdtDef { data_constructors })
    }

    pub fn parse_data_constructor(&mut self) -> Spanned<DataConstructor> {
        let start = self.start();
        let ident = self.parse_ident();
        let of = if self.peek_next() == &Token::KwOf {
            self.expect(Token::KwOf);
            let mut of = Vec::new();
            while self.peek_is_type() {
                of.push(self.parse_primary_type());
            }
            of
        } else {
            Vec::new()
        };

        self.finish(start, DataConstructor { ident, of })
    }

    pub fn parse_type(&mut self) -> Spanned<Type> {
        self.parse_type_with_min_bp(0)
    }

    pub fn peek_is_type(&mut self) -> bool {
        matches!(
            self.peek_next(),
            Token::Ident(_) | Token::LParen | Token::Prime
        )
    }

    pub fn parse_primary_type(&mut self) -> Spanned<Type> {
        let start = self.start();
        match self.peek_next() {
            Token::LParen => {
                self.expect(Token::LParen);
                if self.peek_next() == &Token::RParen {
                    // Empty tuple
                    self.expect(Token::RParen);
                    self.finish(
                        start,
                        Type::Tuple(self.finish(start, TupleType { fields: Vec::new() })),
                    )
                } else {
                    let ty = self.parse_type();
                    if self.peek_next() == &Token::Comma {
                        // Parse a tuple.
                        self.expect(Token::Comma);
                        let mut fields = vec![ty];
                        while self.peek_is_type() {
                            fields.push(self.parse_type());
                        }
                        self.expect(Token::RParen);
                        self.finish(start, Type::Tuple(self.finish(start, TupleType { fields })))
                    } else {
                        // This is just a parenthesized type.
                        self.expect(Token::RParen);
                        ty
                    }
                }
            }
            Token::Ident(_) => {
                let path = self.parse_path_type();
                self.finish(start, Type::Path(path))
            }
            Token::Prime => {
                let ty = self.parse_type_param();
                self.finish(start, Type::Param(ty))
            }
            _ => {
                self.diagnostics.add(ExpectedType {
                    span: self.peek_span(),
                    unexpected: spanned(self.peek_span(), self.peek_next().clone()),
                });
                let _ = self.get_next(); // TODO: better error recovery
                self.finish(start, Type::Err)
            }
        }
    }

    pub fn parse_type_with_min_bp(&mut self, min_bp: u32) -> Spanned<Type> {
        let start = self.start();
        let mut lhs = self.parse_primary_type();

        loop {
            let op = if self.peek_next() == &Token::RArrow {
                TypeBinOp::Fn
            } else if self.peek_is_type() {
                TypeBinOp::Apply
            } else {
                break;
            };

            let (l_bp, r_bp) = op.binding_power();
            if l_bp < min_bp {
                break;
            }
            if op == TypeBinOp::Fn {
                self.expect(Token::RArrow);
            }

            let rhs = self.parse_type_with_min_bp(r_bp);
            lhs = match op {
                TypeBinOp::Apply => self.finish(
                    start,
                    Type::Constructed(self.finish(
                        start,
                        ConstructedType {
                            constructor: Box::new(lhs),
                            arg: Box::new(rhs),
                        },
                    )),
                ),
                TypeBinOp::Fn => self.finish(
                    start,
                    Type::Fn(self.finish(
                        start,
                        FnType {
                            arg_ty: Box::new(lhs),
                            ret_ty: Box::new(rhs),
                        },
                    )),
                ),
            }
        }

        lhs
    }

    pub fn parse_path_type(&mut self) -> Spanned<PathType> {
        let start = self.start();
        let initial = self.parse_ident();
        let mut path = vec![initial];
        while self.peek_next() == &Token::Dot {
            self.expect(Token::Dot);
            path.push(self.parse_ident());
        }

        self.finish(start, PathType { path })
    }

    pub fn parse_expr(&mut self) -> Spanned<Expr> {
        match self.peek_next() {
            Token::KwLet => {
                let start = self.start();
                let expr = self.parse_let_expr();
                self.finish(start, Expr::Let(expr))
            }
            _ => self.parse_expr_with_min_bp(0),
        }
    }

    pub fn peek_is_primary_expr(&self) -> bool {
        match self.peek_next() {
            Token::Ident(_)
            | Token::LBrace
            | Token::LParen
            | Token::BackSlash
            | Token::LitTrue
            | Token::LitFalse
            | Token::LitFloat(_)
            | Token::LitInt(_)
            | Token::LitStr(_)
            | Token::LitChar(_)
            | Token::KwIf
            | Token::KwFor
            | Token::KwWhile
            | Token::KwLoop
            | Token::KwReturn => true,
            tok if UnaryOp::try_from(tok.clone()).is_ok() => true,
            _ => false,
        }
    }

    pub fn parse_primary_expr(&mut self) -> Spanned<Expr> {
        let start = self.start();
        match self.peek_next() {
            Token::Ident(_) => {
                let ident = self.parse_ident();
                self.finish(start, Expr::Ident(self.finish(start, IdentExpr { ident })))
            }
            Token::LBrace => {
                // We need to check if this is a block expression or record expression.
                match (self.peek_nth(2), self.peek_nth(3)) {
                    (Token::Ident(_), Token::Eq) => {
                        let record_expr = self.parse_record_expr();
                        self.finish(start, Expr::Record(record_expr))
                    }
                    _ => {
                        let block = self.parse_block_expr();
                        self.finish(start, Expr::Block(block))
                    }
                }
            }
            Token::BackSlash => {
                let expr = self.parse_lambda_expr();
                self.finish(start, Expr::Lambda(expr))
            }
            Token::LParen => self.parse_tuple_expr(),
            Token::LitTrue => {
                let _ = self.get_next();
                self.finish(start, Expr::LitBool(true))
            }
            Token::LitFalse => {
                let _ = self.get_next();
                self.finish(start, Expr::LitBool(false))
            }
            Token::LitInt(int) => {
                let int = *int;
                let _ = self.get_next();
                self.finish(start, Expr::LitInt(int))
            }
            Token::LitFloat(float) => {
                let float = float.clone();
                let _ = self.get_next();
                self.finish(start, Expr::LitFloat(float))
            }
            Token::LitStr(str) => {
                let str = str.clone();
                let _ = self.get_next();
                self.finish(start, Expr::LitStr(str))
            }
            Token::LitChar(str) => {
                let str = str.clone();
                let _ = self.get_next();
                let mut chars = str.chars(); // TODO: escape codes
                if let Some(char) = chars.next() {
                    if chars.next().is_none() {
                        return self.finish(start, Expr::LitChar(char));
                    }
                }
                self.diagnostics.add(InvalidCharLiteral {
                    span: self.end(start),
                    char: self.finish(start, str),
                });
                self.finish(start, Expr::Err)
            }
            Token::KwIf => {
                let expr = self.parse_if_expr();
                self.finish(start, Expr::If(expr))
            }
            Token::KwFor => {
                let expr = self.parse_for_expr();
                self.finish(start, Expr::For(expr))
            }
            Token::KwWhile => {
                let expr = self.parse_while_expr();
                self.finish(start, Expr::While(expr))
            }
            Token::KwLoop => {
                let expr = self.parse_loop_expr();
                self.finish(start, Expr::Loop(expr))
            }
            Token::KwReturn => {
                let expr = self.parse_return_expr();
                self.finish(start, Expr::Return(expr))
            }
            tok if UnaryOp::try_from(tok.clone()).is_ok() => {
                let start = self.start();
                let op = UnaryOp::try_from(tok.clone()).unwrap();
                let op = self.finish(start, op);
                let _ = self.get_next();
                let expr = self.parse_expr();
                self.finish(
                    start,
                    Expr::Unary(self.finish(
                        start,
                        UnaryExpr {
                            op,
                            expr: Box::new(expr),
                        },
                    )),
                )
            }
            _ => {
                self.diagnostics.add(ExpectedExpr {
                    span: self.peek_span(),
                    unexpected: spanned(self.peek_span(), self.peek_next().clone()),
                });
                let _ = self.get_next(); // TODO: better error recovery
                self.finish(start, Expr::Err)
            }
        }
    }

    pub fn parse_expr_with_min_bp(&mut self, min_bp: u32) -> Spanned<Expr> {
        let start = self.start();
        let mut lhs = self.parse_primary_expr();

        loop {
            // Postfix operator.
            if let Ok(postfix) = self.peek_next().clone().try_into() {
                let postfix: PostfixOp = postfix;
                let (l_bp, ()) = postfix.binding_power();
                if l_bp < min_bp {
                    break;
                }
                match postfix {
                    PostfixOp::Index => {
                        self.expect(Token::LBracket);
                        let index = self.parse_expr();
                        self.expect(Token::RBracket);
                        lhs = self.finish(
                            start,
                            Expr::Index(self.finish(
                                start,
                                IndexExpr {
                                    lhs: Box::new(lhs),
                                    index: Box::new(index),
                                },
                            )),
                        );
                    }
                }
            }

            // Binary operator.
            let bin_op_start = self.start();
            let bin_op: BinOp = match self.peek_next().clone().try_into() {
                Ok(op) => op,
                Err(_) if self.peek_is_primary_expr() => BinOp::FnCall,
                Err(_) => break,
            };
            let (l_bp, r_bp) = bin_op.binding_power();
            if l_bp < min_bp {
                break;
            }

            // Consume the operator.
            if bin_op != BinOp::FnCall {
                let _ = self.get_next();
            }
            let bin_op = self.finish(bin_op_start, bin_op);

            // Parse RHS.
            let rhs = self.parse_expr_with_min_bp(r_bp);
            lhs = self.finish(
                start,
                Expr::Binary(self.finish(
                    start,
                    BinaryExpr {
                        lhs: Box::new(lhs),
                        op: bin_op,
                        rhs: Box::new(rhs),
                    },
                )),
            );
        }

        lhs
    }

    pub fn parse_block_expr(&mut self) -> Spanned<BlockExpr> {
        let start = self.start();
        self.expect(Token::LBrace);

        let mut exprs = Vec::new();
        while self.peek_next() != &Token::RBrace {
            exprs.push(self.parse_expr());
        }
        self.expect(Token::RBrace);
        self.finish(start, BlockExpr { exprs })
    }

    pub fn parse_lambda_expr(&mut self) -> Spanned<LambdaExpr> {
        let start = self.start();
        self.expect(Token::BackSlash);

        let mut params = Vec::new();
        while self.peek_next() != &Token::Eq {
            let start = self.start();
            let param = LambdaParam {
                ident: self.parse_ident(),
            };
            params.push(self.finish(start, param));
        }
        self.expect(Token::Eq);
        let expr = self.parse_expr();
        self.finish(
            start,
            LambdaExpr {
                params,
                expr: Box::new(expr),
            },
        )
    }

    pub fn parse_tuple_expr(&mut self) -> Spanned<Expr> {
        let start = self.start();
        self.expect(Token::LParen);
        let mut elements = Vec::new();
        while self.peek_is_primary_expr() {
            elements.push(self.parse_expr());
            if self.peek_next() != &Token::Comma {
                break;
            } else {
                self.expect(Token::Comma);
            }
        }
        self.expect(Token::RParen);
        match elements.len() {
            1 => elements.into_iter().next().unwrap(),
            _ => self.finish(
                start,
                Expr::Tuple(self.finish(start, TupleExpr { elements })),
            ),
        }
    }

    pub fn parse_record_expr(&mut self) -> Spanned<RecordExpr> {
        let start = self.start();
        self.expect(Token::LBrace);
        let mut fields = Vec::new();
        while let Token::Ident(_) = self.peek_next() {
            fields.push(self.parse_record_field_expr());
            if self.peek_next() != &Token::Comma {
                break;
            } else {
                self.expect(Token::Comma);
            }
        }
        self.expect(Token::RBrace);
        self.finish(start, RecordExpr { fields })
    }

    pub fn parse_record_field_expr(&mut self) -> Spanned<RecordFieldExpr> {
        let start = self.start();
        let ident = self.parse_ident();
        self.expect(Token::Eq);
        let expr = self.parse_expr();
        self.finish(start, RecordFieldExpr { ident, expr })
    }

    pub fn parse_if_expr(&mut self) -> Spanned<IfExpr> {
        let start = self.start();
        self.expect(Token::KwIf);
        let cond = self.parse_expr();
        self.expect(Token::KwThen);
        let then = self.parse_expr();
        self.expect(Token::KwElse);
        let else_ = self.parse_expr();
        self.finish(
            start,
            IfExpr {
                cond: Box::new(cond),
                then: Box::new(then),
                else_: Box::new(else_),
            },
        )
    }

    pub fn parse_while_expr(&mut self) -> Spanned<WhileExpr> {
        let start = self.start();
        self.expect(Token::KwWhile);
        let cond = self.parse_expr();
        let body = self.parse_block_expr();
        let body = Box::new(spanned(body.span(), Expr::Block(body)));
        self.finish(
            start,
            WhileExpr {
                cond: Box::new(cond),
                body,
            },
        )
    }

    pub fn parse_for_expr(&mut self) -> Spanned<ForExpr> {
        let start = self.start();
        self.expect(Token::KwFor);
        let binding = self.parse_binding();
        self.expect(Token::KwIn);
        let iter = self.parse_expr();
        let body = self.parse_block_expr();
        let body = Box::new(spanned(body.span(), Expr::Block(body)));
        self.finish(
            start,
            ForExpr {
                binding,
                iter: Box::new(iter),
                body,
            },
        )
    }

    pub fn parse_loop_expr(&mut self) -> Spanned<LoopExpr> {
        let start = self.start();
        self.expect(Token::KwLoop);
        let body = self.parse_block_expr();
        let body = Box::new(spanned(body.span(), Expr::Block(body)));
        self.finish(start, LoopExpr { body })
    }

    pub fn parse_return_expr(&mut self) -> Spanned<ReturnExpr> {
        let start = self.start();
        self.expect(Token::KwReturn);
        let expr = self.parse_expr();
        self.finish(
            start,
            ReturnExpr {
                expr: Box::new(expr),
            },
        )
    }

    pub fn parse_let_expr(&mut self) -> Spanned<LetExpr> {
        let start = self.start();
        self.expect(Token::KwLet);
        let ident = self.parse_ident();

        let ret_ty = if self.peek_next() == &Token::Colon {
            self.expect(Token::Colon);
            Some(self.parse_type())
        } else {
            None
        };

        self.expect(Token::Eq);
        let expr = self.parse_expr();

        self.expect(Token::KwIn);
        let _in = self.parse_expr();

        self.finish(
            start,
            LetExpr {
                ident,
                ret_ty,
                expr: Box::new(expr),
                _in: Box::new(_in),
            },
        )
    }

    pub fn parse_mod_item(&mut self, attrs: Spanned<Attributes>) -> Spanned<ModItem> {
        let start = self.start();
        let vis = self.parse_vis();
        self.expect(Token::KwMod);
        let ident = self.parse_ident();
        self.finish(start, ModItem { attrs, vis, ident })
    }

    pub fn parse_use_item(&mut self, attrs: Spanned<Attributes>) -> Spanned<UseItem> {
        let start = self.start();
        let vis = self.parse_vis();
        self.expect(Token::KwUse);
        let path = self.parse_ident();
        self.finish(start, UseItem { attrs, vis, path })
    }

    /// Try to parse an identifier. Will consume a token even in the case of mismatch.
    pub fn parse_ident(&mut self) -> Spanned<Ident> {
        let start = self.start();
        let next = self.get_next().clone();
        if let Token::Ident(ident) = next {
            self.finish(start, Ident::Ok(SmolStr::new(ident)))
        } else {
            self.diagnostics.add(UnexpectedToken {
                span: self.end(start),
                expected: vec![Token::Ident("".to_string())],
                unexpected: self.finish(start, next),
            });
            self.finish(start, Ident::Err)
        }
    }

    pub fn parse_binding(&mut self) -> Spanned<Binding> {
        let start = self.start();
        let ident = self.parse_ident();
        let ty = if self.peek_next() == &Token::Colon {
            let _ = self.get_next();
            Some(self.parse_ident())
        } else {
            None
        };
        self.finish(start, Binding { ident, ty })
    }
}
