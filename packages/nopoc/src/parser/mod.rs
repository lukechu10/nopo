use std::ops::Range;

use logos::Logos;
use thiserror::Error;

use crate::ast::*;
use crate::span::{spanned, FileId, Span, Spanned};

use self::lexer::{BinOp, PostfixOp, Token, UnaryOp};

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
}

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("expected one of: {expected:?}, found {unexpected:?}.")]
    ExpectedToken {
        unexpected: Token,
        expected: Vec<Token>,
    },
    #[error("expected an item, found {unexpected:?}.")]
    ExpectedItem { unexpected: Token },
    #[error("expected an expression, found {unexpected:?}.")]
    ExpectedExpr { unexpected: Token },
    #[error("expected a type, found {unexpected:?}.")]
    ExpectedType { unexpected: Token },
    #[error("enum variant is missing a name.")]
    EnumVariantMissingName,
    #[error("char literal is missing. (Help: Try creating an empty string instead.)")]
    MissingCharLiteral,
    #[error("char literal is malformed. (Help: Try creating a string instead.)")]
    InvalidCharLiteral,
    #[error("{message}")]
    Custom { message: String },
}

pub type Result<T, E = ParseError> = std::result::Result<T, E>;

/// A temporary struct used to store the start of a span.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct SpanStart {
    start: u32,
}

/// A temporary struct used to store the current cursor of the parser. This can be used to
/// backtrack the parser.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CursorPos {
    pos: usize,
}

impl Parser {
    pub fn new(file_id: FileId, source: &str) -> Self {
        let tokens = Some((Token::Start, 0..0))
            .into_iter()
            .chain(Token::lexer(source).spanned())
            .collect();
        Self {
            tokens,
            cursor: 0,
            file_id,
        }
    }

    pub fn eof(&self) -> bool {
        self.peek_next() == &Token::Eof
    }

    /// Returns a `SpanStart` that can be used to create a `Span` later.
    #[must_use]
    fn start(&self) -> SpanStart {
        let start = self
            .tokens
            .get(self.cursor + 1)
            .map(|x| x.1.start)
            .unwrap_or(0) as u32;
        SpanStart { start }
    }

    /// Returns a `Span` from a `SpanStart`.
    #[must_use]
    fn end(&self, start: SpanStart) -> Span {
        let end = self.tokens.get(self.cursor).map(|x| x.1.end).unwrap_or(0) as u32;
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

    /// Create a marker at the current position of the cursor to be potentially used in
    /// backtracking later.
    fn marker(&self) -> CursorPos {
        CursorPos { pos: self.cursor }
    }

    fn backtrack(&mut self, marker: CursorPos) {
        self.cursor = marker.pos;
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
    pub fn expect(&mut self, expected: Token) -> Result<&Token> {
        let next = self.get_next();
        if next == &expected {
            Ok(next)
        } else {
            Err(ParseError::ExpectedToken {
                unexpected: next.clone(),
                expected: vec![expected],
            })
        }
    }

    /// Create a [`ParseError::UnexpectedToken`] error with the next token as the unexpected token.
    pub fn unexpected(&self, expected: Vec<Token>) -> ParseError {
        ParseError::ExpectedToken {
            unexpected: self.peek_next().clone(),
            expected,
        }
    }

    pub fn parse_root(&mut self) -> Result<Root> {
        let mut items = Vec::new();
        while !self.eof() {
            items.push(self.parse_item()?);
        }
        Ok(Root { items })
    }

    pub fn parse_attributes(&mut self) -> Result<Spanned<Attributes>> {
        let start = self.start();
        let mut attrs = Vec::new();
        while self.peek_next() == &Token::LBracket {
            attrs.push(self.parse_attribute()?);
        }
        Ok(self.finish(start, Attributes { attrs }))
    }

    pub fn parse_attribute(&mut self) -> Result<Spanned<Attribute>> {
        let start = self.start();
        self.expect(Token::LBracket)?;
        let ident = self.parse_ident()?;
        self.expect(Token::RBracket)?;
        Ok(self.finish(start, Attribute { ident }))
    }

    pub fn parse_vis(&mut self) -> Result<Spanned<Vis>> {
        let start = self.start();
        let vis = match self.peek_next() {
            Token::KwPub => {
                let _ = self.get_next();
                Vis::Pub
            }
            _ => Vis::Priv,
        };
        Ok(self.finish(start, vis))
    }

    pub fn parse_item(&mut self) -> Result<Spanned<Item>> {
        let start = self.start();
        let attrs = self.parse_attributes()?;
        // If we see a visibility keyword, look at the token after that to decide which branch to
        // parse.
        let kw = match self.peek_next() {
            Token::KwPub => self.peek_nth(2),
            x => x,
        };
        match kw {
            Token::KwLet => {
                let item = self.parse_let_item(attrs)?;
                Ok(self.finish(start, Item::Let(item)))
            }
            Token::KwType => {
                let item = self.parse_type_item(attrs)?;
                Ok(self.finish(start, Item::Type(item)))
            }
            Token::KwMod => {
                let item = self.parse_mod_item(attrs)?;
                Ok(self.finish(start, Item::Mod(item)))
            }
            Token::KwUse => {
                let item = self.parse_use_item(attrs)?;
                Ok(self.finish(start, Item::Use(item)))
            }
            _ => Err(ParseError::ExpectedItem {
                unexpected: self.peek_next().clone(),
            }),
        }
    }

    pub fn parse_let_item(&mut self, attrs: Spanned<Attributes>) -> Result<Spanned<LetItem>> {
        let start = self.start();
        let vis = self.parse_vis()?;
        self.expect(Token::KwLet)?;
        let ident = self.parse_ident()?;

        let mut params = Vec::new();
        while let Token::LParen | Token::Ident(_) = self.peek_next() {
            params.push(self.parse_param()?);
        }

        let ret_ty = if self.peek_next() == &Token::Colon {
            self.expect(Token::Colon);
            Some(self.parse_type()?)
        } else {
            None
        };

        self.expect(Token::Eq)?;
        let expr = self.parse_expr()?;
        Ok(self.finish(
            start,
            LetItem {
                attrs,
                vis,
                ident,
                ret_ty,
                params,
                expr,
            },
        ))
    }

    pub fn parse_param(&mut self) -> Result<Spanned<Param>> {
        let start = self.start();
        if self.peek_next() == &Token::LParen {
            self.expect(Token::LParen)?;
            let ident = self.parse_ident()?;
            self.expect(Token::Colon)?;
            let ty = self.parse_type()?;
            self.expect(Token::RParen)?;
            Ok(self.finish(
                start,
                Param {
                    ident,
                    ty: Some(ty),
                },
            ))
        } else {
            let ident = self.parse_ident()?;
            Ok(self.finish(start, Param { ident, ty: None }))
        }
    }

    pub fn parse_type_item(&mut self, attrs: Spanned<Attributes>) -> Result<Spanned<TypeItem>> {
        let start = self.start();
        let vis = self.parse_vis()?;
        self.expect(Token::KwType)?;
        let ident = self.parse_ident()?;
        let mut ty_params = Vec::new();
        while let Token::Ident(_) = self.peek_next() {
            ty_params.push(self.parse_type_param()?);
        }
        self.expect(Token::Eq)?;
        let ty = self.parse_type()?;
        Ok(self.finish(
            start,
            TypeItem {
                attrs,
                vis,
                ident,
                ty_params,
                ty,
            },
        ))
    }

    pub fn parse_type_param(&mut self) -> Result<Spanned<TypeParam>> {
        let start = self.start();
        let ident = self.parse_ident()?;
        Ok(self.finish(start, TypeParam { ident }))
    }

    pub fn parse_type(&mut self) -> Result<Spanned<Type>> {
        self.parse_type_with_enum(true)
    }

    /// Parse a type. If `parse_enum` is `true`, will keep on parsing if a `|` is encountered. If
    /// `false`, will stop when encountering a `|`.
    pub fn parse_type_with_enum(&mut self, parse_enum: bool) -> Result<Spanned<Type>> {
        let start = self.start();
        let start_marker = self.marker();
        let starts_with_ident = matches!(self.peek_next(), Token::Ident(_)) && parse_enum;
        let ty = match self.peek_next() {
            Token::LParen | Token::LBrace => self.parse_primary_type()?,
            Token::Ident(_) => self.finish(start, Type::Path(self.parse_path_type()?)),
            token => {
                return Err(ParseError::ExpectedType {
                    unexpected: token.clone(),
                })
            }
        };

        match self.peek_next() {
            Token::RArrow => {
                self.expect(Token::RArrow)?;
                let ret_ty = self.parse_type()?;
                Ok(self.finish(
                    start,
                    Type::Fn(self.finish(
                        start,
                        FnType {
                            arg_ty: Box::new(ty),
                            ret_ty: Box::new(ret_ty),
                        },
                    )),
                ))
            }
            Token::Or if starts_with_ident => {
                // Restart from beginning and parse as enum.
                self.backtrack(start_marker);
                let ty = self.parse_enum_type()?;
                Ok(self.finish(start, Type::Enum(ty)))
            }
            _ => Ok(ty),
        }
    }

    pub fn parse_primary_type(&mut self) -> Result<Spanned<Type>> {
        let start = self.start();
        match self.peek_next() {
            Token::LParen => {
                self.expect(Token::LParen);
                let ty = self.parse_type()?;
                if self.peek_next() == &Token::Comma {
                    // Parse a tuple.
                    self.expect(Token::Comma);
                    let mut fields = vec![ty];
                    while matches!(
                        self.peek_next(),
                        Token::LParen | Token::LBrace | Token::Ident(_)
                    ) {
                        fields.push(self.parse_type()?);
                    }
                    self.expect(Token::RParen);
                    Ok(self.finish(start, Type::Tuple(self.finish(start, TupleType { fields }))))
                } else {
                    // This is just a parenthesized type.
                    self.expect(Token::RParen);
                    Ok(ty)
                }
            }
            Token::LBrace => {
                let ty = self.parse_record_type()?;
                Ok(self.finish(start, Type::Record(ty)))
            }
            Token::Ident(_) => {
                let ident = self.parse_ident()?;
                Ok(self.finish(
                    start,
                    Type::Path(self.finish(
                        start,
                        PathType {
                            path: vec![ident],
                            ty_args: Vec::new(),
                        },
                    )),
                ))
            }
            _ => Err(ParseError::ExpectedType {
                unexpected: self.peek_next().clone(),
            }),
        }
    }

    pub fn parse_path_type(&mut self) -> Result<Spanned<PathType>> {
        let start = self.start();
        let initial = self.parse_ident()?;
        let mut path = vec![initial];
        while self.peek_next() == &Token::Dot {
            self.expect(Token::Dot);
            path.push(self.parse_ident()?);
        }

        let mut ty_args = Vec::new();
        while matches!(
            self.peek_next(),
            Token::LParen | Token::LBrace | Token::Ident(_)
        ) {
            ty_args.push(self.parse_primary_type()?);
        }

        Ok(self.finish(start, PathType { path, ty_args }))
    }

    pub fn parse_record_type(&mut self) -> Result<Spanned<RecordType>> {
        let start = self.start();
        self.expect(Token::LBrace)?;

        let mut fields = Vec::new();
        while let Token::Ident(_) = self.peek_next() {
            fields.push(self.parse_record_field()?);
        }

        self.expect(Token::RBrace)?;

        Ok(self.finish(start, RecordType { fields }))
    }

    pub fn parse_record_field(&mut self) -> Result<Spanned<RecordField>> {
        let start = self.start();
        let ident = self.parse_ident()?;
        self.expect(Token::Colon);
        let ty = self.parse_type()?;
        Ok(self.finish(
            start,
            RecordField {
                ident,
                ty: Box::new(ty),
            },
        ))
    }

    pub fn parse_enum_type(&mut self) -> Result<Spanned<EnumType>> {
        let start = self.start();
        let first = self.parse_enum_variant()?;
        let mut variants = vec![first];
        while self.peek_next() == &Token::Or {
            variants.push(self.parse_enum_variant()?);
        }
        Ok(self.finish(start, EnumType { variants }))
    }

    pub fn parse_enum_variant(&mut self) -> Result<Spanned<EnumVariant>> {
        let start = self.start();
        let ident = self.parse_ident()?;
        let ty = if matches!(
            self.peek_next(),
            Token::LParen | Token::LBrace | Token::Ident(_)
        ) {
            Some(Box::new(self.parse_type_with_enum(false)?))
        } else {
            None
        };
        Ok(self.finish(start, EnumVariant { ident, ty }))
    }

    pub fn parse_expr(&mut self) -> Result<Spanned<Expr>> {
        self.parse_expr_with_min_bp(0)
    }

    pub fn parse_primary_expr(&mut self) -> Result<Spanned<Expr>> {
        let start = self.start();
        match self.peek_next() {
            Token::Ident(_) => {
                let ident = self.parse_ident()?;
                Ok(self.finish(start, Expr::Ident(ident)))
            }
            Token::LBrace => {
                let block = self.parse_block_expr()?;
                Ok(self.finish(start, Expr::Block(block)))
            }
            Token::LParen => {
                let _ = self.get_next();
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            Token::LitTrue => {
                let _ = self.get_next();
                Ok(self.finish(start, Expr::LitBool(true)))
            }
            Token::LitFalse => {
                let _ = self.get_next();
                Ok(self.finish(start, Expr::LitBool(false)))
            }
            Token::LitInt(int) => {
                let int = *int;
                let _ = self.get_next();
                Ok(self.finish(start, Expr::LitInt(int)))
            }
            Token::LitFloat(float) => {
                let float = float.clone();
                let _ = self.get_next();
                Ok(self.finish(start, Expr::LitFloat(float)))
            }
            Token::LitStr(str) => {
                let str = str.clone();
                let _ = self.get_next();
                Ok(self.finish(start, Expr::LitStr(str)))
            }
            Token::LitChar(str) => {
                let str = str.clone();
                let _ = self.get_next();
                let mut chars = str.chars();
                let char = chars.next().ok_or(ParseError::InvalidCharLiteral)?;
                if chars.next().is_some() {
                    return Err(ParseError::InvalidCharLiteral);
                }
                Ok(self.finish(start, Expr::LitChar(char)))
            }
            tok if UnaryOp::try_from(tok.clone()).is_ok() => {
                let start = self.start();
                let op = UnaryOp::try_from(tok.clone()).unwrap();
                let op = self.finish(start, op);
                let _ = self.get_next();
                let expr = self.parse_expr()?;
                Ok(self.finish(
                    start,
                    Expr::Unary(self.finish(
                        start,
                        UnaryExpr {
                            op,
                            expr: Box::new(expr),
                        },
                    )),
                ))
            }
            _ => Err(ParseError::ExpectedExpr {
                unexpected: self.peek_next().clone(),
            }),
        }
    }

    pub fn parse_expr_with_min_bp(&mut self, min_bp: u32) -> Result<Spanned<Expr>> {
        let start = self.start();
        let mut lhs = self.parse_primary_expr()?;

        loop {
            // Postfix operator.
            if let Ok(postfix) = self.peek_next().clone().try_into() {
                let postfix: PostfixOp = postfix;
                let (l_bp, ()) = postfix.binding_power();
                if l_bp < min_bp {
                    break;
                }
                match postfix {
                    PostfixOp::FnCall => {
                        let args = self.parse_fn_call_args()?;
                        lhs = self.finish(
                            start,
                            Expr::FnCall(self.finish(
                                start,
                                FnCallExpr {
                                    callee: Box::new(lhs),
                                    args,
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
                Err(_) => break,
            };
            let (l_bp, r_bp) = bin_op.binding_power();
            if l_bp < min_bp {
                break;
            }

            // Consume the operator.
            let _ = self.get_next();
            let bin_op = self.finish(bin_op_start, bin_op);

            // Parse RHS.
            let rhs = self.parse_expr_with_min_bp(r_bp)?;
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

        Ok(lhs)
    }

    pub fn parse_block_expr(&mut self) -> Result<Spanned<BlockExpr>> {
        let start = self.start();
        self.expect(Token::LBrace)?;

        let mut stmts = Vec::new();
        while self.peek_next() != &Token::RBrace {
            stmts.push(self.parse_stmt()?);
        }
        self.expect(Token::RBrace)?;
        Ok(self.finish(start, BlockExpr { stmts }))
    }

    pub fn parse_if_expr(&mut self) -> Result<Spanned<IfExpr>> {
        let start = self.start();
        self.expect(Token::KwIf)?;
        let cond = self.parse_expr()?;
        let then = self.parse_block_expr()?;
        let then = spanned(then.span(), Expr::Block(then));
        let else_ = if self.peek_next() == &Token::KwElse {
            let _ = self.get_next();
            let else_ = self.parse_block_expr()?;
            Some(Box::new(spanned(else_.span(), Expr::Block(else_))))
        } else {
            None
        };
        Ok(self.finish(
            start,
            IfExpr {
                cond: Box::new(cond),
                then: Box::new(then),
                else_,
            },
        ))
    }

    pub fn parse_while_expr(&mut self) -> Result<Spanned<WhileExpr>> {
        let start = self.start();
        self.expect(Token::KwWhile)?;
        let cond = self.parse_expr()?;
        let body = self.parse_block_expr()?;
        let body = Box::new(spanned(body.span(), Expr::Block(body)));
        Ok(self.finish(
            start,
            WhileExpr {
                cond: Box::new(cond),
                body,
            },
        ))
    }

    pub fn parse_for_expr(&mut self) -> Result<Spanned<ForExpr>> {
        let start = self.start();
        self.expect(Token::KwFor)?;
        let binding = self.parse_binding()?;
        self.expect(Token::KwIn)?;
        let iter = self.parse_expr()?;
        let body = self.parse_block_expr()?;
        let body = Box::new(spanned(body.span(), Expr::Block(body)));
        Ok(self.finish(
            start,
            ForExpr {
                binding,
                iter: Box::new(iter),
                body,
            },
        ))
    }

    pub fn parse_loop_expr(&mut self) -> Result<Spanned<LoopExpr>> {
        let start = self.start();
        self.expect(Token::KwLoop)?;
        let body = self.parse_block_expr()?;
        let body = Box::new(spanned(body.span(), Expr::Block(body)));
        Ok(self.finish(start, LoopExpr { body }))
    }

    pub fn parse_return_expr(&mut self) -> Result<Spanned<ReturnExpr>> {
        let start = self.start();
        self.expect(Token::KwReturn)?;
        let expr = self.parse_expr()?;
        Ok(self.finish(start, ReturnExpr { expr }))
    }

    pub fn parse_struct_item(&mut self, attrs: Spanned<Attributes>) -> Result<Spanned<StructItem>> {
        let start = self.start();
        let vis = self.parse_vis()?;
        self.expect(Token::KwStruct)?;
        let ident = self.parse_ident()?;
        self.expect(Token::LBrace)?;
        let mut fields = Vec::new();
        while self.peek_next() != &Token::RBrace {
            fields.push(self.parse_struct_field()?);
            match self.peek_next() {
                Token::RBrace => break,
                Token::Comma => {
                    let _ = self.get_next();
                    if self.peek_next() == &Token::RBrace {
                        break;
                    }
                }
                _ => {
                    self.expect(Token::Comma)?;
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(self.finish(
            start,
            StructItem {
                attrs,
                vis,
                ident,
                fields,
            },
        ))
    }

    pub fn parse_struct_field(&mut self) -> Result<Spanned<StructField>> {
        let start = self.start();
        let ident = self.parse_ident()?;
        self.expect(Token::Colon)?;
        let ty = self.parse_ident()?;
        Ok(self.finish(start, StructField { ident, ty }))
    }

    pub fn parse_mod_item(&mut self, attrs: Spanned<Attributes>) -> Result<Spanned<ModItem>> {
        let start = self.start();
        let vis = self.parse_vis()?;
        self.expect(Token::KwMod)?;
        let ident = self.parse_ident()?;
        Ok(self.finish(start, ModItem { attrs, vis, ident }))
    }

    pub fn parse_use_item(&mut self, attrs: Spanned<Attributes>) -> Result<Spanned<UseItem>> {
        let start = self.start();
        let vis = self.parse_vis()?;
        self.expect(Token::KwUse)?;
        let path = self.parse_ident()?;
        Ok(self.finish(start, UseItem { attrs, vis, path }))
    }

    pub fn peek_ident(&self) -> Result<&str> {
        let next = self.peek_next();
        let Token::Ident(ident) = next else {
            return Err(ParseError::ExpectedToken {
                unexpected: next.clone(),
                expected: vec![Token::Ident("".to_string())],
            });
        };
        Ok(ident)
    }

    pub fn parse_ident(&mut self) -> Result<Spanned<String>> {
        let start = self.start();
        let next = self.get_next();
        let Token::Ident(ident) = next else {
            return Err(ParseError::ExpectedToken {
                unexpected: next.clone(),
                expected: vec![Token::Ident("".to_string())],
            });
        };
        let ident = ident.clone();
        Ok(self.finish(start, ident))
    }

    pub fn parse_binding(&mut self) -> Result<Spanned<Binding>> {
        let start = self.start();
        let ident = self.parse_ident()?;
        let ty = if self.peek_next() == &Token::Colon {
            let _ = self.get_next();
            Some(self.parse_ident()?)
        } else {
            None
        };
        Ok(self.finish(start, Binding { ident, ty }))
    }
}
