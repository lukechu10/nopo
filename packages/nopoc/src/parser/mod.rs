use std::ops::Range;

use logos::Logos;
use thiserror::Error;

use crate::ast::*;
use crate::span::{respan, Span, Spanned};

use self::lexer::{BinOp, Token};

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
}

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("expected one of: {expected:?}, found {unexpected:?}.")]
    ExpectedToken {
        unexpected: Token,
        expected: Vec<Token>,
    },
    #[error("expected an expression, found {unexpected:?}.")]
    ExpectedExpr { unexpected: Token },
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
    start: usize,
}

impl Parser {
    pub fn new(source: &str) -> Self {
        let tokens = Some((Token::Start, 0..0))
            .into_iter()
            .chain(Token::lexer(source).spanned())
            .collect();
        Self { tokens, cursor: 0 }
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
            .unwrap_or(0);
        SpanStart { start }
    }

    /// Returns a `Span` from a `SpanStart`.
    #[must_use]
    fn end(&self, start: SpanStart) -> Span {
        let end = self.tokens.get(self.cursor).map(|x| x.1.end).unwrap_or(0);
        Span {
            start: start.start,
            end,
        }
    }

    #[must_use]
    fn respan<T>(&self, start: SpanStart, node: T) -> Spanned<T> {
        respan(self.end(start), node)
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

    pub fn parse_root_or_stmt(&mut self) -> Result<RootOrStmt> {
        if self.peek_next().clone().is_item_kw() {
            let root = self.parse_root()?;
            Ok(RootOrStmt::Root(root))
        } else {
            let stmt = self.parse_stmt_with_semi(false)?.unspan();
            Ok(RootOrStmt::Stmt(stmt))
        }
    }

    pub fn parse_item(&mut self) -> Result<Spanned<Item>> {
        let start = self.start();
        match self.peek_next() {
            Token::KwFn => {
                let item = self.parse_fn_item()?;
                Ok(self.respan(start, Item::Fn(item)))
            }
            Token::KwExtern => {
                todo!("extern fns");
            }
            Token::KwStruct => {
                let item = self.parse_struct_item()?;
                Ok(self.respan(start, Item::Struct(item)))
            }
            Token::KwEnum => {
                todo!("enums");
            }
            _ => Err(self.unexpected(vec![
                Token::KwFn,
                Token::KwExtern,
                Token::KwStruct,
                Token::KwEnum,
            ])),
        }
    }

    pub fn parse_fn_item(&mut self) -> Result<Spanned<FnItem>> {
        let start = self.start();
        self.expect(Token::KwFn)?;
        let ident = self.parse_ident()?;
        let args = self.parse_fn_args()?;
        let ret_ty = if self.peek_next() == &Token::RArrow {
            let _ = self.get_next();
            Some(self.parse_ident()?)
        } else {
            None
        };
        let body = self.parse_block_expr()?;

        Ok(self.respan(
            start,
            FnItem {
                ident,
                args,
                ret_ty,
                body,
            },
        ))
    }

    pub fn parse_fn_args(&mut self) -> Result<Spanned<FnArgs>> {
        let start = self.start();
        self.expect(Token::LParen)?;

        let mut args = Vec::new();
        while self.peek_next() != &Token::RParen {
            args.push(self.parse_binding()?);
            if self.peek_next() == &Token::Comma {
                let _ = self.get_next();
            }
        }
        self.expect(Token::RParen)?;
        Ok(self.respan(start, FnArgs { args }))
    }

    pub fn parse_stmt(&mut self) -> Result<Spanned<Stmt>> {
        self.parse_stmt_with_semi(true)
    }

    pub fn parse_stmt_with_semi(&mut self, semi_required: bool) -> Result<Spanned<Stmt>> {
        let start = self.start();
        // If we see a control-flow statement, we don't need a semicolon unless the type of the
        // expression is not unit. However, we don't know this until type-checking, so we
        // don't check for semi-colon here.
        let defer_semi_check = matches!(
            self.peek_next(),
            Token::KwIf | Token::KwWhile | Token::KwFor | Token::KwLoop
        );
        match self.peek_next() {
            Token::KwLet => {
                let stmt = self.parse_let_stmt()?;
                self.expect(Token::Semi)?;
                Ok(self.respan(start, Stmt::Let(stmt)))
            }
            Token::KwReturn => {
                let expr = self.parse_return_stmt()?;
                self.expect(Token::Semi)?;
                Ok(self.respan(start, Stmt::Return(expr)))
            }
            _ => {
                let expr = self.parse_expr()?;
                if !defer_semi_check && semi_required {
                    self.expect(Token::Semi)?;
                }
                Ok(self.respan(start, Stmt::ExprStmt(expr)))
            }
        }
    }

    pub fn parse_let_stmt(&mut self) -> Result<Spanned<LetStmt>> {
        let start = self.start();
        self.expect(Token::KwLet)?;
        let binding = self.parse_binding()?;
        self.expect(Token::Eq)?;
        let expr = self.parse_expr()?;
        Ok(self.respan(start, LetStmt { binding, expr }))
    }

    pub fn parse_return_stmt(&mut self) -> Result<Spanned<ReturnStmt>> {
        let start = self.start();
        self.expect(Token::KwReturn)?;
        let expr = self.parse_expr()?;
        Ok(self.respan(start, ReturnStmt { expr }))
    }

    pub fn parse_expr(&mut self) -> Result<Spanned<Expr>> {
        self.parse_expr_with_min_bp(0)
    }

    pub fn parse_primary_expr(&mut self) -> Result<Spanned<Expr>> {
        let start = self.start();
        match self.peek_next() {
            Token::Ident(_) => {
                let ident = self.parse_ident()?;
                Ok(self.respan(start, Expr::Ident(ident)))
            }
            Token::LBrace => {
                let block = self.parse_block_expr()?;
                Ok(self.respan(start, Expr::Block(block)))
            }
            Token::LParen => {
                let _ = self.get_next();
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            Token::LitTrue => {
                let _ = self.get_next();
                Ok(self.respan(start, Expr::LitBool(true)))
            }
            Token::LitFalse => {
                let _ = self.get_next();
                Ok(self.respan(start, Expr::LitBool(false)))
            }
            Token::LitInt(int) => {
                let int = *int;
                let _ = self.get_next();
                Ok(self.respan(start, Expr::LitInt(int)))
            }
            Token::LitFloat(float) => {
                let float = float.clone();
                let _ = self.get_next();
                Ok(self.respan(start, Expr::LitFloat(float)))
            }
            Token::LitStr(str) => {
                let str = str.clone();
                let _ = self.get_next();
                Ok(self.respan(start, Expr::LitStr(str)))
            }
            Token::LitChar(str) => {
                let str = str.clone();
                let _ = self.get_next();
                let mut chars = str.chars();
                let char = chars.next().ok_or(ParseError::InvalidCharLiteral)?;
                if chars.next().is_some() {
                    return Err(ParseError::InvalidCharLiteral);
                }
                Ok(self.respan(start, Expr::LitChar(char)))
            }
            _ => Err(ParseError::ExpectedExpr {
                unexpected: self.peek_next().clone(),
            }),
        }
    }

    pub fn parse_expr_with_min_bp(&mut self, bp: u32) -> Result<Spanned<Expr>> {
        let start = self.start();
        let mut lhs = self.parse_primary_expr()?;

        loop {
            let bin_op_start = self.start();
            let bin_op: BinOp = match self.peek_next().clone().try_into() {
                Ok(op) => op,
                Err(_) => break,
            };
            let (l_bp, r_bp) = bin_op.binding_power();
            if l_bp < bp {
                break;
            }

            // Consume the operator.
            let _ = self.get_next();
            let bin_op = self.respan(bin_op_start, bin_op);

            // Parse RHS.
            let rhs = self.parse_expr_with_min_bp(r_bp)?;
            lhs = self.respan(
                start,
                Expr::Binary(self.respan(
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
            stmts.push(self.parse_stmt_with_semi(false)?);
            // Require semicolons after expressions if it is not the last expression of the block.
            if self.peek_next() != &Token::RBrace {
                self.expect(Token::Semi)?;
            }
        }
        self.expect(Token::RBrace)?;
        Ok(self.respan(start, BlockExpr { stmts }))
    }

    pub fn parse_if_expr(&mut self) -> Result<Spanned<IfExpr>> {
        let start = self.start();
        self.expect(Token::KwIf)?;
        let cond = self.parse_expr()?;
        let then = self.parse_block_expr()?;
        let else_ = if self.peek_next() == &Token::KwElse {
            let _ = self.get_next();
            Some(self.parse_block_expr()?)
        } else {
            None
        };
        Ok(self.respan(
            start,
            IfExpr {
                cond: Box::new(cond),
                then,
                else_,
            },
        ))
    }

    pub fn parse_while_expr(&mut self) -> Result<Spanned<WhileExpr>> {
        let start = self.start();
        self.expect(Token::KwWhile)?;
        let cond = self.parse_expr()?;
        let body = self.parse_block_expr()?;
        Ok(self.respan(
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
        Ok(self.respan(
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
        Ok(self.respan(start, LoopExpr { body }))
    }

    pub fn parse_struct_item(&mut self) -> Result<Spanned<StructItem>> {
        let start = self.start();
        self.expect(Token::KwStruct)?;
        let ident = self.parse_ident()?;
        self.expect(Token::LBrace)?;
        let mut fields = Vec::new();
        while self.peek_next() != &Token::RBrace {
            fields.push(self.parse_struct_field()?);
            self.expect(Token::Comma)?; // TODO: optional comma after last field.
        }
        self.expect(Token::RBrace)?;
        Ok(self.respan(start, StructItem { ident, fields }))
    }

    pub fn parse_struct_field(&mut self) -> Result<Spanned<StructField>> {
        let start = self.start();
        let ident = self.parse_ident()?;
        self.expect(Token::Colon)?;
        let ty = self.parse_ident()?;
        Ok(self.respan(start, StructField { ident, ty }))
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
        Ok(self.respan(start, ident))
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
        Ok(self.respan(start, Binding { ident, ty }))
    }
}
