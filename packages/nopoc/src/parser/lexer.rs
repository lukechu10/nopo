#[derive(Debug, Clone, PartialEq, Eq, logos::Logos)]
pub enum Token {
    // Punctuation
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token(",")]
    Comma,
    #[token(".")]
    Dot,
    #[token(":")]
    Colon,
    #[token(";")]
    Semi,
    #[token("->")]
    RArrow,

    // Operators
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("!")]
    Bang,
    #[token("=")]
    Eq,
    #[token("==")]
    EqEq,
    #[token("!=")]
    BangEq,

    // Keywords
    #[token("fn")]
    KwFn,
    #[token("extern")]
    KwExtern,
    #[token("struct")]
    KwStruct,
    #[token("enum")]
    KwEnum,
    #[token("let")]
    KwLet,
    #[token("if")]
    KwIf,
    #[token("else")]
    KwElse,
    #[token("while")]
    KwWhile,
    #[token("for")]
    KwFor,
    #[token("in")]
    KwIn,
    #[token("loop")]
    KwLoop,
    #[token("return")]
    KwReturn,
    #[token("break")]
    KwBreak,
    #[token("continue")]
    KwContinue,

    // Identifiers
    #[regex("[a-zA-Z_$][a-zA-Z0-9_$]*", |lex| lex.slice().to_string())]
    Ident(String),

    // Literals
    #[token("true")]
    LitTrue,
    #[token("false")]
    LitFalse,
    #[regex("[0-9]+", |lex| lex.slice().parse())]
    LitInt(i64),
    #[regex("[0-9]+\\.[0-9]+", |lex| lex.slice().to_string())]
    LitFloat(String),
    #[regex(r#""(?:[^"]|\\")*""#, |lex| lex.slice()[1..lex.slice().len() - 1].to_string())]
    LitStr(String),
    #[regex(r#"'([^'\\]|\\.)*'"#, |lex| lex.slice()[1..lex.slice().len() - 1].to_string())]
    LitChar(String),

    /// A special token that marks the start of the input.
    Start,
    /// A special token that represents the end of the input.
    Eof,
    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Err,
}

impl Token {
    /// Returns `true` if this token is a keyword that starts an item.
    pub fn is_item_kw(self) -> bool {
        matches!(
            self,
            Token::KwFn | Token::KwExtern | Token::KwStruct | Token::KwEnum
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Plus,
    Minus,
    Mul,
    Div,
    Mod,
    Eq,
    EqEq,
    NotEq,
    /// Member accessor operator.
    Dot,
}

impl TryFrom<Token> for BinOp {
    type Error = ();

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::Plus => Ok(BinOp::Plus),
            Token::Minus => Ok(BinOp::Minus),
            Token::Star => Ok(BinOp::Mul),
            Token::Slash => Ok(BinOp::Div),
            Token::Percent => Ok(BinOp::Mod),
            Token::Eq => Ok(BinOp::Eq),
            Token::EqEq => Ok(BinOp::EqEq),
            Token::BangEq => Ok(BinOp::NotEq),
            Token::Dot => Ok(BinOp::Dot),
            _ => Err(()),
        }
    }
}

impl BinOp {
    pub fn binding_power(self) -> (u32, u32) {
        match self {
            BinOp::Eq => (10, 20),
            BinOp::EqEq | BinOp::NotEq => (30, 40),
            BinOp::Plus | BinOp::Minus => (50, 60),
            BinOp::Mul | BinOp::Div | BinOp::Mod => (70, 80),
            BinOp::Dot => (100, 90),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

impl TryFrom<Token> for UnaryOp {
    type Error = ();

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::Minus => Ok(UnaryOp::Neg),
            Token::Bang => Ok(UnaryOp::Not),
            _ => Err(()),
        }
    }
}
