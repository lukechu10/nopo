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
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("<=")]
    LtEq,
    #[token(">=")]
    GtEq,

    #[token("==")]
    EqEq,
    #[token("!=")]
    BangEq,

    #[token("&")]
    And,
    #[token("|")]
    Or,
    #[token("^")]
    Xor,
    #[token(">>")]
    ShiftRight,
    #[token("<<")]
    ShiftLeft,
    #[token(">>>")]
    UnsignedShiftRight,

    #[token("&&")]
    AndAnd,
    #[token("||")]
    OrOr,

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
    #[token("use")]
    KwUse,
    #[token("mod")]
    KwMod,
    #[token("pub")]
    KwPub,

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
    #[regex(r"[ \t\n\f]+", logos::skip)] // Whitespace
    #[regex(r#"//[^\n]*"#, logos::skip)] // Line comments
    // TODO: block comments
    Err,
}

impl Token {
    /// Returns `true` if this token is a keyword that starts an item.
    pub fn is_item_kw(self) -> bool {
        matches!(
            self,
            Token::KwFn
                | Token::KwExtern
                | Token::KwStruct
                | Token::KwEnum
                | Token::KwMod
                | Token::KwUse
                | Token::KwPub
                | Token::LBracket
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Plus,
    Minus,
    Mul,
    Div,
    Mod,
    // Bitwise
    And,
    Or,
    Xor,
    ShiftLeft,
    ShiftRight,
    UnsignedShiftRight,
    // Relational
    EqEq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    // Logical
    AndAnd,
    OrOr,
    // Assignment
    Eq,
    // Member access
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
            Token::And => Ok(BinOp::And),
            Token::Or => Ok(BinOp::Or),
            Token::Xor => Ok(BinOp::Xor),
            Token::ShiftLeft => Ok(BinOp::ShiftLeft),
            Token::ShiftRight => Ok(BinOp::ShiftRight),
            Token::UnsignedShiftRight => Ok(BinOp::UnsignedShiftRight),
            Token::EqEq => Ok(BinOp::EqEq),
            Token::BangEq => Ok(BinOp::NotEq),
            Token::Lt => Ok(BinOp::Lt),
            Token::Gt => Ok(BinOp::Gt),
            Token::LtEq => Ok(BinOp::LtEq),
            Token::GtEq => Ok(BinOp::GtEq),
            Token::AndAnd => Ok(BinOp::AndAnd),
            Token::OrOr => Ok(BinOp::OrOr),
            Token::Eq => Ok(BinOp::Eq),
            Token::Dot => Ok(BinOp::Dot),
            _ => Err(()),
        }
    }
}

impl BinOp {
    pub fn binding_power(self) -> (u32, u32) {
        match self {
            BinOp::Eq => (10, 0),
            BinOp::OrOr => (100, 110),
            BinOp::AndAnd => (120, 130),
            BinOp::Or => (200, 210),
            BinOp::Xor => (220, 230),
            BinOp::And => (240, 250),
            BinOp::EqEq | BinOp::NotEq => (300, 310),
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq => (400, 410),
            BinOp::ShiftLeft | BinOp::ShiftRight | BinOp::UnsignedShiftRight => (500, 510),
            BinOp::Plus | BinOp::Minus => (1000, 1010),
            BinOp::Mul | BinOp::Div | BinOp::Mod => (1020, 1030),
            BinOp::Dot => (2000, 2010),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PostfixOp {
    FnCall,
}

impl TryFrom<Token> for PostfixOp {
    type Error = ();

    fn try_from(value: Token) -> Result<Self, Self::Error> {
        match value {
            Token::LParen => Ok(PostfixOp::FnCall),
            _ => Err(()),
        }
    }
}

impl PostfixOp {
    pub fn binding_power(self) -> (u32, ()) {
        match self {
            PostfixOp::FnCall => (2000, ()),
        }
    }
}
