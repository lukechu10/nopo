# Nopo Language

## Specification

### Grammar

_Root_: _Item_*

_Item_: _LetItem_ | _TypeItem_

_LetItem_: `let` _Ident_ _Arg_* (`:` _Type_)? `=` _Expr_ \
_Arg_: _Ident_ | `(` _Ident_ `:` _Type_ `)`

_TypeItem_: `type` _Ident_ _TypeArg_* `=` _Type_ \
_TypeArg_: _Ident_ **(TODO: add type bounds?)**

_Type_: _TypePath_ | _Fn_ | _Record_ | _Enum_ | _Tuple_ \
_TypePath_: _Ident_ (`.` _Ident_)* _TypeArg_* \
_Fn_: _Type_ `->` _Type_ \
_Record_: `{` (_Ident_ `:` _Type_ `,`)* `}`) \
_Enum_: _EnumVar_ (`|` _EnumVar_)* **(TODO: allow empty enums?)** \
_EnumVar_: _Ident_ _Type_? \
_Tuple_: `(` (_Type_ `,`)* `)`

_Expr_: _Call_ | _Binop_ | _Unary_ | _TupleExpr_ | _RecordExpr_ | _Lambda_ | _Index_ | _IfElse_ | _For_ | _While_ | _Block_ | _Lit_ | _Update_ | _Paren_ \
_ExprPath_: _Ident_ (`.` _Ident_)* \
_ExprParened_: _ExprPath_ | _Block_ | _Lit_ | _Paren_ \
_Call_: _ExprPath_ _ExprParened_* \
_Index_: _ExprParened_ `[` _Expr_ `]` \
_Binop_, _Unary_, **use pratt parsing with corresponding operator precedence** \
_Block_: `{` _ExprStmt_* `}` \
_IfElse_: `if` _Expr_ `then` _Expr_ (`else` _Expr_)? \
_For_: `for` _Ident_ in _Expr_ _Block_ \
_While_: `while` _Expr_ _Block_ \
_Lambda_: `\` _Ident_* `=` _Expr_ \
_TupleExpr_: `(` (_Expr_ `,`)* `)` \
_RecordExpr_: `{` (_Ident_ `:` _Expr_ `,`)* `}` \
_Update_: _ExprPath_ `:=` _Expr_

_Paren_: `(` _Expr_ `)`

_ExprStmt_: _Expr_ | _Item_

_Lit_: _IntLit_ | _FlaotLit_ | _StringLit_ | `true` | `false` **(define bool as an enum?)**

_Ident_: **refer to unicode-xid**

