
datatype 'a type_token =
  TypeIdent of string | TypeSymbol of string | TypeVar of string |
  Comma | LParen | RParen |
  AQ of 'a


open optmonad monadic_parse
open fragstr
infix >- >> ++

open HOLtokens
infix ANDNOT

fun lex s =
  ((token antiq >- return o AQ) ++
   (symbol "(" >> return LParen) ++
   (symbol ")" >> return RParen) ++
   (symbol "," >> return Comma) ++
   (token (item #"'" >> normal_alpha_ident)  >-
    (fn s => return (TypeVar ("'"^s)))) ++
   (token (many1_charP HOLid) >- return o TypeIdent) ++
   (token (many1_charP (HOLsym ANDNOT ITEMS "(),")) >- return o TypeSymbol)) s


fun token_string (TypeIdent s) = s
  | token_string (TypeVar s) = s
  | token_string (TypeSymbol s) = s
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (AQ x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote token"

fun is_ident (TypeIdent _) = true
  | is_ident _ = false
fun is_tvar (TypeVar _) = true
  | is_tvar _ = false
fun is_typesymbol (TypeSymbol _) = true
  | is_typesymbol _ = false
fun is_aq (AQ _) = true
  | is_aq _ = false

