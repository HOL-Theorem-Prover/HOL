structure type_tokens_dtype =
struct

  datatype 'a type_token
      = TypeIdent of string
      | QTypeIdent of string * string (* thy name * type name *)
      | TypeSymbol of string
      | TypeVar of string
      | Comma
      | LParen
      | RParen
      | LBracket
      | RBracket
      | AQ of 'a
      | Error of 'a base_tokens.base_token

end
