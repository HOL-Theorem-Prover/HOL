signature term_tokens =
sig

  datatype 'a term_token =
    Ident of string
  | Antiquote of 'a
  | Numeral of (Arbnum.num * char option)
  | Fraction of {wholepart : Arbnum.num, fracpart : Arbnum.num,
                 places : int}
  | QIdent of (string * string)

  val lex : string list -> 'a qbuf.qbuf -> 'a term_token locn.located option
      (* NONE indicates end of input; this function *always* advances over
         what it pulls out of the qbuf.   *)

  val user_split_ident : string list -> string -> (string * string)

  val token_string : 'a term_token -> string
  val dest_aq      : 'a term_token -> 'a
  val is_ident     : 'a term_token -> bool
  val is_aq        : 'a term_token -> bool

  val nonagg_c     : char -> bool

  val lextest : string list -> string -> 'a term_token list

end

