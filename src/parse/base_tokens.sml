structure base_tokens :> base_tokens =
struct

  exception LEX_ERR of string * locn.locn

  datatype 'a base_token =
    BT_Ident of string
  | BT_Numeral of (string * char option)
  | BT_QIdent of (string * string)
  | BT_AQ of 'a
  | BT_EOI
  | BT_InComment of int

  fun toString (BT_Ident s) = s
    | toString (BT_Numeral(s, copt)) = s ^ (case copt of SOME c => String.str c
                                                       | NONE => "")
    | toString (BT_QIdent(s1, s2)) = s1 ^ "$" ^ s2
    | toString (BT_AQ x) = "<AntiQuote>"
    | toString BT_EOI = "<End of Input>"
    | toString (BT_InComment n) = "<In Comment, depth "^Int.toString(n + 1)^">"

end;
