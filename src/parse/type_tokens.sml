structure type_tokens :> type_tokens =
struct

  datatype 'a type_token
      = TypeIdent of string
      | QTypeIdent of string * string (* thy name * type name *)
      | TypeSymbol of string
      | TypeVar of string
      | KindCst
      | RankCst
      | Comma
      | Period
      | LParen
      | RParen
      | LBracket
      | RBracket
      | AQ of 'a
      | Error of 'a base_tokens.base_token

val ERR = Feedback.mk_HOL_ERR "type_tokens"

open qbuf base_tokens

fun special_symb c = c = #"(" orelse c = #")" orelse c = #"," orelse c = #"." orelse
                     c = #":" (* orelse c = #"!" orelse c = #"\\" *)

fun split_and_check fb s locn = let
  (* if the first character of s is non-alphanumeric character, then it
     will be a symbolic blob.  *)
  val s0 = String.sub(s, 0)
  fun nadvance n tt =
      if size s = n then ((fn () => advance fb),(tt,locn))
      else let
          val (locn',locn'') = locn.split_at n locn
        in
          ((fn () => replace_current (BT_Ident (String.extract(s, n, NONE)),
                                      locn'') fb),
           (tt,locn'))
        end
  val error = ((fn () => advance fb), (Error (BT_Ident s), locn))
in
  if Char.isAlpha s0 then ((fn () => advance fb), (TypeIdent s,locn))
  else if s0 = #"'" then ((fn () => advance fb), (TypeVar s,locn))
  else if s0 = #"(" then nadvance 1 LParen
  else if s0 = #")" then nadvance 1 RParen
  else if s0 = #":" then
    if size s = 1 then nadvance 1 KindCst
    else if size s = 2 then error
    else if String.sub(s,1) = #"<" andalso
            String.sub(s,2) = #"=" then
           nadvance 3 RankCst
         else error
(*
    if size s > 1 then
      if String.sub(s,1) = #":" then
        nadvance 2 KindCst
      else error
    else error
*)
(*
  else if s0 = #"<" then
    if size s > 1 then
      if String.sub(s,1) = #"=" then
        nadvance 2 RankCst
      else error
    else error
*)
  else if s0 = #"," then nadvance 1 Comma
  else if s0 = #"." then nadvance 1 Period
  else if s0 = #"[" then nadvance 1 LBracket
  else if s0 = #"]" then nadvance 1 RBracket
  else if s0 = #"\"" then error
  else let
      val (ssl, ssr) =
          Substring.splitl (not o special_symb) (Substring.all s)
      val sl = Substring.string ssl
      val sr = Substring.string ssr
    in
      nadvance (size sl) (TypeSymbol sl)
    end
end

fun handle_num numinfo =
    case numinfo of
      (num, NONE) => TypeIdent (Arbnum.toString num)
    | (num, SOME _) => Error (BT_Numeral numinfo)

fun typetok_of fb = let
  val (bt,locn) = current fb
in
  case bt of
    BT_Numeral numinfo => ((fn () => advance fb), (handle_num numinfo, locn))
  | BT_QIdent p => ((fn () => advance fb), (QTypeIdent p,locn))
  | BT_AQ x => ((fn () => advance fb), (AQ x,locn))
  | BT_EOI => ((fn () => ()), (Error bt,locn))
  | BT_Ident s => split_and_check fb s locn
end

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

end
