structure kind_tokens :> kind_tokens =
struct

  datatype 'a kind_token
      = KindIdent of string (* alphanum name of constant kind, defined *)
      | QKindIdent of string * string (* thy name * kind name *)
      | KindSymbol of string (* symbolic identifier, not :: or <= or incl  (),:  *)
      | KindVar of string
      | KindArity
      | KindNumeral of int
      | KindCst
      | RankCst
      | Comma
      | LParen
      | RParen
      | LBracket
      | RBracket
      | AQ of 'a
      | Error of 'a base_tokens.base_token

val ERR = Feedback.mk_HOL_ERR "kind_tokens"

open qbuf base_tokens

fun special_symb c = c = #"(" orelse c = #")" orelse c = #"," orelse
                     c = #":"

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
  if s = "ar" then ((fn () => advance fb), (KindArity,locn))
  else if Char.isAlpha s0 then ((fn () => advance fb), (KindIdent s,locn))
  else if s0 = #"'" then ((fn () => advance fb), (KindVar s,locn))
  else if s0 = #"(" then nadvance 1 LParen
  else if s0 = #")" then nadvance 1 RParen
  else if s0 = #":" then
    if size s > 1 then
      if String.sub(s,1) = #":" then
        nadvance 2 KindCst
      else error
    else error
  else if s0 = #"<" then
    if size s > 1 then
      if String.sub(s,1) = #"=" then
        nadvance 2 RankCst
      else error
    else error
  else if s0 = #"," then nadvance 1 Comma
  else if s0 = #"[" then nadvance 1 LBracket
  else if s0 = #"]" then nadvance 1 RBracket
  else if s0 = #"\"" then error
  else let
      val (ssl, ssr) =
          Substring.splitl (not o special_symb) (Substring.all s)
      val sl = Substring.string ssl
      val sr = Substring.string ssr
    in
      nadvance (size sl) (KindSymbol sl)
    end
end

fun handle_num numinfo =
    case numinfo of
      (num, NONE) => (KindNumeral (Arbnum.toInt num)
                      handle Overflow => Error (BT_Numeral numinfo))
    | (num, SOME _) => Error (BT_Numeral numinfo)

fun kindtok_of fb = let
  val (bt,locn) = current fb
in
  case bt of
    BT_Numeral numinfo => ((fn () => advance fb), (handle_num numinfo, locn))
  | BT_QIdent p => ((fn () => advance fb), (QKindIdent p,locn))
  | BT_AQ x => ((fn () => advance fb), (AQ x,locn))
  | BT_EOI => ((fn () => ()), (Error bt,locn))
  | BT_Ident s => split_and_check fb s locn
end

fun token_string (KindIdent s) = s
  | token_string (KindVar s) = s
  | token_string (KindSymbol s) = s
  | token_string (KindNumeral i) = Int.toString i
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (AQ x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote kind token"

fun is_ident (KindIdent _) = true
  | is_ident _ = false
fun is_kindvar (KindVar _) = true
  | is_kindvar _ = false
fun is_kindsymbol (KindSymbol _) = true
  | is_kindsymbol _ = false
fun is_kindaq (AQ _) = true
  | is_kindaq _ = false

end
