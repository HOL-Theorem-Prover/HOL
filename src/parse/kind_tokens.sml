structure kind_tokens :> kind_tokens =
struct

  datatype 'a kind_token
      = KindIdent of string (* alphanum name of constant kind, defined *)
      | QKindIdent of string * string (* thy name * type name *)
      | KindSymbol of string (* symbolic identifier, not :: or <= or incl  (),:  *)
      | KindVar of string
      | KindArity
      | KindNumeral of string
      | KindRankCst
      | Comma
      | LParen
      | RParen
      | LBracket
      | RBracket
      | AQ of 'a
      | Error of 'a base_tokens.base_token

fun toksize tt =
    case tt of
      KindIdent s => size s
    | QKindIdent (s1,s2) => size s1 + size s2 + 1
    | KindSymbol s => size s
    | KindVar s => size s
    | KindArity => 1
    | KindNumeral s => size s
(* if n = 0 then 1 else Real.ceil (Math.log10 (Real.fromInt (n+1))) *)
    | KindRankCst => 1
    | Comma => 1
    | LParen => 1
    | RParen => 1
    | LBracket => 1
    | _ => 0 (* a lie, but unimportant given calling context *)


val ERR = Feedback.mk_HOL_ERR "kind_tokens"

open qbuf base_tokens

fun munge slist = String.concat (List.rev slist)

fun special_symb c = c = #"(" orelse c = #")" orelse c = #"," orelse
                     c = #":"

fun kindidentp (part1, part2) s = let
  open UnicodeChars
  (* record whether or not we're onto part2 by checking if part2 is non-null *)
in
  if isAlphaNum s orelse s = "_" then
    if not (null part2) then
      SOME (part1, s :: part2)
    else SOME (s :: part1, part2)
  else if s = "$" then SOME (part1, s :: part2)
  else NONE
end

fun MkKindIdent (part1, part2) =
    if null part2 then
      let val s = munge part1
      in if s = "ar" then KindArity else KindIdent s
      end
    else if length part2 = 1 then
      raise ERR "MkKindIdent" "Malformed qualified identifier (no part after $)"
    else QKindIdent(munge part1, String.extract (munge part2, 1, NONE))

fun kindvarp0 s = UnicodeChars.isAlphaNum s orelse s = "'" orelse s = "_"
fun kindvarp acc s = if kindvarp0 s then SOME (s::acc) else NONE

fun kindsymp0 s =
    case s of
      "(" => false
    | ")" => false
    | "," => false
    | "[" => false
    | "]" => false
    | "'" => false
    | "\"" => false
    | _ => UnicodeChars.isSymbolic s
fun kindsymp acc s = if kindsymp0 s then SOME (s::acc) else NONE

fun numeralkindp (pfx,sfx) s = let
  val c = String.sub(s,0)
in
  if isSome sfx then NONE
  else if Char.isDigit c then SOME (s::pfx, sfx)
  else if Char.isAlpha c then SOME (pfx, SOME c)
  else NONE
end

fun MkNumKind (pfx, sfx) =
    case sfx of
      NONE =>
        let val s = munge pfx
        in KindNumeral s
        end
    | SOME _ => Error (BT_Numeral (Arbnum.fromString (munge pfx), sfx))


fun split_and_check fb s locn = let
  (* if the first character of s is non-alphanumeric character, then it
     will be a symbolic blob.  *)
  val ((s0,i), srest) = valOf (UTF8.getChar s)
  fun nadvance n tt =
      if size s = n then ((fn () => advance fb),(tt,locn))
      else let
          val (locn',locn'') = locn.split_at n locn
        in
          ((fn () => replace_current (BT_Ident (String.extract(s, n, NONE)),
                                      locn'') fb),
           (tt,locn'))
        end
  fun consume_kind p con acc s =
      case UTF8.getChar s of
        NONE => ((fn () => advance fb), (con acc,locn))
      | SOME ((c,_), rest) => let
        in
          case p acc c of
            NONE => let
              val res = con acc
            in
              nadvance (toksize res) res
            end
          | SOME acc' => consume_kind p con acc' rest
        end
  val error = ((fn () => advance fb), (Error (BT_Ident s), locn))
  open UnicodeChars
in
  (*if (* "ar" *) s0 = "a" andalso size s > 1 andalso String.sub(s,1) = #"r"
     then nadvance 2 KindArity
  else*) if isAlpha s0 then consume_kind kindidentp MkKindIdent ([s0],[]) srest
  else if s0 = "'"   then consume_kind kindvarp (KindVar o munge) [s0] srest
  (* else if isDigit s0 then consume_kind kindnump MkKindNumeral [s0] srest *)
  else if Char.isDigit (String.sub(s0,0)) then
    consume_kind numeralkindp MkNumKind ([s0], NONE) srest
  else if s0 = "(" then nadvance 1 LParen
  else if s0 = ")" then nadvance 1 RParen
  else if s0 = ":" andalso not(size s > 1 andalso String.sub(s,1) = #"]")
                   then nadvance 1 KindRankCst
  else if s0 = "," then nadvance 1 Comma
  else if s0 = "[" then nadvance 1 LBracket
  else if s0 = "]" then nadvance 1 RBracket
  else if s0 = "\"" then error
  else consume_kind kindsymp (KindSymbol o munge) [s0] srest
end

fun handle_num numinfo =
    case numinfo of
      (num, NONE) => (KindNumeral (Int.toString(Arbnum.toInt num))
                      handle Overflow => Error (BT_Numeral numinfo))
    | (num, SOME _) => Error (BT_Numeral numinfo)

fun kindtok_of fb = let
  val (bt,locn) = current fb
in
  case bt of
    BT_Numeral numinfo => ((fn () => advance fb), (handle_num numinfo, locn))
  | BT_AQ x => ((fn () => advance fb), (AQ x,locn))
  | BT_EOI => ((fn () => ()), (Error bt,locn))
  | BT_Ident s => split_and_check fb s locn
end

fun token_string (KindIdent s) = s
  | token_string (KindVar s) = s
  | token_string (KindSymbol s) = s
  | token_string (KindNumeral s) = s
  | token_string  KindRankCst  = ":"
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
