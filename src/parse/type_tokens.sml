structure type_tokens :> type_tokens =
struct

val greek_tyvars = ref true

val _ = Feedback.register_btrace ("Greek tyvars", greek_tyvars)

datatype 'a type_token
     = TypeIdent of string
     | QTypeIdent of string * string
     | TypeSymbol of string
     | TypeVar of string
     | Comma
     | LParen
     | RParen
     | LBracket
     | RBracket
     | AQ of 'a
     | Error of 'a base_tokens.base_token

fun toksize tt =
    case tt of
      TypeIdent s => size s
    | QTypeIdent (s1,s2) => size s1 + size s2 + 1
    | TypeSymbol s => size s
    | TypeVar s => size s
    | Comma => 1
    | LParen => 1
    | RParen => 1
    | LBracket => 1
    | _ => 0 (* a lie, but unimportant given calling context *)


val ERR = Feedback.mk_HOL_ERR "type_tokens"

open qbuf base_tokens

fun munge slist = String.concat (List.rev slist)


fun special_symb c = c = #"(" orelse c = #")" orelse c = #","

fun typeidentp (part1, part2) s = let
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
fun MkTypeIdent (part1, part2) =
    if null part2 then TypeIdent (munge part1)
    else if length part2 = 1 then
      raise ERR "MkTypeIdent" "Malformed qualified identifier (no part after $)"
    else QTypeIdent(munge part1, String.extract (munge part2, 1, NONE))

fun typevarp0 s = UnicodeChars.isAlphaNum s orelse s = "'" orelse s = "_"
fun typevarp acc s = if typevarp0 s then SOME (s::acc) else NONE

fun typesymp0 s =
    case s of
      "(" => false
    | ")" => false
    | "," => false
    | "[" => false
    | "]" => false
    | "'" => false
    | "\"" => false
    | _ => UnicodeChars.isSymbolic s
fun typesymp acc s = if typesymp0 s then SOME (s::acc) else NONE

fun numeraltypep (pfx,sfx) s = let
  val c = String.sub(s,0)
in
  if isSome sfx then NONE
  else if Char.isDigit c then SOME (s::pfx, sfx)
  else if Char.isAlpha c then SOME (pfx, SOME c)
  else NONE
end

fun MkNumType (pfx, sfx) =
    case sfx of
      NONE => TypeIdent (munge pfx)
    | SOME _ => Error (BT_Numeral (Arbnum.fromString (munge pfx), sfx))

fun isGreekLower i = (* but not lambda *)
    0x3B1 <= i andalso i <= 0x3C9 andalso i <> 0x3BB

fun split_and_check fb s locn = let
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
  fun consume_type p con acc s =
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
          | SOME acc' => consume_type p con acc' rest
        end
  open UnicodeChars
in
  if s0 = "'" orelse (isGreekLower i andalso !greek_tyvars) then
    consume_type typevarp (TypeVar o munge) [s0] srest
  else if isAlpha s0 then consume_type typeidentp MkTypeIdent ([s0],[]) srest
  else if Char.isDigit (String.sub(s0,0)) then
    consume_type numeraltypep MkNumType ([s0], NONE) srest
  else if s0 = "(" then nadvance 1 LParen
  else if s0 = ")" then nadvance 1 RParen
  else if s0 = "," then nadvance 1 Comma
  else if s0 = "[" then nadvance 1 LBracket
  else if s0 = "]" then nadvance 1 RBracket
  else if s0 = "\"" then ((fn () => advance fb), (Error (BT_Ident s),locn))
  else consume_type typesymp (TypeSymbol o munge) [s0] srest
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
