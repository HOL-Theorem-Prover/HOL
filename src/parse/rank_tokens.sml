structure rank_tokens :> rank_tokens =
struct

  datatype 'a rank_token
      = RankNumeral of string
      | AQ of 'a
      | Error of 'a base_tokens.base_token

fun toksize tt =
    case tt of
      RankNumeral s => size s
(* if n = 0 then 1 else Real.ceil (Math.log10 (Real.fromInt (n+1))) *)
    | _ => 0 (* a lie, but unimportant given calling context *)


val ERR = Feedback.mk_HOL_ERR "rank_tokens"

open qbuf base_tokens

fun munge slist = String.concat (List.rev slist)

fun numeralrankp (pfx,sfx) s = let
  val c = String.sub(s,0)
in
  if isSome sfx then NONE
  else if Char.isDigit c then SOME (s::pfx, sfx)
  else if Char.isAlpha c then SOME (pfx, SOME c)
  else NONE
end

fun MkNumRank (pfx, sfx) =
    case sfx of
      NONE =>
        let val s = munge pfx
        in RankNumeral s
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
  fun consume_rank p con acc s =
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
          | SOME acc' => consume_rank p con acc' rest
        end
  val error = ((fn () => advance fb), (Error (BT_Ident s), locn))
  open UnicodeChars
in
  if Char.isDigit (String.sub(s0,0)) then
    consume_rank numeralrankp MkNumRank ([s0], NONE) srest
(*
  else if s0 = "(" then nadvance 1 LParen
  else if s0 = ")" then nadvance 1 RParen
*)
  else error
end

fun handle_num numinfo =
    case numinfo of
      (num, NONE) => (RankNumeral (Int.toString(Arbnum.toInt num))
                      handle Overflow => Error (BT_Numeral numinfo))
    | (num, SOME _) => Error (BT_Numeral numinfo)

fun ranktok_of fb = let
  val (bt,locn) = current fb
in
  case bt of
    BT_Numeral numinfo => ((fn () => advance fb), (handle_num numinfo, locn))
  | BT_AQ x => ((fn () => advance fb), (AQ x,locn))
  | BT_EOI => ((fn () => ()), (Error bt,locn))
  | BT_Ident s => split_and_check fb s locn
  | BT_DecimalFraction r => ((fn () => ()), (Error bt, locn))
end

fun token_string (RankNumeral s) = s
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (AQ x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote rank token"

fun is_rankaq (AQ _) = true
  | is_rankaq _ = false

end
