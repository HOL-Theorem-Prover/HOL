structure term_tokens :> term_tokens =
struct

  open qbuf base_tokens locn

  val WARN = Feedback.HOL_WARNING "term lexer" ""

  datatype 'a term_token =
    Ident of string
  | Antiquote of 'a
  | Numeral of (Arbnum.num * char option)
  | QIdent of (string * string)


val non_aggregating_chars =
    foldl (fn (c, cs) => CharSet.add(cs,c)) CharSet.empty
          (explode "()[]{}~.,;-")
fun nonagg_c c = CharSet.member(non_aggregating_chars, c)

fun s_has_nonagg_char s = length (String.fields nonagg_c s) <> 1 orelse
                          s = UnicodeChars.neg

fun term_symbolp s = UnicodeChars.isSymbolic s andalso
                     not (s_has_nonagg_char s) andalso
                     s <> "\"" andalso s <> "'" andalso s <> "_"
fun const_symbolp s = Char.isPunct (String.sub(s,0)) andalso s <> ")" andalso
                      s <> "_" andalso s <> "'" andalso s <> "\""

fun term_identp s = UnicodeChars.isMLIdent s andalso s <> UnicodeChars.lambda
fun const_identp s = Char.isAlphaNum (String.sub(s,0)) orelse s = "_" orelse
                     s = "'"
fun const_identstartp s = const_identp s andalso
                          not (Char.isDigit (String.sub(s,0)))

fun ishexdigit s = let
  val c = Char.toLower (String.sub(s,0))
in
  #"a" <= c andalso c <= #"f"
end
fun numberp s = Char.isDigit (String.sub(s,0)) orelse s = "_" orelse
                s = "x" orelse
                ishexdigit s

fun categorise c =
    if s_has_nonagg_char c orelse c = UnicodeChars.neg then s_has_nonagg_char
    else if term_identp c then term_identp
    else if Char.isDigit (String.sub(c,0)) then numberp
    else term_symbolp

fun constid_categorise c =
    if const_identstartp c then const_identp
    else if const_symbolp c then const_symbolp
    else raise Fail (c ^ " is not a valid constant name constituent")


fun mixed s = let
  open UnicodeChars UTF8
  val (c,s) = case getChar s of
            NONE => raise Fail "Can't use emptystring as a grammar token"
          | SOME ((c,_), s) => (c,s)
  val test = categorise c
  fun allok s =
      case getChar s of
        NONE => true
      | SOME ((s, i), rest) => test s andalso allok rest
in
  not (allok s)
end

(* lexer guarantees:

     All Idents fit into one of the following categories :

     * a double-quote delimited string
     * a character literal, consisting of four characters, # " <anything> "
     * an alpha-numeric identifier (first character will be one
       of _ ' A-Z a-z), possibly preceded by a dollar sign
     * a symbolic identifier = a chain of symbol characters (again possibly
       preceded by a dollar sign).

     A symbol is any  printable ASCII character EXCEPT
       A-Z a-z 0-9 $ "
     " is used exclusively for strings, and $ is used for
     token 'quoting' as well as being the separator for qualified identifiers.
*)

fun str_all P s = let
  fun recurse ss =
      case Substring.getc ss of
        NONE => true
      | SOME (c, ss') => P c andalso recurse ss'
in
  recurse (Substring.all s)
end

fun MkID (s, loc) = let
  val c = String.sub(s,0)
in
  if Char.isDigit c then
    Numeral (base_tokens.parse_numeric_literal (s, loc))
  else if c = #"'" then
    if str_all (fn c => c = #"'") s then Ident s
    else raise LEX_ERR ("Term idents can't begin with prime characters",loc)
  else Ident s
end

open qbuf

fun split_ident mixedset s locn qb = let
  val {advance,replace_current} = qb
  val s0 = String.sub(s, 0)
  val is_char = s0 = #"#" andalso size s > 1 andalso String.sub(s,1) = #"\""
  val ID = Ident
in
  if is_char orelse s0 = #"\"" then (advance(); (ID s, locn))
  else if s0 = #"$" then let
      val (tok,locn') = split_ident mixedset
                                   (String.extract(s, 1, NONE))
                                   (locn.move_start 1 locn) qb
    in
      case tok of
        Ident s' => (ID ("$" ^ s'), locn.move_start ~1 locn')
      | _ => raise LEX_ERR ("Can't use $-quoting of this sort of token", locn')
    end
  else if not (mixed s) andalso not (s_has_nonagg_char s) then
    (advance (); (MkID (s, locn), locn))
  else
    case UTF8Set.longest_pfx_member(mixedset, s) of
      NONE => (* identifier blob doesn't occur in list of known keywords *) let
      in
        case UTF8.getChar s of
          NONE => raise LEX_ERR ("Token is empty string??", locn)
        | SOME ((c,i),rest) => let
            open UnicodeChars
            fun grab test acc s =
                case UTF8.getChar s of
                  NONE => (String.concat (List.rev acc), "")
                | SOME((s,i),rest) => let
                  in
                    if test s then grab test (s::acc) rest
                    else (String.concat (List.rev acc), s^rest)
                  end
            val (tok,sfx) =
                if s_has_nonagg_char c then (ID c, rest)
                else let
                    val (pfx0, sfx0) = grab (categorise c) [c] rest
                  in
                    if size sfx0 <> 0 andalso String.sub(sfx0,0) = #"$" then
                      if size sfx0 > 1 then let
                          val sfx0_1 = String.extract(sfx0, 1, NONE)
	                  val c0 = String.sub(sfx0_1, 0)
                          val rest = String.extract(sfx0_1, 1, NONE)
	                  val (qid2, sfx) =
                              grab (constid_categorise (str c0)) [str c0] rest
                              handle Fail s => raise LEX_ERR (s, locn)
	                in
	                  (QIdent(pfx0,qid2), sfx)
                        end
                      else
                        raise LEX_ERR ("Malformed qualified ident", locn)
                    else (MkID (pfx0,locn), sfx0)
                  end
            val (locn1, locn2) = locn.split_at (size s - size sfx) locn
          in
            if size sfx <> 0 then
              (replace_current (BT_Ident sfx,locn2); (tok, locn1))
            else
              (advance (); (tok, locn))
          end
      end
    | SOME {pfx,rest} => let
        val (locn1,locn2) = locn.split_at (size pfx) locn
      in
        if size rest = 0 then (advance(); (ID s, locn))
        else
          (replace_current (BT_Ident rest,locn2); (ID pfx, locn1))
      end
end



fun lex keywords0 = let
  fun test s = mixed s orelse s_has_nonagg_char s
  val mixed = List.filter test keywords0
  val mixedset = UTF8Set.addList(UTF8Set.empty, mixed)
  val split = split_ident mixedset
in
fn qb => let
   val (bt,locn) = current qb
   in
     case bt of
         BT_Numeral p   => (advance qb; SOME (Numeral p,locn))
       | BT_AQ x        => (advance qb; SOME (Antiquote x,locn))
       | BT_EOI         => NONE
       | BT_Ident s     => let
           val qbfns = {advance = (fn () => advance qb),
                        replace_current = (fn p => replace_current p qb)}
           val (tok,locn') = split s locn qbfns
         in
           SOME (tok,locn')
         end
   end
end

fun user_split_ident keywords = let
  fun test s = mixed s orelse s_has_nonagg_char s
  val mixed = List.filter test keywords
  val mixedset = UTF8Set.addList (UTF8Set.empty, mixed)
in
  fn s => let
       val pushback = ref ""
       fun a () = ()
       fun rc (btid, _) =
           case btid of
             BT_Ident s => (pushback := s)
           | _ => () (* shouldn't happen *)
       val _ = split_ident mixedset s locn.Loc_None
                           {advance=a, replace_current=rc}
     in
       (String.substring(s,0,size s - size (!pushback)),
        !pushback)
     end
end

fun token_string (Ident s) = s
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (Antiquote x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote token"

fun is_ident (Ident _) = true
  | is_ident _ = false
fun is_aq (Antiquote _) = true
  | is_aq _ = false

end (* struct *)

(* good parsing/lexing test:

time Term
    `~((~v5 \/ ~v0 \/ v0) /\ (~v5 \/ ~v2 \/ v2) /\ (~v5 \/ ~v31 \/ v31) /\
       (~v5 \/ ~v5 \/ v5) /\ (~v13 \/ ~v0 \/ v7) /\ (~v13 \/ ~v2 \/ v9) /\
       (~v13 \/ ~v31 \/ v11) /\ (~v13 \/ ~v5 \/ v13) /\ (~v20 \/ ~v0 \/ v15) /\
       (~v20 \/ ~v2 \/ v16) /\ (~v20 \/ ~v31 \/ v18) /\ (~v20 \/ ~v5 \/ v20) /\
       (~v28 \/ ~v0 \/ v22) /\ (~v28 \/ ~v2 \/ v24) /\ (~v28 \/ ~v31 \/ v26) /\
       (~v28 \/ ~v5 \/ v28) /\ (~v31 \/ ~v7 \/ v0) /\ (~v31 \/ ~v9 \/ v2) /\
       (~v31 \/ ~v11 \/ v31) /\ (~v31 \/ ~v13 \/ v5) /\ (~v11 \/ ~v7 \/ v7) /\
       (~v11 \/ ~v9 \/ v9) /\ (~v11 \/ ~v11 \/ v11) /\ (~v11 \/ ~v13 \/ v13) /\
       (~v18 \/ ~v7 \/ v15) /\ (~v18 \/ ~v9 \/ v16) /\ (~v18 \/ ~v11 \/ v18) /\
       (~v18 \/ ~v13 \/ v20) /\ (~v26 \/ ~v7 \/ v22) /\ (~v26 \/ ~v9 \/ v24) /\
       (~v26 \/ ~v11 \/ v26) /\ (~v26 \/ ~v13 \/ v28) /\ (~v2 \/ ~v15 \/ v0) /\
       (~v2 \/ ~v16 \/ v2) /\ (~v2 \/ ~v18 \/ v31) /\ (~v2 \/ ~v20 \/ v5) /\
       (~v9 \/ ~v15 \/ v7) /\ (~v9 \/ ~v16 \/ v9) /\ (~v9 \/ ~v18 \/ v11) /\
       (~v9 \/ ~v20 \/ v13) /\ (~v16 \/ ~v15 \/ v15) /\
       (~v16 \/ ~v16 \/ v16) /\ (~v16 \/ ~v18 \/ v18) /\
       (~v16 \/ ~v20 \/ v20) /\ (~v24 \/ ~v15 \/ v22) /\
       (~v24 \/ ~v16 \/ v24) /\ (~v24 \/ ~v18 \/ v26) /\
       (~v24 \/ ~v20 \/ v28) /\ (~v0 \/ ~v22 \/ v0) /\ (~v0 \/ ~v24 \/ v2) /\
       (~v0 \/ ~v26 \/ v31) /\ (~v0 \/ ~v28 \/ v5) /\ (~v7 \/ ~v22 \/ v7) /\
       (~v7 \/ ~v24 \/ v9) /\ (~v7 \/ ~v26 \/ v11) /\ (~v7 \/ ~v28 \/ v13) /\
       (~v15 \/ ~v22 \/ v15) /\ (~v15 \/ ~v24 \/ v16) /\
       (~v15 \/ ~v26 \/ v18) /\ (~v15 \/ ~v28 \/ v20) /\
       (~v22 \/ ~v22 \/ v22) /\ (~v22 \/ ~v24 \/ v24) /\
       (~v22 \/ ~v26 \/ v26) /\ (~v22 \/ ~v28 \/ v28) /\ (~v6 \/ ~v1 \/ v1) /\
       (~v6 \/ ~v3 \/ v3) /\ (~v6 \/ ~v4 \/ v4) /\ (~v6 \/ ~v6 \/ v6) /\
       (~v14 \/ ~v1 \/ v8) /\ (~v14 \/ ~v3 \/ v10) /\ (~v14 \/ ~v4 \/ v12) /\
       (~v14 \/ ~v6 \/ v14) /\ (~v21 \/ ~v1 \/ v30) /\ (~v21 \/ ~v3 \/ v17) /\
       (~v21 \/ ~v4 \/ v19) /\ (~v21 \/ ~v6 \/ v21) /\ (~v29 \/ ~v1 \/ v23) /\
       (~v29 \/ ~v3 \/ v25) /\ (~v29 \/ ~v4 \/ v27) /\ (~v29 \/ ~v6 \/ v29) /\
       (~v4 \/ ~v8 \/ v1) /\ (~v4 \/ ~v10 \/ v3) /\ (~v4 \/ ~v12 \/ v4) /\
       (~v4 \/ ~v14 \/ v6) /\ (~v12 \/ ~v8 \/ v8) /\ (~v12 \/ ~v10 \/ v10) /\
       (~v12 \/ ~v12 \/ v12) /\ (~v12 \/ ~v14 \/ v14) /\
       (~v19 \/ ~v8 \/ v30) /\ (~v19 \/ ~v10 \/ v17) /\
       (~v19 \/ ~v12 \/ v19) /\ (~v19 \/ ~v14 \/ v21) /\
       (~v27 \/ ~v8 \/ v23) /\ (~v27 \/ ~v10 \/ v25) /\
       (~v27 \/ ~v12 \/ v27) /\ (~v27 \/ ~v14 \/ v29) /\ (~v3 \/ ~v30 \/ v1) /\
       (~v3 \/ ~v17 \/ v3) /\ (~v3 \/ ~v19 \/ v4) /\ (~v3 \/ ~v21 \/ v6) /\
       (~v10 \/ ~v30 \/ v8) /\ (~v10 \/ ~v17 \/ v10) /\
       (~v10 \/ ~v19 \/ v12) /\ (~v10 \/ ~v21 \/ v14) /\
       (~v17 \/ ~v30 \/ v30) /\ (~v17 \/ ~v17 \/ v17) /\
       (~v17 \/ ~v19 \/ v19) /\ (~v17 \/ ~v21 \/ v21) /\
       (~v25 \/ ~v30 \/ v23) /\ (~v25 \/ ~v17 \/ v25) /\
       (~v25 \/ ~v19 \/ v27) /\ (~v25 \/ ~v21 \/ v29) /\ (~v1 \/ ~v23 \/ v1) /\
       (~v1 \/ ~v25 \/ v3) /\ (~v1 \/ ~v27 \/ v4) /\ (~v1 \/ ~v29 \/ v6) /\
       (~v8 \/ ~v23 \/ v8) /\ (~v8 \/ ~v25 \/ v10) /\ (~v8 \/ ~v27 \/ v12) /\
       (~v8 \/ ~v29 \/ v14) /\ (~v30 \/ ~v23 \/ v30) /\
       (~v30 \/ ~v25 \/ v17) /\ (~v30 \/ ~v27 \/ v19) /\
       (~v30 \/ ~v29 \/ v21) /\ (~v23 \/ ~v23 \/ v23) /\
       (~v23 \/ ~v25 \/ v25) /\ (~v23 \/ ~v27 \/ v27) /\
       (~v23 \/ ~v29 \/ v29) /\ (~v29 \/ v1) /\ (~v21 \/ v3) /\ (~v14 \/ v4) /\
       (~v6 \/ v6) /\ (~v27 \/ v8) /\ (~v19 \/ v10) /\ (~v12 \/ v12) /\
       (~v4 \/ v14) /\ (~v25 \/ v30) /\ (~v17 \/ v17) /\ (~v10 \/ v19) /\
       (~v3 \/ v21) /\ (~v23 \/ v23) /\ (~v30 \/ v25) /\ (~v8 \/ v27) /\
       (~v1 \/ v29) /\ (v0 \/ v1) /\ (v2 \/ v3) /\ (v31 \/ v4) /\ (v5 \/ v6) /\
       (v7 \/ v8) /\ (v9 \/ v10) /\ (v11 \/ v12) /\ (v13 \/ v14) /\
       (v15 \/ v30) /\ (v16 \/ v17) /\ (v18 \/ v19) /\ (v20 \/ v21) /\
       (v22 \/ v23) /\ (v24 \/ v25) /\ (v26 \/ v27) /\ (v28 \/ v29) /\ ~v30 /\
       ~v31)`;

*)
