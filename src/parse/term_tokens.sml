(* add comments ; comments should skip over antiquotations *)
datatype 'a term_token =
  Ident of string | Antiquote of 'a | Numeral of (string * char option)

open optmonad monadic_parse
open fragstr

infix >- >> ++ >->

exception LEX_ERR of string

open HOLtokens
infix OR

val quotec = #"\"" and bslashc = #"\\" and nlc = #"\n"
fun q_ok c = c <> quotec andalso c <> bslashc andalso c <> nlc
fun strip_eqs strm =
  (many
   (monadic_parse.itemP (fn ANTIQUOTE _ => false | QUOTE s => size s = 0)))
  strm
fun bslash_error strm =
  (strip_eqs >> get >-
   (fn x =>
    case x of
      QUOTE s =>
        (Lib.mesg true ("Don't recognise \\"^String.substring(s,0,1)^
                        " as a valid backslash escape.\n");
         pushback x >> fail)
    | ANTIQUOTE _ => let
      in
        Lib.mesg true "Must not have antiquotations inside strings.\n";
        pushback x >> fail
      end)) strm

fun failwith s x = (Lib.mesg true s ; fail) x
fun qstring_contents strm =
  (many (many1_charP q_ok ++
         (string "\\\\" >> return "\\") ++
         (string "\\\"" >> return "\"") ++
         (string "\\n" >> return "\n") ++
         (item #"\\" >> bslash_error) ++
         (item #"\n" >>
          failwith "Newlines must not appear inside strings.") ++
         (antiq >>
          failwith "Must not have antiquotations inside strings.")) >-
   (fn slist => return (String.concat slist))) strm;

fun quoted_string strm =
  ((item #"\"" >> qstring_contents >-> item #"\"") >-
   (fn c => return ("\""^c^"\""))) strm

(* Terminology and basic algorithm
   -------------------------------

   An identifier character is one of A-Z a-z 0-9 _ and '.

   A punctuation character is pretty much anything else except $.

   A non-aggregating character is one of:
     ~ ( ) [ ] { }
   All non-aggregating characters are punctuation characters.

   A non-aggregating string is a string including one of the above.

   We are given a list of keywords, or specials, and must come up with a
   lexing function.  The function must return a sequence of Idents, Symbols
   and antiquotations.  Idents are undistinguished identifiers, symbols are
   from the list of specials.

   The first thing to do is to grab the next non-empty sequence of
   identifier and punctuation characters with an optional leading
   dollar-sign.  (If there isn't one, there will be an anti-quote which
   can be returned.)

   This string (ignoring the dollar-sign if present) needs to yield
   the string corresponding to the next token, and then this string needs to
   be classified as either a symbol or an ident.

   If the string includes any non-aggregating characters
   from the strings in the list of specials, then

     * split it into two substrings s and t such that s^t = the
       original string, and t has a non-aggregating string from the
       specials list as a prefix.  Further, t's prefix is the first
       such non-aggregating string.

     * if s non-empty, then s is the token string, pushback t.
     * otherwise the longest prefix of t which is a non-aggregating string
       on the list of specials is the token string, push back the rest of t.

  If the string has no non-aggregating characters, it is the token string.

  If there is a $, split the string into identifier and punctuation
  regions and return Ident of the first region, pushing back the rest.

  To get this far, we have a string with no leading dollar.  If the
  whole string is equal to a special, return Symbol of the whole
  string.  Otherwise split the string into identifier and punctuation
  regions, pushback all but the first region, and then if the first is a
  special, return Symbol of it, else return Ident of it.
*)

val non_aggregating_chars = explode "()[]{}~."
fun nonagg_c c = Lib.mem c non_aggregating_chars

fun s_has_nonagg_char s = length (String.fields nonagg_c s) <> 1

fun pushback_s s = if s <> "" then pushback (QUOTE s) else ok

fun compare_pos (((pfx1, _), n1), ((pfx2, _), n2)) = let
  open Substring
  val s1 = size pfx1 and s2 = size pfx2
in
  if s1 = 0 andalso s2 = 0 then Int.compare(String.size n2, String.size n1)
  else Int.compare(s1, s2)
end

fun std_id strm  =
  (itemP (fromLex Lexis.alphabet) >-
   (fn c1 => many_charP (fromLex Lexis.alphanumerics) >-
    (fn remainder => return (str c1 ^ remainder)))) strm

fun strip_eqs [] = []
  | strip_eqs (QUOTE ""::xs) = strip_eqs xs
  | strip_eqs x = x

fun lex keywords0 afn frags0 = let
  val non_agg_specials = List.filter s_has_nonagg_char keywords0
  fun handle_symbolics dollarp ss = let
    open Substring
    fun dollarit s = Ident ((if dollarp then "$" else "") ^ s)
    val non_agg_positions0 =
      map (fn na => (position na ss, na)) non_agg_specials
    val non_agg_positions = Listsort.sort compare_pos non_agg_positions0
    val ((pfx, sfx), na) = hd non_agg_positions
  in
    if (size pfx = 0) then
      pushback_s (string (triml (String.size na) sfx)) >> return (dollarit na)
    else
      pushback_s (string sfx) >> return (dollarit (string pfx))
  end
  val (frags1, f1) = token get frags0
in
  case f1 of
    NONE => (frags1, NONE)
  | SOME (ANTIQUOTE aq) => (frags1, SOME (Antiquote aq))
  | SOME (q as (QUOTE s)) => let
      (* know that s is a non-empty string, whose first character is not
         white-space *)
      val c1 = String.sub(s,0)
      val (frags2, _) = pushback q frags1
    in
      if Char.isDigit c1 then let
        val (frags3, dp) = many1_charP Char.isDigit frags2
        val (frags4, optc) = optional (itemP Char.isAlpha) frags3
      in
        (frags4,
         SOME (Numeral(valOf dp, Option.map Char.toLower (valOf optc))))
      end
      else if c1 = quotec then let
        val (final_frags, stropt) = quoted_string frags2
      in
        case stropt of
          NONE => raise LEX_ERR "Quoted string fails to terminate"
        | SOME s => (final_frags, SOME (Ident s))
      end
      else let (* it's some sort of symbol *)
        (* get everything up to the next whitespace *)
        val (frags3, stropt) = many1_charP (not o Char.isSpace) frags2
        open Substring
        val str0 = all (valOf stropt)
        val (dollared, str) =
          if sub(str0, 0) = #"$" then (true, slice(str0, 1, NONE))
          else (false, str0)
        val c2 = sub(str, 0)
        fun ok_inid c =
          Char.isAlpha c orelse Char.isDigit c orelse
          c = #"_" orelse c = #"'"
      in
        (* c2 is first character of identifier, ignoring dollar-signs *)
        if Char.isAlpha c2 then let
          (* could be a long-ID or a normal identifier *)
          val (id, rest) = splitl ok_inid str
        in
          if not (isEmpty rest) andalso sub(rest,0) = #"$" then
            (* this is a possible long-ID *)
            if Lib.mem (string id) (afn()) then let
              (* the id string is a possible theory name *)
              val rest = slice(rest, 1, NONE) (* skip dollar sign *)
            in
              case getc rest of
                NONE =>
                  raise LEX_ERR ("Long $-id "^string id^" with no sub-part")
              | SOME(c3, rest) => let (* c3 will be alphabetic or a hol sym *)
                  fun grab_id P = let
                    val (sub_id, push_this_back) = splitl P rest
                    val final_id = string (span(str, sub_id))
                      (* ignores any leading dollar-sign *)
                    val (final_frags,_) =
                      pushback_s (string push_this_back) frags3
                  in
                    (final_frags, SOME (Ident final_id))
                  end
                in
                  if Char.isAlpha c3 then grab_id ok_inid
                  else
                    if fromLex Lexis.hol_symbols c3 then
                      grab_id (fromLex Lexis.hol_symbols)
                    else
                      raise LEX_ERR ("Sub-component starting with "^
                                     String.str c3^ " after "^string id^
                                     " lexically bad")
                end
            end
            else
              raise LEX_ERR (string id ^ " not a known theory name")
          else (* not a possible long-ID *) let
            val (final_frags, _) = pushback_s (string rest) frags3
            val final_id = string (span(str0, id))
            (* grabs dollar-sign, if any *)
          in
            (final_frags, SOME (Ident final_id))
          end
        end
        else (* not (Char.isAlpha c2) *)
          if HOLsym c2 orelse HOLspecials c2 then let
            val (ss, push_this_back) = splitl (HOLsym OR HOLspecials) str
            val (final_frags, _) = pushback_s (string push_this_back) frags3
          in
            handle_symbolics dollared ss final_frags
          end
          else
            raise LEX_ERR ("Can't make lexical sense of "^string str)
      end (* "some sort of symbol" let *)
    end (* SOME (QUOTE s) let *)
end (* newlex *)












fun token_string (Ident s) = s
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (Antiquote x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote token"

fun is_ident (Ident _) = true
  | is_ident _ = false
fun is_aq (Antiquote _) = true
  | is_aq _ = false



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
