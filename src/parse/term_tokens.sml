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

fun failwith s x = (print s ; fail) x
fun qstring_contents strm =
  (many (many1_charP q_ok ++
         (string "\\\\" >> return "\\") ++
         (string "\\\"" >> return "\"") ++
         (string "\\n" >> return "\n") ++
         (item #"\\" >> bslash_error) ++
         (item #"\n" >>
          failwith "Newlines must not appear inside strings.\n") ++
         (antiq >>
          failwith "Must not have antiquotations inside strings.\n")) >-
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


fun lex keywords0 afn = let
  val non_agg_specials = List.filter s_has_nonagg_char keywords0
  fun doit dollarp s = let
    open Substring
    val ss = all s
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
in
  (token antiq >- return o Antiquote) ++
  (token quoted_string >- return o Ident) ++
  (token (optional (item #"$") >- (return o isSome) >-
          (fn dollared =>
           std_id >-
           (fn idstr =>
            ((item #"$" >>
              (many1_charP HOLsym ++ std_id) >-
              (fn partname =>
               if Lib.mem idstr (afn()) then
                 return (Ident(idstr^"$"^partname))
               else
                 raise LEX_ERR ("invalid theory name: "^idstr))) ++
             (return (Ident ((if dollared then "$" else "")^idstr)))))))) ++
  (token (many1_charP Char.isDigit >-       (fn dp =>
          optional (itemP Char.isAlpha) >-  (fn csuffix =>
          return (Numeral(dp, Option.map Char.toLower csuffix)))))) ++
  (token ((optional (item #"$")) >- return o isSome >-   (fn b =>
          many1_charP (HOLsym OR HOLspecials) >- doit b))) ++
  (token (many1_charP (not o Char.isSpace) >-
   (fn s => raise LEX_ERR ("can't make lexical sense of "^s))))
end







fun token_string (Ident s) = s
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (Antiquote x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote token"

fun is_ident (Ident _) = true
  | is_ident _ = false
fun is_aq (Antiquote _) = true
  | is_aq _ = false

