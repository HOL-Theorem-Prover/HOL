(* add comments ; comments should skip over antiquotations *)
datatype 'a term_token =
  Ident of string | Symbol of string | Antiquote of 'a

open optmonad monadic_parse
open fragstr

infix >- >> ++

open HOLtokens
infix OR

fun member x [] = false
  | member x (y::ys) = x = y orelse member x ys

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
fun nonagg_c c = member c non_aggregating_chars

fun s_has_nonagg_char s = length (String.fields nonagg_c s) <> 1

fun pushback_s s = if s <> "" then pushback (QUOTE s) else ok
fun split_into_regions s = let
  val ss = Substring.all s
  val P =
    case Substring.getc ss of
      SOME(c, _) => if HOLid c then HOLid
                    else HOLsym
    | NONE => raise Fail "term_tokens.split_into_regions given empty string"
  val (r1, r2) = Substring.splitl P ss
in
  (Substring.string r1, Substring.string r2)
end

fun compare_pos (((pfx1, _), n1), ((pfx2, _), n2)) = let
  open Substring
  val s1 = size pfx1 and s2 = size pfx2
in
  if s1 = 0 andalso s2 = 0 then Int.compare(String.size n2, String.size n1)
  else Int.compare(s1, s2)
end

fun lex keywords0 = let
  val non_agg_specials = List.filter s_has_nonagg_char keywords0
  val keywords =
    Listsort.sort (fn (s1, s2) => Int.compare(size s2, size s1)) keywords0
  fun doit dollarp s = let
    open Substring
    val ss = all s
    fun dollarit s = if dollarp then Ident s else Symbol s
    val non_agg_positions0 =
      map (fn na => (position na ss, na)) non_agg_specials
    val non_agg_positions = Listsort.sort compare_pos non_agg_positions0
    val ((pfx, sfx), na) = hd non_agg_positions
    fun deal_with_tokensubstring ts =
      if member (string ts) keywords then return (dollarit (string ts))
      else let
        val (r1, r2) = split_into_regions (string ts)
      in
        pushback_s r2 >>
        (if not dollarp andalso member r1 keywords then return (Symbol r1)
         else return (Ident r1))
      end
  in
    if (size pfx = 0) then
      pushback_s (string (triml (String.size na) sfx)) >> return (dollarit na)
    else
      pushback_s (string sfx) >> deal_with_tokensubstring pfx
  end

in
  (token antiq >- return o Antiquote) ++
  (token ((optional (item #"$")) >- return o isSome >-   (fn b =>
          many1_charP (HOLsym OR HOLid) >- doit b)))
end







fun token_string (Ident s) = s
  | token_string (Symbol s) = s
  | token_string _ = raise Fail "token_string of something with no string"
fun dest_aq (Antiquote x) = x
  | dest_aq _ = raise Fail "dest_aq of non antiquote token"

fun is_ident (Ident _) = true
  | is_ident _ = false
fun is_symbol (Symbol _) = true
  | is_symbol _ = false
fun is_aq (Antiquote _) = true
  | is_aq _ = false

