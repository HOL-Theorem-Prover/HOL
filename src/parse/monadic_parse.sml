(* PROSPER project (Plug-in Interface) *)
(* Copyright University of Cambridge 1999 *)
(* Author: Michael Norrish *)
(* $Id$ *)
structure monadic_parse :> monadic_parse = struct
open optmonad
infix >-
infix >>
infix ++
infix >-> +++

exception NoParseResult of string

type ('a, 'b) Parser = ('b list, 'a) optmonad

fun get [] = ([], NONE)
  | get (x::xs) = (xs, SOME x)

fun peek [] = ([], NONE)
  | peek (xs as x::_) = (xs, SOME x)

fun pushback i sq = (i::sq, SOME ())


fun fail s = optmonad.fail

fun item c =
  (get +++ fail "") >- (fn x => if x = c then return c
                                else pushback x >> fail "")

fun itemP P =
  (get +++ fail "") >- (fn x => if P x then return x
                                else pushback x >> fail "")




fun eof [] = ([], SOME ())
  | eof x = (x, NONE)

fun wholething p = p >-> eof

val grab_whitespace = many (itemP Char.isSpace)

fun sepby sep p =
  (p >- (fn i =>
  (sep >> sepby sep p >- (fn rest => return (i::rest))) +++
  return [i])) +++ (return [])

fun parse p = p >-> grab_whitespace
fun token p = grab_whitespace >> p
val pure_ident =
  many1 (itemP Char.isAlpha) >- (return o implode)
val ident =
  itemP Char.isAlpha >-              (fn char1 =>
  many (itemP (fn c => Char.isAlphaNum c orelse c = #"_"))  >- (fn rest =>
  return (implode (char1::rest))))
fun member x [] = false
  | member x (y::ys) = x = y orelse member x ys
(* omit $ and ` because these are not available in HOL *)
fun SMLsym c = member c [#"!", #"?", #"#", #"%", #"^", #"&", #"*", #"=",
                         #"-", #"+", #"@", #"~", #"<", #">", #"/", #"\\",
                         #"|"]
val ident_op =
  many1 (itemP SMLsym) >- (return o implode)
val number =
  many1 (itemP Char.isDigit) >-
  (return o valOf o Int.fromString o implode)
fun substring s = if Substring.isEmpty s then return s
                  else let
                    val (x,xs) = valOf (Substring.getc s)
                  in
                    item x >> substring xs >> return s
                  end
fun string s = substring (Substring.all s) >> return s
fun symbol s = token (string s);

val T_ident = token ident
val T_ident_op = token ident_op

fun optll p sepp dflt =
  (sepp >-          (fn f =>
   p >-             (fn val2 =>
   optll p sepp (f dflt val2)))) ++ return dflt

fun chainl1 p sepp = p >- optll p sepp
fun chainl p sepp dflt = (chainl1 p sepp) ++ return dflt
fun chainr1 p sepp =
  p >-                 (fn first =>
  ((sepp >-            (fn f =>
    chainr1 p sepp >-  (fn rest =>
    return (f first rest)))) ++
   (return first)))
fun chainr p sepp deflt = (chainr1 p sepp) ++ return deflt

fun bracketted l p r = l >> p >-> r
fun file_to_cseq fname = let
  val i = TextIO.openIn fname
in
  explode (TextIO.inputAll i) before TextIO.closeIn i
end



val string_to_cseq = String.explode

fun apply_to_string f s = let
  val (remaining_string, result) = (wholething f o string_to_cseq) s
in
  case result of
    SOME x => x
  | NONE => raise NoParseResult (implode remaining_string)
end

fun apply_to_file f fname = let
  val (remaining_string, result) = wholething f (file_to_cseq fname)
in
  case result of
    SOME x => x
  | NONE => raise NoParseResult (implode remaining_string)
end

end
