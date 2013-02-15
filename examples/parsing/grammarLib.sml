structure grammarLib :> grammarLib =
struct

open Abbrev
open errormonad

infix >-* >>-* <-
fun (m >-* cf) = m >- (fn v1 => cf v1 >- (fn v2 => return (v1,v2)))
fun (m1 >>-* m2) = m1 >-* (fn _ => m2)
fun (m1 <- m2) = m1 >- (fn v => m2 >> return v)

type 'a tt = (term frag list, 'a, string) t

datatype stringt = S of string | TM of term
datatype sym = NT of string | TOK of stringt
type t = (string * sym list list) list

fun aq0 error frags =
    case frags of
      [] => (frags, Error error)
    | QUOTE s :: rest => if s = "" then aq0 error rest
                         else (frags, Error error)
    | ANTIQUOTE t :: rest => (rest, Some t)

fun getc error frags =
  case frags of
    [] => (frags, Error error)
  | QUOTE s :: rest =>
    if s = "" then getc error rest
    else let val i' = if size s = 1 then rest
                      else QUOTE (String.extract(s,1,NONE)) :: rest
         in
           (i', Some (String.sub(s,0)))
         end
  | ANTIQUOTE _ :: _ => (frags, Error error)

fun dropP P = repeat (getc "" >- (fn c => if P c then ok
                                          else fail ""))

fun getP P =
  getc "getP: EOF" >-
  (fn c => if P c then return c else fail "getP: P false")

fun token0 s = let
  val sz = size s
  fun recurse i =
      if i = sz then ok
      else let
        val c = String.sub(s,i)
      in
        getc "" >-
        (fn c' => if c' = c then recurse (i + 1)
                  else fail ("token: didn't find "^str c^" of "^s))
      end
in
  recurse 0
end

fun mnot m s = let
  val (s',res) = m s
in
  case res of
    Some _ => fail "mnot" s
  | Error _ => ok s
end

fun comment s =
    (token0 "(*" >> repeat (mnot (token0 "*)") >> getc "") >>
     token0 "*)") s

fun lex m = repeat ((getP Char.isSpace >> ok) ++ comment) >> m
fun complete m = m <- repeat ((getP Char.isSpace >> ok) ++ comment)
fun token s = lex (token0 s)
fun aq s = lex (aq0 s)

fun mrpt m = let
  fun recurse acc = (m >- (fn v => recurse (v::acc))) ++
                    return (List.rev acc)
in
  recurse []
end

fun ident0 s =
  (getP Char.isAlpha >-
   (fn c => mrpt (getP Char.isAlphaNum) >-
   (fn cs => return (String.implode (c::cs))))) s

fun ident s = lex ident0 s

fun escape #"n" = #"\n"
  | escape #"t" = #"\t"
  | escape c = c

fun slitchar s =
  ((getP (equal #"\\") >> getc "" >- (return o escape)) ++
   (getP (not o equal #"\""))) s

val slitcontent : string tt =
  mrpt slitchar >- (return o String.implode)

val slit0 : string tt =
  getP (equal #"\"") >>
  slitcontent >-
  (fn s => (getP (equal #"\"") >> return s) ++
           fail "Unterminated string literal")

val slit = lex slit0

fun sepby m sep =
    (m >>-* mrpt (sep >> m)) >- (return o op::)

val clause =
    mrpt ((ident >- (return o NT)) ++
          (slit >- (return o TOK o S)) ++
          ((token "<" >> aq "" <- token ">") >- (return o TOK o TM))
         )

val rulebody =
    sepby clause (token "|") <- token ";"

val grule = ident >>-* (token "::=" >> rulebody)
val grammar0 =
    complete (mrpt grule) <-
     (mnot (getc "") ++
      fail "Couldn't make sense of remaining input")

fun grammar fs =
    case grammar0 fs of
        (_, Error s) => raise Fail s
      | (_, Some v) => v

end
