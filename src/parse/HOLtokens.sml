fun member x [] = false
  | member x (y::ys) = x = y orelse member x ys

type charclass = char -> bool

infix ANDNOT OR
fun (P ANDNOT Q) x = P x andalso not (Q x)
fun (P OR Q) x = P x orelse Q x
fun ITEMS s x = member x (explode s)
fun ITEM c x = x = c

val empty = fn c => false

(* we put _ into both sets *)
val HOLsym = Char.isPunct ANDNOT ITEMS "$'"
val HOLid = Char.isAlphaNum OR ITEMS "_'"
