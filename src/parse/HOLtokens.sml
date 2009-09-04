structure HOLtokens :> HOLtokens =
struct

type charclass = char -> bool

infix ANDNOT OR
fun (P ANDNOT Q) x = P x andalso not (Q x)
fun (P OR Q) x = P x orelse Q x
fun ITEMS s = let val clist = String.explode s in (fn x => Lib.mem x clist) end
fun ITEM c x = x = c

val empty = fn c => false

fun fromLex a c = Lexis.in_class(a, ord c)

val HOLsym = fromLex Lexis.hol_symbols

val HOLspecials = ITEMS "(){}[]."

end;
