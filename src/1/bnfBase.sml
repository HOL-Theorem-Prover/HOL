structure bnfBase :> bnfBase =
struct

open bnfBase_dtype parse_bnf

type t = thm info TypeNet.typenet

fun pure_lookup db ty = TypeNet.peek (db,ty)

end
