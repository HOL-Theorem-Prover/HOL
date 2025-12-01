structure bnfBase :> bnfBase =
struct

open bnfBase_dtype

type t = info TypeNet.typenet

fun pure_lookup db ty = TypeNet.peek (db,ty)


end
