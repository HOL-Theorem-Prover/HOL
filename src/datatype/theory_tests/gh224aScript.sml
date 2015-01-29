open HolKernel Parse boolLib Datatype

val _ = new_theory "gh224a";

(* val _ = Datatype `bar = <| size : num |>` *)

val _ = Datatype `A_x = <| y : num |>`
val _ = Datatype `A = <| x : A_x |>`


val _ = export_theory();
