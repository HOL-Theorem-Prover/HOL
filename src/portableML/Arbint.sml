(* Author: Michael Norrish *)

structure Arbint :> Arbint =
struct

open Arbintcore

fun pp_int bi = HOLPP.add_string (toString bi)

end
