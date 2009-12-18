(* Author: Michael Norrish *)

structure Arbint :> Arbint =
struct

open Arbintcore

fun pp_int ppstrm bi = HOLPP.add_string ppstrm (toString bi);

end
