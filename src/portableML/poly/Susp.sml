(* Susp -- support for lazy evaluation 1995-05-22 *)
structure Susp :> Susp =
struct

datatype 'a thunk = VAL of 'a | THUNK of unit -> 'a
type 'a susp = 'a thunk ref

fun delay (f : unit -> 'a) = ref (THUNK f) : 'a susp

fun force (su : 'a susp) : 'a =
    case !su of
      VAL v   => v
    | THUNK f => let val v = f () in su := VAL v; v end


end (* struct *)

