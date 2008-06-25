signature Susp =
sig
(* Susp -- support for lazy evaluation *)

type 'a susp

val delay : (unit -> 'a) -> 'a susp
val force : 'a susp -> 'a

(*
   ['a susp] is the type of lazily evaluated expressions with result
   type 'a.

   [delay (fn () => e)] creates a suspension for the expression e.
   The first time the suspension is forced, the expression e will be
   evaluated, and the result stored in the suspension.  All subsequent
   forcing of the suspension will just return this result, so e is
   evaluated at most once.  If the suspension is never forced, then e
   is never evaluated.

   [force su] forces the suspension su and returns the result of the
   expression e stored in the suspension.
*)
end