(* ========================================================================= *)
(* A TYPE FOR SUBSUMPTION CHECKING                                           *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

signature mlibSubsum =
sig

type 'a pp           = 'a mlibUseful.pp
type ('a, 'b) maplet = ('a, 'b) mlibUseful.maplet
type formula         = mlibTerm.formula
type subst           = mlibSubst.subst

type 'a subsum

val empty             : 'a subsum
val add               : (formula list, 'a) maplet -> 'a subsum -> 'a subsum
val subsumed          : 'a subsum -> formula list -> (subst * 'a) list
val strictly_subsumed : 'a subsum -> formula list -> (subst * 'a) list
val info              : 'a subsum -> string
val pp_subsum         : 'a subsum pp

end