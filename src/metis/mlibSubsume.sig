(* ========================================================================= *)
(* A TYPE FOR SUBSUMPTION CHECKING                                           *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

signature mlibSubsume =
sig

type 'a pp           = 'a mlibUseful.pp
type ('a, 'b) maplet = ('a, 'b) mlibUseful.maplet
type formula         = mlibTerm.formula
type subst           = mlibSubst.subst

type 'a subsume

val empty             : 'a subsume
val add               : (formula list, 'a) maplet -> 'a subsume -> 'a subsume
val subsumed          : 'a subsume -> formula list -> (subst * 'a) list
val strictly_subsumed : 'a subsume -> formula list -> (subst * 'a) list
val info              : 'a subsume -> string
val pp_subsum         : 'a subsume pp

end