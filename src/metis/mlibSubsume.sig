(* ========================================================================= *)
(* SUBSUMPTION CHECKING                                                      *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

signature mlibSubsume =
sig

type 'a pp           = 'a mlibUseful.pp
type ('a, 'b) maplet = ('a, 'b) mlibUseful.maplet
type formula         = mlibTerm.formula
type subst           = mlibSubst.subst

type 'a subsume

val empty      : 'a subsume
val add        : (formula list, 'a) maplet -> 'a subsume -> 'a subsume
val pp_subsume : 'a subsume pp

(* All subsuming clauses *)
val subsumes : 'a subsume -> formula list -> (subst * 'a) list

(* Subsuming clauses that don't contain more literals than the query *)
val subsumes' : 'a subsume -> formula list -> (subst * 'a) list

(* Single clause versions *)
val subsumes1  : formula list -> formula list -> subst list
val subsumes1' : formula list -> formula list -> subst list

end
