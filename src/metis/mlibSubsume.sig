(* ========================================================================= *)
(* SUBSUMPTION CHECKING                                                      *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibSubsume =
sig

type 'a pp          = 'a mlibUseful.pp
type ('a,'b) maplet = ('a,'b) mlibUseful.maplet
type 'a stream      = 'a mlibStream.stream
type formula        = mlibTerm.formula
type subst          = mlibSubst.subst

type 'a subsume

(* Basic operations *)
val empty  : unit -> 'a subsume
val size   : 'a subsume -> int
val add    : (formula list,'a) maplet -> 'a subsume -> 'a subsume
val filter : ('a -> bool) -> 'a subsume -> 'a subsume

(* All subsuming clauses *)
val subsumes : 'a subsume -> formula list -> (subst * 'a) stream

(* Subsuming clauses that don't contain more literals than the query *)
val subsumes' : 'a subsume -> formula list -> (subst * 'a) stream

(* Single clause versions *)
val subsumes1  : formula list -> formula list -> subst list
val subsumes1' : formula list -> formula list -> subst list

(* Pretty-printing *)
val pp_subsume : 'a subsume pp

end
