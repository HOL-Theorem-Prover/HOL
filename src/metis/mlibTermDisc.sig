(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF TERMS                                *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibTermDisc =
sig

type 'a pp           = 'a mlibUseful.pp
type ('a, 'b) maplet = ('a, 'b) mlibUseful.maplet
type term            = mlibTerm.term

type 'a term_map

val empty        : 'a term_map
val insert       : (term, 'a) maplet -> 'a term_map -> 'a term_map
val match        : 'a term_map -> term -> 'a list
val matched      : 'a term_map -> term -> 'a list
val unify        : 'a term_map -> term -> 'a list
val size         : 'a term_map -> int
val from_maplets : (term, 'a) maplet list -> 'a term_map
val to_list      : 'a term_map -> 'a list
val pp_term_map  : 'a pp -> 'a term_map pp

end
