(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF TERMS                                *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibTermnet =
sig

type 'a pp           = 'a mlibUseful.pp
type ('a, 'b) maplet = ('a, 'b) mlibUseful.maplet
type term            = mlibTerm.term

type 'a termnet

val empty        : 'a termnet
val insert       : (term, 'a) maplet -> 'a termnet -> 'a termnet
val match        : 'a termnet -> term -> 'a list
val matched      : 'a termnet -> term -> 'a list
val unify        : 'a termnet -> term -> 'a list
val size         : 'a termnet -> int
val from_maplets : (term, 'a) maplet list -> 'a termnet
val to_list      : 'a termnet -> 'a list
val pp_termnet   : 'a pp -> 'a termnet pp

end
