(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF LITERALS                             *)
(* Created by Joe Hurd, June 2002                                            *)
(* ========================================================================= *)

signature mlibLiteralNet =
sig

type 'a pp           = 'a mlibUseful.pp
type formula         = mlibTerm.formula
type ('a, 'b) maplet = ('a, 'b) mlibTerm.maplet

type 'a literal_map

val empty          : 'a literal_map
val insert         : (formula, 'a) maplet -> 'a literal_map -> 'a literal_map
val match          : 'a literal_map -> formula -> 'a list
val matched        : 'a literal_map -> formula -> 'a list
val unify          : 'a literal_map -> formula -> 'a list
val size           : 'a literal_map -> int
val size_profile   : 'a literal_map -> {t : int, f : int, p : int, n : int}
val from_maplets   : (formula, 'a) maplet list -> 'a literal_map
val to_list        : 'a literal_map -> 'a list
val pp_literal_map : 'a pp -> 'a literal_map pp

end