(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF LITERALS                             *)
(* Created by Joe Hurd, June 2002                                            *)
(* ========================================================================= *)

signature mlibLiteralnet =
sig

type 'a pp           = 'a mlibUseful.pp
type formula         = mlibTerm.formula
type ('a, 'b) maplet = ('a, 'b) mlibTerm.maplet

type 'a literalnet

val empty         : 'a literalnet
val insert        : (formula, 'a) maplet -> 'a literalnet -> 'a literalnet
val match         : 'a literalnet -> formula -> 'a list
val matched       : 'a literalnet -> formula -> 'a list
val unify         : 'a literalnet -> formula -> 'a list
val size          : 'a literalnet -> int
val size_profile  : 'a literalnet -> {t : int, f : int, p : int, n : int}
val from_maplets  : (formula, 'a) maplet list -> 'a literalnet
val to_list       : 'a literalnet -> 'a list
val pp_literalnet : 'a pp -> 'a literalnet pp

end