(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF TERMS                                *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibTermnet =
sig

type 'a pp          = 'a mlibUseful.pp
type ('a,'b) maplet = ('a,'b) mlibUseful.maplet
type term           = mlibTerm.term

type 'a termnet

(* Basic operations *)
val empty        : unit -> 'a termnet
val size         : 'a termnet -> int
val insert       : (term,'a) maplet -> 'a termnet -> 'a termnet
val from_maplets : (term,'a) maplet list -> 'a termnet
val filter       : ('a -> bool) -> 'a termnet -> 'a termnet

(* mlibMatching and unifying *)
val match   : 'a termnet -> term -> 'a list
val matched : 'a termnet -> term -> 'a list
val unify   : 'a termnet -> term -> 'a list

(* Pretty-printing *)
val to_maplets : 'a termnet -> (term,'a) maplet list
val pp_termnet : 'a pp -> 'a termnet pp

end
