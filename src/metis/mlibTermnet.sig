(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF TERMS                                *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibTermnet =
sig

type 'a pp          = 'a mlibUseful.pp
type ('a,'b) maplet = ('a,'b) mlibUseful.maplet
type term           = mlibTerm.term

type parameters = {fifo : bool}

type 'a termnet

(* Basic operations *)
val empty        : parameters -> 'a termnet
val size         : 'a termnet -> int
val insert       : (term,'a) maplet -> 'a termnet -> 'a termnet
val from_maplets : parameters -> (term,'a) maplet list -> 'a termnet
val filter       : ('a -> bool) -> 'a termnet -> 'a termnet

(* mlibMatching and unifying *)
val match   : 'a termnet -> term -> 'a list
val matched : 'a termnet -> term -> 'a list
val unify   : 'a termnet -> term -> 'a list

(* Pretty-printing *)
val to_maplets : 'a termnet -> (term,'a) maplet list
val pp_termnet : 'a pp -> 'a termnet pp

end
