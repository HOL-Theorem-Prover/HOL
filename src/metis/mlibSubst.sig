(* ========================================================================= *)
(* SUBSTITUTIONS ON FIRST-ORDER TERMS AND FORMULAS                           *)
(* Copyright (c) 2002-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibSubst =
sig

type 'a pp           = 'a mlibUseful.pp
type ('a, 'b) maplet = ('a, 'b) mlibUseful.maplet
type term            = mlibTerm.term
type formula         = mlibTerm.formula

type subst

val |<>|          : subst
val ::>           : (string, term) maplet * subst -> subst
val @>            : subst * subst -> subst
val null          : subst -> bool
val term_subst    : subst -> term -> term
val formula_subst : subst -> formula -> formula
val find_redex    : string -> subst -> term option
val norm          : subst -> subst       (* Removes identity substitutions *)
val restrict      : string list -> subst -> subst
val refine        : subst -> subst -> subst
val is_renaming   : subst -> bool
val to_maplets    : subst -> (string, term) maplet list
val from_maplets  : (string, term) maplet list -> subst
val foldl         : ((string, term) maplet -> 'a -> 'a) -> 'a -> subst -> 'a
val foldr         : ((string, term) maplet -> 'a -> 'a) -> 'a -> subst -> 'a
val pp_subst      : subst pp

end

