(* ========================================================================= *)
(* MATCHING AND UNIFICATION                                                  *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

signature mlibMatch =
sig

type term    = mlibTerm.term
type formula = mlibTerm.formula
type subst   = mlibSubst.subst

(* mlibMatching *)
val matchl          : subst -> (term * term) list -> subst
val match           : term -> term -> subst
val matchl_literals : subst -> (formula * formula) list -> subst
val match_literals  : formula -> formula -> subst

(* Unification *)
val unifyl          : subst -> (term * term) list -> subst
val unify           : subst -> term -> term -> subst
val unify_and_apply : term -> term -> term
val unifyl_literals : subst -> (formula * formula) list -> subst
val unify_literals  : subst -> formula -> formula -> subst

end
