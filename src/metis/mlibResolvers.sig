(* ========================================================================= *)
(* A TYPE TO FIND RESOLVANT CLAUSES                                          *)
(* Created by Joe Hurd, April 2002                                           *)
(* ========================================================================= *)

signature mlibResolvers =
sig

type 'a pp   = 'a mlibUseful.pp
type formula = mlibTerm.formula
type subst   = mlibSubst.subst
type thm     = mlibThm.thm

type resolvers
type resolvant = {mate : thm, sub : subst, res : thm}

val empty_resolvers : resolvers
val add_resolver    : thm -> resolvers -> resolvers
val find_resolvants : resolvers -> thm -> resolvant list
val resolvers_info  : resolvers -> string
val pp_resolvers    : resolvers pp

end