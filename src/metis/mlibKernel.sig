(* ========================================================================= *)
(* A LCF-STYLE LOGICAL KERNEL FOR FIRST-ORDER CLAUSES                        *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibKernel =
sig

type term    = mlibTerm.term
type formula = mlibTerm.formula
type subst   = mlibSubst.subst

(* An ABSTRACT type for theorems *)
eqtype thm
datatype inference = Axiom | Refl | Assume | Inst | Factor | Resolve | Equality

(* Destruction of theorems is fine *)
val dest_thm : thm -> formula list * (inference * thm list)

(* But creation is only allowed by the primitive rules of inference *)
val AXIOM    : formula list -> thm
val REFL     : term -> thm
val ASSUME   : formula -> thm
val INST     : subst -> thm -> thm
val FACTOR   : thm -> thm
val RESOLVE  : formula -> thm -> thm -> thm
val EQUALITY : formula -> int list -> term -> bool -> thm -> thm

end
