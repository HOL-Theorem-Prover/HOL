(* ========================================================================= *)
(* MAPPING BETWEEN HOL AND FIRST-ORDER LOGIC.                                *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature folMapping =
sig

type 'a pp    = 'a mlibUseful.pp
type term1    = mlibTerm.term
type formula1 = mlibTerm.formula
type thm1     = mlibThm.thm
type hol_type = Type.hol_type
type term     = Term.term
type thm      = Thm.thm
type vars     = term list * hol_type list

(* Mapping parameters *)
type parameters =
  {higher_order : bool,       (* Application is a first-order function *)
   with_types   : bool};      (* First-order terms include HOL type info *)

val defaults            : parameters
val update_higher_order : (bool -> bool) -> parameters -> parameters
val update_with_types   : (bool -> bool) -> parameters -> parameters

(* Mapping HOL literals to FOL (need to pass in variables) *)
val hol_literals_to_fol : parameters -> vars * term list -> formula1 list
  
(* Mapping HOL theorems to FOL axioms *)
val hol_thm_to_fol : parameters -> vars * thm -> thm1

(* Mapping FOL theorems to HOL *)
type Axioms  = thm1 -> vars * thm
type Pattern = vars * term list
type Result  = vars * thm list
val fol_thms_to_hol : parameters -> Axioms -> Pattern -> thm1 list -> Result

(* Prettify FOL representations of HOL terms---WILL BREAK PROOF TRANSLATION! *)
val prettify_fol     : bool ref
val prettify_formula : formula1 -> formula1

end
