(* ========================================================================= *)
(* INTERFACE TO THE LCF-STYLE LOGICAL KERNEL, PLUS SOME DERIVED RULES        *)
(* Created by Joe Hurd, September 2001                                       *)
(* ========================================================================= *)

signature mlibThm =
sig

type 'a pp = 'a mlibUseful.pp

include mlibKernel

(* Annotated primitive inferences *)
datatype inference' =
  Axiom'    of formula list
| Refl'     of term
| Assume'   of formula
| Inst'     of subst * thm
| Factor'   of thm
| Resolve'  of formula * thm * thm
| Equality' of formula * int list * term * bool * thm

val primitive_inference : inference' -> thm

(* User-friendly destructors *)
val clause    : thm -> formula list
val inference : thm -> inference'
val proof     : thm -> (thm * inference') list

(* Pretty-printing of theorems and inferences *)
val pp_thm               : thm pp
val pp_inference         : inference pp
val pp_inference'        : inference' pp
val thm_to_string'       : int -> thm -> string        (* purely functional *)
val inference_to_string' : int -> inference' -> string
val thm_to_string        : thm -> string               (* using !LINE_LENGTH *)
val inference_to_string  : inference' -> string

(* Contradictions and unit clauses *)
val is_contradiction : thm -> bool
val dest_unit        : thm -> formula
val is_unit          : thm -> bool

(* Derived rules and theorems *)
val CONTR          : formula -> thm -> thm
val WEAKEN         : formula list -> thm -> thm
val FRESH_VARS     : thm -> thm
val FRESH_VARSL    : thm list -> thm list
val UNIT_SQUASH    : thm -> thm
val REFLEXIVITY    : thm
val SYMMETRY       : thm
val TRANSITIVITY   : thm
val FUN_CONGRUENCE : string * int -> thm
val REL_CONGRUENCE : string * int -> thm

end
