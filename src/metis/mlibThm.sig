(* ========================================================================= *)
(* INTERFACE TO THE LCF-STYLE LOGICAL KERNEL, PLUS SOME DERIVED RULES        *)
(* Copyright (c) 2001-2004 Joe Hurd.                                         *)
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

val dest_axiom : thm -> formula list
val is_axiom   : thm -> bool

(* Theorem operations *)
val thm_compare : thm * thm -> order
val thm_map     : (thm * 'a list -> 'a) -> thm -> 'a
val thm_foldr   : (thm * 'a -> 'a) -> 'a -> thm -> 'a

(* Contradictions and units *)
val is_contradiction : thm -> bool
val dest_unit        : thm -> formula
val is_unit          : thm -> bool
val dest_unit_eq     : thm -> term * term
val is_unit_eq       : thm -> bool

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
val SYM            : formula -> thm -> thm
val EQ_FACTOR      : thm -> thm
val REWR           : thm * bool -> thm * formula * int list -> thm
val DEPTH1         : (term->thm*term*bool) -> thm * formula -> thm * formula
val DEPTH          : (term->thm*term*bool) -> thm -> thm

(* Converting to clauses *)
val axiomatize : formula -> thm list
val eq_axioms  : formula -> thm list
val clauses    : formula -> {thms : thm list, hyps : thm list}

(* Pretty-printing of theorems and inferences *)
val pp_thm               : thm pp
val pp_inference         : inference pp
val pp_inference'        : inference' pp
val pp_proof             : (thm * inference') list pp
val thm_to_string'       : int -> thm -> string        (* purely functional *)
val inference_to_string' : int -> inference' -> string
val proof_to_string'     : int -> (thm * inference') list -> string
val thm_to_string        : thm -> string               (* uses !LINE_LENGTH *)
val inference_to_string  : inference' -> string
val proof_to_string      : (thm * inference') list -> string

end
