(* ========================================================================= *)
(* A HOL INTERFACE TO THE METIS FIRST-ORDER PROVER.                          *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature metisTools =
sig

type 'a stream = 'a mlibStream.stream
type limit     = mlibMeter.limit
type term      = Term.term
type thm       = Thm.thm
type tactic    = Abbrev.tactic
type Query     = folTools.Query
type Result    = folTools.Result

(* Parameters *)
type Fparm      = folTools.parameters
type Mparm      = mlibMetis.parameters
type parameters = {interface : Fparm, solver : Mparm, limit : limit}

val defaults              : parameters
val update_parm_interface : (Fparm -> Fparm) -> parameters -> parameters
val update_parm_solver    : (Mparm -> Mparm) -> parameters -> parameters
val update_parm_limit     : (limit -> limit) -> parameters -> parameters

(* Interface to the metis solver *)
val GEN_METIS_SOLVE :
  parameters -> {thms : thm list, hyps : thm list} -> Query -> Result stream

(* Tactic interface to the metis prover *)
val GEN_METIS_TAC : parameters -> thm list -> tactic

(* All the following use this limit *)
val limit : limit ref

(* Canned parameters for common situations *)
val METIS_TAC      : thm list -> tactic           (* First-order, typeless *)
val HO_METIS_TAC   : thm list -> tactic           (* Higher-order, typed *)
val FULL_METIS_TAC : thm list -> tactic           (* + combinator reductions *)

(* Simple user interface to the metis prover *)
val METIS_PROVE      : thm list -> term -> thm
val HO_METIS_PROVE   : thm list -> term -> thm
val FULL_METIS_PROVE : thm list -> term -> thm

end
