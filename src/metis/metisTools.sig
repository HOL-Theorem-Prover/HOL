(* ========================================================================= *)
(* A HOL INTERFACE TO THE METIS FIRST-ORDER PROVER.                          *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature metisTools =
sig

(* "Metis" trace levels:
   0: No output
   1: The equivalent of Meson dots
   2: Timing information
   3: More detailed prover information: slice by slice
   4: Log of each step in proof translation
   5: Log of each inference during proof search *)

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

val defaults         : parameters
val update_interface : (Fparm -> Fparm) -> parameters -> parameters
val update_solver    : (Mparm -> Mparm) -> parameters -> parameters
val update_limit     : (limit -> limit) -> parameters -> parameters

(* Prolog solver *)
val PROLOG_SOLVE : thm list -> Query -> Result stream

(* Metis solver *)
val GEN_METIS_SOLVE : parameters -> thm list -> Query -> Result stream

(* Tactic interface to the metis prover *)
val GEN_METIS_TAC : parameters -> thm list -> tactic

(* All the following use this limit *)
val limit : limit ref

(* Canned parameters for common situations *)
val FO_METIS_TAC   : thm list -> tactic         (* First-order *)
val FOT_METIS_TAC  : thm list -> tactic         (* + types *)
val HO_METIS_TAC   : thm list -> tactic         (* Higher-order *)
val HOT_METIS_TAC  : thm list -> tactic         (* + types *)
val FULL_METIS_TAC : thm list -> tactic         (* + combinators & booleans *)

(* Simple user interface to the metis prover *)
val FO_METIS_PROVE   : thm list -> term -> thm  (* First-order *)
val FOT_METIS_PROVE  : thm list -> term -> thm  (* + types *)
val HO_METIS_PROVE   : thm list -> term -> thm  (* Higher-order *)
val HOT_METIS_PROVE  : thm list -> term -> thm  (* + types *)
val FULL_METIS_PROVE : thm list -> term -> thm  (* + combinators & booleans *)

(* Uses heuristics to apply one of {FO|FOT}, {HO|HOT} or FULL. *)
val METIS_TAC   : thm list -> tactic
val METIS_PROVE : thm list -> term -> thm

end
