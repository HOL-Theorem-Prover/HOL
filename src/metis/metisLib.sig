(* ========================================================================= *)
(* THE METIS LIBRARY                                                         *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

signature metisLib =
sig

type 'a stream = 'a mlibStream.stream
type term      = Term.term
type thm       = Thm.thm
type tactic    = Abbrev.tactic
type Query     = folTools.Query
type Result    = folTools.Result

(* Prolog solver *)
val PROLOG_SOLVE : thm list -> Query -> Result stream

(* Tactic interface to the metis prover *)
val METIS_TAC      : thm list -> tactic           (* First-order, typeless *)
val HO_METIS_TAC   : thm list -> tactic           (* Higher-order, typed *)
val FULL_METIS_TAC : thm list -> tactic           (* + combinator reductions *)

(* Simple user interface to the metis prover *)
val METIS_PROVE      : thm list -> term -> thm
val HO_METIS_PROVE   : thm list -> term -> thm
val FULL_METIS_PROVE : thm list -> term -> thm

end
