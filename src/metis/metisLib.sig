(* ========================================================================= *)
(* THE METIS LIBRARY                                                         *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

signature metisLib =
sig

(* Top-level entry-point to the metis prover *)
val METIS_TAC   : Thm.thm list -> Tactic.tactic
val METIS_PROVE : Thm.thm list -> Term.term -> Thm.thm

end
