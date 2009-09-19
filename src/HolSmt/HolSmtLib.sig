(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

signature HolSmtLib = sig

  val GENERIC_SMT : (Abbrev.goal -> SolverSpec.result) -> Abbrev.goal -> Thm.thm

  val YICES_ORACLE : Abbrev.goal -> Thm.thm
  val CVC3_ORACLE : Abbrev.goal -> Thm.thm
  val Z3_ORACLE : Abbrev.goal -> Thm.thm
  val Z3_PROVE : Abbrev.goal -> Thm.thm

  val YICES_TAC : Abbrev.tactic
  val CVC3_TAC : Abbrev.tactic
  val Z3_ORACLE_TAC : Abbrev.tactic
  val Z3_TAC : Abbrev.tactic

end
