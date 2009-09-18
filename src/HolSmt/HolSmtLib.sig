(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

signature HolSmtLib = sig

  val GENERIC_SMT : (Term.term -> SolverSpec.result) -> Term.term -> Thm.thm

  val YICES_ORACLE : Term.term -> Thm.thm
  val CVC3_ORACLE : Term.term -> Thm.thm
  val Z3_ORACLE : Term.term -> Thm.thm
  val Z3_PROVE : Term.term -> Thm.thm

  val YICES_TAC : Abbrev.tactic
  val CVC3_TAC : Abbrev.tactic
  val Z3_ORACLE_TAC : Abbrev.tactic
  val Z3_TAC : Abbrev.tactic

end
