(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

signature HolSmtLib = sig

  include Abbrev

  val GENERIC_SMT_TAC : (goal -> SolverSpec.result) -> tactic

  val YICES_TAC : tactic
  val Z3_ORACLE_TAC : tactic
  val Z3_TAC : tactic

  val YICES_PROVE : term -> thm
  val Z3_ORACLE_PROVE : term -> thm
  val Z3_PROVE : term -> thm

end
