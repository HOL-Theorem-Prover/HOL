(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT_TAC and derived tactics to
   call SMT solvers. *)

structure HolSmtLib :> HolSmtLib = struct

  open Abbrev

  fun GENERIC_SMT_TAC solver =
  let
    val ERR = Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT_TAC"
    fun SMT_TAC goal =
      case solver goal of
        SolverSpec.SAT NONE =>
        raise ERR "solver reports negated term to be 'satisfiable'"
      | SolverSpec.SAT (SOME _) =>
        raise ERR
          "solver reports negated term to be 'satisfiable' (model returned)"
      | SolverSpec.UNSAT NONE =>
        ([], fn _ => Thm.mk_oracle_thm "HolSmtLib" goal)
      | SolverSpec.UNSAT (SOME thm) =>
        (* 'thm' should be of the form "A' |- concl", where A' \subseteq A, and
           (A, concl) is the input goal (cf. SolverSpec.sml) *)
        ([], fn _ => thm)
      | SolverSpec.UNKNOWN NONE =>
        raise ERR
          "solver reports 'unknown' (solver not installed/problem too hard?)"
      | SolverSpec.UNKNOWN (SOME message) =>
        raise ERR ("solver reports 'unknown' (" ^ message ^ ")")
  in
    Tactical.THENL (Tactical.REPEAT Tactic.GEN_TAC, [SMT_TAC])
  end

  val YICES_TAC = GENERIC_SMT_TAC Yices.Yices_Oracle
  val CVC3_TAC = GENERIC_SMT_TAC CVC3.CVC3_SMT_Oracle
  val Z3_ORACLE_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Oracle
  val Z3_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Prover

end
