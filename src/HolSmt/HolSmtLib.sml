(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT_TAC and derived tactics to
   call SMT solvers. *)

structure HolSmtLib :> HolSmtLib = struct

  open Abbrev

  fun GENERIC_SMT_TAC solver goal =
  let
    val ERR = Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT_TAC"
  in
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
  end

  val YICES_TAC = GENERIC_SMT_TAC Yices.Yices_Oracle
  val Z3_ORACLE_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Oracle
  val Z3_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Prover

  fun YICES_PROVE tm = Tactical.prove(tm, YICES_TAC)
  fun Z3_ORACLE_PROVE tm = Tactical.prove(tm, Z3_ORACLE_TAC)
  fun Z3_PROVE tm = Tactical.prove(tm, Z3_TAC)

end
