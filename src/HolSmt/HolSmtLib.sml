(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT_TAC and derived tactics to
   call SMT solvers. *)

structure HolSmtLib :> HolSmtLib = struct

  open Abbrev

  fun GENERIC_SMT_TAC solver goal =
    case solver goal of
      SolverSpec.SAT NONE =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT_TAC"
          "solver reports negated term to be 'satisfiable'")
    | SolverSpec.SAT (SOME _) =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT_TAC"
          "solver reports negated term to be 'satisfiable' (model returned)")
    | SolverSpec.UNSAT NONE =>
        let
          val thm = Thm.mk_oracle_thm "HolSmtLib" goal
        in
          ([], fn _ => thm)
        end
    | SolverSpec.UNSAT (SOME thm) =>
        (* 'thm' should be of the form "A' |- concl", where A' \subseteq A and
           (A, concl) is the input goal (cf. SolverSpec.sml) *)
        ([], fn _ => thm)
    | SolverSpec.UNKNOWN NONE =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT_TAC"
          "solver reports 'unknown' (solver not installed/problem too hard?)")
    | SolverSpec.UNKNOWN (SOME message) =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT_TAC"
          ("solver reports 'unknown' (" ^ message ^ ")"))

  val YICES_TAC = GENERIC_SMT_TAC Yices.Yices_Oracle
  val CVC3_TAC = GENERIC_SMT_TAC CVC3.CVC3_SMT_Oracle
  val Z3_ORACLE_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Oracle
  val Z3_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Prover

end
