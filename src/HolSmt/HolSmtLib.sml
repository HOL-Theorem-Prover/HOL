(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT and functions to call
   individual SMT solvers. *)

structure HolSmtLib :> HolSmtLib = struct

  (* single entry point into HolSmtLib *)
  fun GENERIC_SMT solver goal =
    case solver goal of
      SolverSpec.SAT NONE =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
          "solver reports negated term to be 'satisfiable'")
    | SolverSpec.SAT (SOME _) =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
          "solver reports negated term to be 'satisfiable' (model returned)")
    | SolverSpec.UNSAT NONE =>
        Thm.mk_oracle_thm "HolSmtLib" goal
    | SolverSpec.UNSAT (SOME thm) =>
        (* 'thm' should be of the form "A |- concl", where A \subseteq B and
           (B, concl) is the input goal (cf. SolverSpec.sml) *)
        thm
    | SolverSpec.UNKNOWN NONE =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
          "solver reports 'unknown' (solver not installed/problem too hard?)")
    | SolverSpec.UNKNOWN (SOME message) =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
          ("solver reports 'unknown' (" ^ message ^ ")"))

  val YICES_ORACLE = GENERIC_SMT Yices.Yices_Oracle
  val CVC3_ORACLE = GENERIC_SMT CVC3.CVC3_SMT_Oracle
  val Z3_ORACLE = GENERIC_SMT Z3.Z3_SMT_Oracle
  val Z3_PROVE = GENERIC_SMT Z3.Z3_SMT_Prover

  fun tactic (generic_smt : Abbrev.goal -> Thm.thm) : Abbrev.tactic =
    fn goal =>
      let
        val thm = generic_smt goal
      in
        ([], fn _ => thm)
      end

  val YICES_TAC = tactic YICES_ORACLE
  val CVC3_TAC = tactic CVC3_ORACLE
  val Z3_ORACLE_TAC = tactic Z3_ORACLE
  val Z3_TAC = tactic Z3_PROVE

end
