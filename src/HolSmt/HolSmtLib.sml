(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT_TAC and derived tactics to
   call SMT solvers. *)

structure HolSmtLib :> HolSmtLib = struct

  open Abbrev

  fun GENERIC_SMT_TAC solver goal =
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
    val (goals, proof) = Tactical.THENL (Tactical.REPEAT Tactic.GEN_TAC,
      [Tactical.THEN (Library.LET_SIMP_TAC,
         Tactical.THEN (Library.WORD_SIMP_TAC,
           Tactical.THEN (Library.SET_SIMP_TAC, Tactic.BETA_TAC)))]) goal
  in
    (* ugly hack to work around the fact that SET_SIMP_TAC and BETA_TAC prove
       ``T``; we call the SMT solver anyway to make sure this only works if the
       solver is installed (which is relied upon in selftest.sml) *)
    case goals of
      [] =>
      (ignore (SMT_TAC ([], boolSyntax.T));
      (goals, proof))
    | [g] =>
      Lib.apsnd (fn f => proof o Lib.single o f) (SMT_TAC g)
    | _ =>  (* cannot happen *)
      raise Match
  end

  val YICES_TAC = GENERIC_SMT_TAC Yices.Yices_Oracle
  val CVC3_TAC = GENERIC_SMT_TAC CVC3.CVC3_SMT_Oracle
  val Z3_ORACLE_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Oracle
  val Z3_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Prover

end
