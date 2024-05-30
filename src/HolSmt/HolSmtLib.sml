(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT_TAC and derived tactics to
   call SMT solvers. *)

structure HolSmtLib :> HolSmtLib = struct

  open Abbrev

  val op THEN = Tactical.THEN

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

  val CVC_ORACLE_TAC = GENERIC_SMT_TAC CVC.CVC_SMT_Oracle
  val YICES_TAC = GENERIC_SMT_TAC Yices.Yices_Oracle
  val Z3_ORACLE_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Oracle
  val Z3_TAC = GENERIC_SMT_TAC Z3.Z3_SMT_Prover

  fun assume_thms thms = Tactical.map_every (Tactic.ASSUME_TAC o Drule.GEN_ALL) thms

  (* The tactics below accept a list of theorems, like metis_tac[] *)
  fun z3_tac thms = assume_thms thms THEN Z3_TAC
  fun z3o_tac thms = assume_thms thms THEN Z3_ORACLE_TAC

  fun prove (tm, tac) = Tactical.TAC_PROOF(([], tm), tac)
  fun CVC_ORACLE_PROVE tm = prove (tm, CVC_ORACLE_TAC)
  fun YICES_PROVE tm = prove (tm, YICES_TAC)
  fun Z3_ORACLE_PROVE tm = prove (tm, Z3_ORACLE_TAC)
  fun Z3_PROVE tm = prove (tm, Z3_TAC)

  val include_theorems = SmtLib.include_theorems

  (* report whether solvers are available *)
  val _ =
    let
      fun check_available prove_fn name =
        (
          prove_fn boolSyntax.T;  (* try to prove ``T`` *)
          Feedback.HOL_MESG ("HolSmtLib: solver " ^ name ^ " is available.")
        )
      fun provoke_err prove_fn =
        ignore (prove_fn boolSyntax.T)  (* should fail *)
          handle Feedback.HOL_ERR {message, ...} =>
            Feedback.HOL_MESG ("HolSmtLib: " ^ message)
    in
      Feedback.set_trace "HolSmtLib" 0;
      if CVC.is_configured () then
        check_available CVC_ORACLE_PROVE "cvc5 (oracle)"
      else
        provoke_err CVC_ORACLE_PROVE;
      if Yices.is_configured () then
        check_available YICES_PROVE "Yices"
      else
        provoke_err YICES_PROVE;
      if Z3.is_configured () then (
        check_available Z3_ORACLE_PROVE "Z3 (oracle)";
        check_available Z3_PROVE "Z3 (with proofs)"
      ) else
        provoke_err Z3_ORACLE_PROVE;
      Feedback.reset_trace "HolSmtLib"
    end

end
