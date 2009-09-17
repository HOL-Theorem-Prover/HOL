(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT and related conversions. *)

structure HolSmtLib :> HolSmtLib = struct

  (* single entry point into HolSmtLib *)
  fun GENERIC_SMT solver tm =
    let
      val _ = if Term.type_of tm <> Type.bool then
          raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
            "term supplied is not of type bool")
        else ()
      val neg_tm = boolSyntax.mk_neg tm (* we could strip quantifiers *)
    in
      case solver neg_tm of
        SolverSpec.SAT NONE =>
          raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
            "solver reports negated term to be 'satisfiable'")
      | SolverSpec.SAT (SOME _) =>
          raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
            "solver reports negated term to be 'satisfiable' (model returned)")
      | SolverSpec.UNSAT NONE =>
          Thm.mk_oracle_thm "HolSmtLib" ([], tm)
      | SolverSpec.UNSAT (SOME thm) =>
          (* we expect 'thm' to be of the form '~tm |- F' *)
          Thm.CCONTR tm thm
      | SolverSpec.UNKNOWN NONE =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
          "solver reports 'unknown' (solver not installed/problem too hard?)")
      | SolverSpec.UNKNOWN (SOME message) =>
        raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
          ("solver reports 'unknown' (" ^ message ^ ")"))
    end

  fun YICES_ORACLE tm =
    GENERIC_SMT Yices.Yices_Oracle tm

  fun CVC3_ORACLE tm =
    GENERIC_SMT CVC3.CVC3_SMT_Oracle tm

  fun Z3_ORACLE tm =
    GENERIC_SMT Z3.Z3_SMT_Oracle tm

  fun Z3_PROVE tm =
    GENERIC_SMT Z3.Z3_SMT_Prover tm

end
