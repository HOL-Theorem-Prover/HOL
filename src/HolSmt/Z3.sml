(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Functions to invoke the Z3 SMT solver *)

structure Z3 = struct

  (* returns SAT if Z3 reported "sat", UNSAT if Z3 reported "unsat" *)
  fun is_sat_stream instream =
    case TextIO.inputLine instream of
      NONE => SolverSpec.UNKNOWN NONE
    | SOME "sat\n" => SolverSpec.SAT NONE
    | SOME "unsat\n" => SolverSpec.UNSAT NONE
    | _ => is_sat_stream instream

  fun is_sat_file path =
    let
      val instream = TextIO.openIn path
    in
      is_sat_stream instream
        before TextIO.closeIn instream
    end

  (* Z3 (Linux/Unix), SMT-LIB file format, no proofs *)
  val Z3_SMT_Oracle = SolverSpec.make_solver
    (Lib.apfst (Lib.K ()) o SmtLib.goal_to_SmtLib)
    "z3 -smt2"
    (Lib.K is_sat_file)

  (* Z3 (Linux/Unix), SMT-LIB file format, with proofs *)
  val Z3_SMT_Prover = SolverSpec.make_solver
    (Lib.S (Lib.apfst o Lib.pair) SmtLib.goal_to_SmtLib_with_get_proof)
    "z3 PROOF_MODE=2 -smt2"
    (fn (goal, (ty_dict, tm_dict)) =>
      fn outfile =>
        let
          val instream = TextIO.openIn outfile
          val result = is_sat_stream instream
        in
          case result of
            SolverSpec.UNSAT NONE =>
            let
              (* invert 'ty_dict' and 'tm_dict', create parsing functions *)
              val ty_dict = Redblackmap.foldl (fn (ty, s, dict) =>
                (* types don't take arguments *)
                Redblackmap.insert (dict, s, [SmtLib_Theories.K_zero_zero ty]))
                (Redblackmap.mkDict String.compare) ty_dict
              val tm_dict = Redblackmap.foldl (fn (tm, s, dict) =>
                Redblackmap.insert (dict, s, [Lib.K (SmtLib_Theories.zero_args
                  (Lib.curry Term.list_mk_comb tm))]))
                (Redblackmap.mkDict String.compare) tm_dict
              (* add relevant SMT-LIB types/terms to dictionaries *)
              val ty_dict = Library.union_dict (Library.union_dict
                SmtLib_Logics.AUFNIRA.tydict SmtLib_Logics.QF_ABV.tydict)
                ty_dict
              val tm_dict = Library.union_dict (Library.union_dict
                SmtLib_Logics.AUFNIRA.tmdict SmtLib_Logics.QF_ABV.tmdict)
                tm_dict
              (* parse the proof and check it in HOL *)
              val proof = Z3_ProofParser.parse_stream (ty_dict, tm_dict)
                instream
              val _ = TextIO.closeIn instream
              val thm = Z3_ProofReplay.check_proof proof

(* TODO
              (* specialize the theorem derived by Z3 to the types and terms
                 that were used in the input goal *)
              val ty_subst =
                Redblackmap.foldl (fn (ty, s, subst) =>
                  {redex = Type.mk_vartype ("'" ^ s), residue = ty} :: subst)
                  [] ty_dict
              val tm_subst =
                Redblackmap.foldl (fn (tm, s, subst) =>
                  {redex = Term.mk_var (s, Term.type_of tm), residue = tm} ::
                    subst)
                  [] tm_dict
              val thm = Drule.INST_TY_TERM (tm_subst, ty_subst) thm
*)

              (* discharging definitions: INT_MIN, INT_MAX, ABS *)
              val INT_ABS = intLib.ARITH_PROVE
                ``!x. ABS (x:int) = if x < 0i then 0i - x else x``
              (* bool_case is replaced by if_then_else by the translation to
                 SMT-LIB format; this must therefore be done in the goal as
                 well *)
              (* returns SOME "tm[bool_case ...] |- tm[if_then_else ...]", or
                 NONE *)
              fun unfold_bool_case tm =
                Lib.total (Drule.UNDISCH o Lib.fst o Thm.EQ_IMP_RULE o
                  Conv.BETA_RULE o simpLib.SIMP_CONV simpLib.empty_ss
                    [boolTheory.bool_case_DEF]) tm
              val (As, g) = goal
              val unfold_thms = List.mapPartial unfold_bool_case
                (boolSyntax.mk_neg g :: As)
              fun prove_hyp (hyp, th) =
                if HOLset.member (Thm.hypset th, Thm.concl hyp) then
                  Drule.PROVE_HYP hyp th
                else
                  th
              val thm = List.foldl prove_hyp thm (integerTheory.INT_MIN ::
                integerTheory.INT_MAX :: INT_ABS :: unfold_thms)
              val thm = Thm.CCONTR g thm
            in
              SolverSpec.UNSAT (SOME thm)
            end
          | _ => (result before TextIO.closeIn instream)
        end)

end
