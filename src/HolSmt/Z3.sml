(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Functions to invoke the Z3 SMT solver *)

structure Z3 = struct

  (* returns SAT if Z3 reported "sat", UNSAT if Z3 reported "unsat" *)
  fun is_sat_stream instream =
    case Option.map (String.tokens Char.isSpace) (TextIO.inputLine instream) of
      NONE => SolverSpec.UNKNOWN NONE
    | SOME ["sat"] => SolverSpec.SAT NONE
    | SOME ["unsat"] => SolverSpec.UNSAT NONE
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
    (fn goal =>
      let
        val (goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC false) goal
        val (_, strings) = SmtLib.goal_to_SmtLib goal
      in
        ((), strings)
      end)
    "z3 -smt2 -file:"
    (Lib.K is_sat_file)

  (* Z3 (Linux/Unix), SMT-LIB file format, with proofs *)
  val Z3_SMT_Prover = SolverSpec.make_solver
    (fn goal =>
      let
        val (goal, validation) = SolverSpec.simplify (SmtLib.SIMP_TAC true) goal
        val (ty_tm_dict, strings) = SmtLib.goal_to_SmtLib_with_get_proof goal
      in
        (((goal, validation), ty_tm_dict), strings)
      end)
    "z3 PROOF_MODE=2 -smt2 -file:"
    (fn ((goal, validation), (ty_dict, tm_dict)) =>
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
              val tm_dict = Redblackmap.foldl (fn ((tm, n), s, dict) =>
                Redblackmap.insert (dict, s, [Lib.K (SmtLib_Theories.zero_args
                  (fn args =>
                    if List.length args = n then
                      Term.list_mk_comb (tm, args)
                    else
                      raise Feedback.mk_HOL_ERR "Z3" ("<" ^ s ^ ">")
                        "wrong number of arguments"))]))
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
              val (As, g) = goal
              val thm = Thm.CCONTR g thm
              val thm = validation [thm]
            in
              SolverSpec.UNSAT (SOME thm)
            end
          | _ => (result before TextIO.closeIn instream)
        end)

end
