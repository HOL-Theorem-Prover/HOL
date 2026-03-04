(* Functions to invoke the cvc5 SMT solver *)

structure CVC = struct

  (* returns SAT if cvc5 reported "sat", UNSAT if cvc5 reported "unsat" *)
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

  fun is_configured () =
      let val v = OS.Process.getEnv "HOL4_CVC_EXECUTABLE" in
          (Option.isSome v) andalso (Option.valOf v <> "")
      end;

  val error_msg = "CVC not configured: set the HOL4_CVC_EXECUTABLE environment variable to point to the cvc5 executable file.";

  fun mk_CVC_fun name pre cmd_stem post goal =
    case OS.Process.getEnv "HOL4_CVC_EXECUTABLE" of
      SOME file =>
        if file = "" then
           raise Feedback.mk_HOL_ERR "CVC" name error_msg
        else
           SolverSpec.make_solver pre (file ^ cmd_stem) post goal
    | NONE =>
        raise Feedback.mk_HOL_ERR "CVC" name error_msg

  (* cvc5, SMT-LIB file format, no proofs *)
  val CVC_SMT_Oracle =
    mk_CVC_fun "CVC_SMT_Oracle"
      (fn goal =>
        let
          val (goal, _) = SolverSpec.simplify (SmtLib.SIMP_TAC false) goal
          val (_, strings) = SmtLib.goal_to_SmtLib (SOME "ALL") goal
        in
          ((), strings)
        end)
      (* Some options were added due to:
         https://github.com/cvc5/cvc5/issues/10293 *)
      " --macros-quant --macros-quant-mode=all --lang smt "
      (Lib.K is_sat_file)

  (* cvc5, SMT-LIB file format, with Alethe proofs *)
  val CVC_SMT_Prover =
    mk_CVC_fun "CVC_SMT_Prover"
      (fn goal =>
        let
          val (goal, validation) = SolverSpec.simplify (SmtLib.SIMP_TAC true) goal
          val (ty_tm_dict, strings) =
            SmtLib.goal_to_SmtLib_with_get_proof (SOME "ALL") goal
        in
          (((goal, validation), ty_tm_dict), strings)
        end)
      " --produce-proofs --dump-proofs --proof-format-mode=alethe --lang smt "
      (fn ((goal, validation), (ty_dict, tm_dict)) =>
        fn outfile =>
          let
            val instream = TextIO.openIn outfile
            val result = is_sat_stream instream
          in
            case result of
              SolverSpec.UNSAT NONE =>
              let
                (* invert dictionaries for proof parsing, same as Z3.sml *)
                val ty_dict = Redblackmap.foldl (fn (ty, s, dict) =>
                  Redblackmap.insert (dict, s, [SmtLib_Theories.K_zero_zero ty]))
                  (Redblackmap.mkDict String.compare) ty_dict
                val tm_dict = Redblackmap.foldl (fn ((tm, n), s, dict) =>
                  Redblackmap.insert (dict, s, [Lib.K (SmtLib_Theories.zero_args
                    (fn args =>
                      if List.length args = n then
                        Term.list_mk_comb (tm, args)
                      else
                        raise Feedback.mk_HOL_ERR "CVC" ("<" ^ s ^ ">")
                          "wrong number of arguments"))]))
                  (Redblackmap.mkDict String.compare) tm_dict
                (* add relevant SMT-LIB types/terms to dictionaries *)
                val ty_dict = Library.union_dict (Library.union_dict
                  SmtLib_Logics.AUFNIRA.tydict SmtLib_Logics.QF_ABV.tydict)
                  ty_dict
                val tm_dict = Library.union_dict (Library.union_dict
                  SmtLib_Logics.AUFNIRA.tmdict SmtLib_Logics.QF_ABV.tmdict)
                  tm_dict
                (* parse the Alethe proof *)
                val proof = Alethe_ProofParser.parse_stream
                  (ty_dict, tm_dict) instream
                val _ = TextIO.closeIn instream
                val _ = if List.null proof then
                          raise Feedback.mk_HOL_ERR "CVC" "CVC_SMT_Prover"
                            "cvc5 returned empty proof (may be unsupported)"
                        else ()
                val (As, g) = goal
                val thm = Alethe_ProofReplay.check_proof (As, g, proof)
                val thm = Thm.CCONTR g thm
                val thm = validation [thm]
              in
                SolverSpec.UNSAT (SOME thm)
              end
            | _ => (result before TextIO.closeIn instream)
          end)

end
