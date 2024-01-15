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
      " --lang smt "
      (Lib.K is_sat_file)

end
