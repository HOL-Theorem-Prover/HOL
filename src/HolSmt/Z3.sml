(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Functions to invoke the Z3 SMT solver *)

structure Z3 = struct

  (* returns SAT if Z3 reported 'sat_line', UNSAT if Z3 reported 'unsat_line' *)
  fun is_sat sat_line unsat_line path =
    let val instream = TextIO.openIn path
        (* skip over Z3's other output (e.g., proofs) *)
        fun last_line () =
          let val line = TextIO.inputLine instream
          in
            if TextIO.endOfStream instream then
              line
            else
              last_line ()
          end
        val line = last_line ()
    in
      TextIO.closeIn instream;
      if line = SOME sat_line then
        SolverSpec.SAT NONE
      else if line = SOME unsat_line then
        SolverSpec.UNSAT NONE
      else
        SolverSpec.UNKNOWN NONE
    end

  (* DOS-style CR/LF line breaks *)
  val is_sat_DOS = is_sat "sat\r\n" "unsat\r\n"

  (* Unix-style line breaks *)
  val is_sat_Unix = is_sat "sat\n" "unsat\n"

  local
    val infile = "input.z3.smt"
    val outfile = "output.z3"
  in
    (* Z3 (via Wine), SMT-LIB file format, no proofs *)
    val Z3_Wine_SMT_Oracle = SolverSpec.make_solver
      (Library.write_strings_to_file infile o Lib.snd o SmtLib.goal_to_SmtLib)
      ("wine C:\\\\Z3\\\\bin\\\\z3.exe /smt " ^ infile ^ " > " ^ outfile)
      (fn () => is_sat_DOS outfile)
      [infile, outfile]

    (* Z3 (Linux/Unix), SMT-LIB file format, no proofs *)
    val Z3_SMT_Oracle = SolverSpec.make_solver
      (Library.write_strings_to_file infile o Lib.snd o SmtLib.goal_to_SmtLib)
      ("z3 -smt " ^ infile ^ " > " ^ outfile)
      (fn () => is_sat_Unix outfile)
      [infile, outfile]

    (* Z3 (Linux/Unix), SMT-LIB file format, with proofs *)
    val Z3_SMT_Prover = SolverSpec.make_solver
      (fn goal =>
        let
          val (ty_tm_dict, lines) = SmtLib.goal_to_SmtLib goal
        in
          Library.write_strings_to_file infile lines;
          (goal, ty_tm_dict)
        end)
      ("z3 -ini:z3.ini -smt " ^ infile ^ " > " ^ outfile)
      (fn (goal, ty_tm_dict) =>
         let
           val result = is_sat_Unix outfile
         in
           case result of
             SolverSpec.UNSAT NONE =>
             let
               val thm = Z3_ProofReplay.check_proof
                 (Z3_ProofParse.parse_proof_file outfile ty_tm_dict)
               (* discharging definitions: INT_MIN, INT_MAX, ABS *)
               val INT_ABS = intLib.ARITH_PROVE
                 ``!x. ABS (x:int) = if x < 0 then 0 - x else x``
               (* bool_case is replaced by if_then_else by the translation to
                  SMT-LIB format; this must therefore be done in the goal as
                  well *)
               (* returns SOME "tm |- (... if-then-else ...)", or NONE *)
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
           | _ => result
         end)
      [infile, outfile]
  end

end
