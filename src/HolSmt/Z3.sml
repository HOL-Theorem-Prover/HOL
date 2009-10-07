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
      (fn (goal, (ty_dict, tm_dict)) =>
         let
           val result = is_sat_Unix outfile
         in
           case result of
             SolverSpec.UNSAT NONE =>
             let
               val thm = Z3_ProofReplay.check_proof
                 (Z3_ProofParse.parse_proof_file outfile)
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
               (* discharging definitions: INT_MIN, INT_MAX, ABS *)
               val INT_ABS = intLib.ARITH_PROVE
                 ``!x. ABS (x:int) = if x < 0 then 0 - x else x``
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
           | _ => result
         end)
      [infile, outfile]
  end

(*
    (* invert 'ty_dict' (which is a map from types to strings): we need a map
       from strings to types *)
    val inverse_ty_dict = ref (Redblackmap.foldl (fn (ty, s, dict) =>
      case Redblackmap.peek (dict, s) of
        NONE =>
        Redblackmap.insert (dict, s, ty)
      | SOME _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
          ("inverting dictionary: more than one type maps to '" ^ s ^ "'"))
      ) (Redblackmap.mkDict String.compare) ty_dict)
    (* invert 'tm_dict' (which is a map from terms to strings): we need a map
       from strings to terms *)
    val inverse_tm_dict = ref (Redblackmap.foldl (fn (tm, s, dict) =>
      case Redblackmap.peek (dict, s) of
        NONE =>
        Redblackmap.insert (dict, s, tm)
      | SOME _ =>
        raise (Feedback.mk_HOL_ERR "Z3" "parse_proof_file"
          ("inverting dictionary: more than one term maps to '" ^ s ^ "'"))
      ) (Redblackmap.mkDict String.compare) tm_dict)
*)

end
