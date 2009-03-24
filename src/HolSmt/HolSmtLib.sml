(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Entry point into HolSmtLib. Provides GENERIC_SMT and related tactics. *)

structure HolSmtLib :> HolSmtLib = struct

  (* possible values:
     0 - no output at all (except for fatal errors)
     1 - warnings only
     2 - also diagnostic messages of constant length
     3 - also diagnostic messages that are potentially lengthy (e.g., terms,
         models, proofs)
     4 - moreover, temporary files (for communication with the SMT solver) are
         not removed after solver invocation *)
  val trace = ref 2

  val _ = Feedback.register_trace ("HolSmtLib", trace, 4)

  exception SMT_cex of Thm.thm (* counterexample *)

  (* single entry point into HolSmtLib *)
  fun GENERIC_SMT solver tm =
    let
      val _ = if Term.type_of tm <> Type.bool then
          raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
            "term supplied is not of type bool")
        else ()
      fun write_strings_to_file path strings =
        let val outstream = TextIO.openOut path
        in
          ignore (map (TextIO.output o Lib.pair outstream) strings);
          TextIO.closeOut outstream
        end
      val files = SolverSpec.get_infile solver :: SolverSpec.get_outfiles solver
      fun remove_files () =
        if !trace < 4 then
          ignore (map (fn path => OS.FileSys.remove path handle SysErr _ => ())
            files)
        else ()
      val neg_tm = boolSyntax.mk_neg tm (* we could strip quantifiers *)
    in
      (* precaution: make sure infile and outfiles don't exist *)
      ignore (map (fn path => if OS.FileSys.access (path, []) then
          raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
            ("file '" ^ path ^ "' exists, please remove it"))
        else ()) files);
      if !trace > 1 then
        Feedback.HOL_MESG ("HolSmtLib: calling external SMT solver '" ^
          SolverSpec.get_name solver ^ "'")
      else ();
      if !trace > 2 then
        Feedback.HOL_MESG ("Passing term: " ^ Hol_pp.term_to_string neg_tm)
      else ();
      (* writing the SMT file *)
      write_strings_to_file (SolverSpec.get_infile solver)
        (SolverSpec.get_translation_fn solver neg_tm);
      (* the actual system call to the SMT solver *)
      Systeml.system_ps (SolverSpec.get_command solver);
      (* result parsing *)
      if SolverSpec.get_is_sat_fn solver () then (
        if !trace > 1 then
          Feedback.HOL_MESG ("HolSmtLib: solver reports 'satisfiable'")
        else ();
        case SolverSpec.get_model_fn solver of
          NONE =>
          (
            remove_files ();
            raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
              "solver reports negated term to be 'satisfiable'")
          )
        | SOME model_fn =>
          let val model = model_fn ()
          in
            remove_files ();
            raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
              "counterexamples not implemented yet")
          end
      ) else (
        if !trace > 1 then
          Feedback.HOL_MESG ("HolSmtLib: solver reports 'unsatisfiable'")
        else ();
        case SolverSpec.get_proof_fn solver of
          NONE =>
          (
            remove_files ();
            Thm.mk_oracle_thm ("HolSmtLib (" ^ SolverSpec.get_name solver ^ ")")
              ([], tm)
          )
        | SOME proof_fn =>
          let val proof = proof_fn ()
          in
            remove_files ();
            raise (Feedback.mk_HOL_ERR "HolSmtLib" "GENERIC_SMT"
              "proof checking not implemented yet")
          end
      )
    end

  fun YICES_ORACLE tm =
    GENERIC_SMT Yices.YicesOracle tm

end
