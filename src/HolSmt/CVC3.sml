(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Functions to invoke the CVC3 SMT solver *)

structure CVC3 = struct

  (* returns true if CVC3 reported "sat", false if CVC3 reported "unsat" *)
  fun is_sat path =
    let val instream = TextIO.openIn path
        val line     = TextIO.inputLine instream
    in
      TextIO.closeIn instream;
      if line = "sat\n" then
        true
      else if line = "unsat\n" then
        false
      else
        raise (Feedback.mk_HOL_ERR "CVC3" "is_sat"
          "satisfiability unknown (solver not installed/problem too hard?)")
    end

  (* CVC3, SMT-LIB file format *)
  local val infile = "input.cvc3.smt"
        val outfile = "output.cvc3"
  in
    val CVC3SMTOracle = SolverSpec.make_solver
      ("CVC3 (SMT-LIB)",
       "cvc3-optimized -lang smt " ^ infile ^ " > " ^ outfile,
       SmtLib.term_to_SmtLib,
       infile,
       [outfile],
       (fn () => is_sat outfile),
       NONE,  (* no models *)
       NONE)  (* no proofs *)
  end

end
