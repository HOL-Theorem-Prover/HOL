(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

signature HolSmtLib = sig

  (* a tracing variable "HolSmtLib" is provided via Feedback.register_trace *)

  exception SMT_cex of Thm.thm (* counterexample *)

  val GENERIC_SMT : SolverSpec.T -> Term.term -> Thm.thm

  val YICES_ORACLE : Term.term -> Thm.thm

end
