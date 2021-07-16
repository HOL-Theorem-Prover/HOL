signature l3_equivalenceLib =
sig
  include Abbrev

  val mk_blast_thm : term -> thm

  val l3_eval : thm list -> term -> thm;
  val l3_eval_tac : thm list -> tactic;
  val l3_decode : term -> thm
  val l3_decode_tac : tactic
  val l3_run : term -> thm list
  val l3_run_tac : tactic

  val CEVAL : conv
  val asl_execute : term -> thm
  val asl_cexecute : term -> thm
  val asl_execute_tac : tactic
  val asl_cexecute_tac : tactic

  val unfold_rws : thm
  val encode_rws : thm
  val monad_rws : thm
  val asl_word_rws : thm

  val state_rel_tac : thm list -> tactic

end
