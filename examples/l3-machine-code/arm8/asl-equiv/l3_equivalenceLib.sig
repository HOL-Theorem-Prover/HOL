signature l3_equivalenceLib =
sig
  include Abbrev

  val mk_blast_thm : term -> thm
  val b64 : hol_type -> thm -> thm
  val b32 : hol_type -> thm -> thm
  val one : hol_type
  val qcollapse_tac : term quotation -> tactic

  val l3_eval : thm list -> term -> thm
  val l3_eval_tac : thm list -> tactic
  val l3_decode : term -> thm
  val l3_decode_tac : tactic
  val l3_run : term -> thm list
  val l3_run_tac : tactic

  val CEVAL : conv
  val asl_execute : term -> thm
  val asl_cexecute : term -> thm
  val asl_execute_tac : tactic
  val asl_cexecute_tac : tactic

  val encode_rws : thm
  val asl_word_rws : thm
  val asl_reg_rws : thm
  val l3_reg_rws : thm
  val asl_sys_reg_rws : thm

  val state_rel_tac : thm list -> tactic

end
