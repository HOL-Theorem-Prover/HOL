signature tttSetup =
sig

  include Abbrev

  (* directories *)
  val infix_file : string
  val tactictoe_dir : string
  val ttt_eval_dir : string

  (* nearest neighbor predictor *)
  val ttt_thmlarg_radius : int ref
  val ttt_ortho_radius   : int ref
  val ttt_presel_radius  : int ref

  (* recording *)
  val record_flag : bool ref
  val record_ortho_flag : bool ref
  val record_savestate_flag : bool ref
  val record_prove_flag : bool ref
  val record_let_flag   : bool ref
  val record_tactic_time : real ref
  val record_proof_time : real ref
  val learn_tactic_time : real ref
  val learn_abstract_term : bool ref
  val export_thmdata_flag : bool ref

  (* search *)
  val ttt_search_time : real ref
  val ttt_tactic_time : real ref
  val ttt_metis_flag : bool ref
  val ttt_metis_time : real ref
  val ttt_metis_radius : int ref
  val ttt_policy_coeff : real ref
  val ttt_explo_coeff : real ref
  val ttt_ex_flag : bool ref

end
