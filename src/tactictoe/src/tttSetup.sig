signature tttSetup =
sig

  include Abbrev

  (* directories *)
  val infix_file : string
  val tactictoe_dir : string
  val ttt_debugdir : string
  val ttt_eval_updir : string 
  val ttt_eval_dir : string ref

  (* nearest neighbor *)
  val ttt_thmlarg_radius : int ref
  val ttt_ortho_radius   : int ref
  val ttt_presel_radius  : int ref

  (* recording *)
  val ttt_savestate_flag : bool ref
  val ttt_recprove_flag : bool ref
  val ttt_reclet_flag   : bool ref
  val ttt_recproof_time : real ref

  (* search *)
  val ttt_search_time : real ref
  val ttt_tactic_time : real ref
  val ttt_metis_time : real ref
  val ttt_metis_radius : int ref
  val ttt_policy_coeff : real ref
  val ttt_ex_flag : bool ref

end
