signature tttSetup =
sig

  (* recording *)
  val ttt_record_flag    : bool ref
  val ttt_reclet_flag    : bool ref
  val ttt_recprove_flag  : bool ref

  (* learning *)
  val ttt_ortho_flag   : bool ref
  val ttt_ortho_number : int ref
  val ttt_selflearn_flag : bool ref

  (* evaluation *)
  val ttt_eval_flag : bool ref
  val one_in_n      : unit -> bool
  val ttt_evlet_flag : bool ref (* val ttt_evletonly_flag : bool ref *)
  val ttt_evprove_flag : bool ref
  val hh_only_flag  : bool ref
  val test_eval_hook : (string -> bool) ref

  (* preselection *)
  val ttt_maxselect_pred : int ref

  (* search *)
  val ttt_policy_coeff   : real ref
  val ttt_mcrecord_flag  : bool ref
  val ttt_mcnoeval_flag  : bool ref
  val ttt_mctriveval_flag : bool ref
  val ttt_mc_radius      : int ref
  val ttt_mc_coeff       : real ref
  val ttt_mcpresim_int   : int ref
  val ttt_evalinit_flag  : bool ref
  val ttt_evalfail_flag  : bool ref

  (* metis + holyhammer + synthetizing *)
  val ttt_metisexec_flag : bool ref
  val ttt_metishammer_flag : bool ref
  val ttt_metisrecord_flag : bool ref
  val ttt_namespacethm_flag : bool ref

  val ttt_metis_time  : real ref
  val ttt_metis_npred : int ref

  (* holyhammer *)
  val ttt_hhhammer_flag : bool ref
  val ttt_hhhammer_time : int ref
  val ttt_async_limit : int ref

  (* synthetizing *)
  val ttt_thmlarg_flag : bool ref
  val ttt_thmlarg_number : int ref
  val ttt_termarg_flag : bool ref
  val ttt_termarg_number : int ref
  val ttt_termpresim_int : int ref

  (* minimization *)
  val ttt_prettify_flag : bool ref
  val ttt_minimize_flag : bool ref

  (* init record and eval *)
  val set_record : string -> unit
  val set_record_hook : (unit -> unit) ref

end
