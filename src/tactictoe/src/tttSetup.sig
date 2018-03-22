signature tttSetup =
sig

  (** Recording **)
  val ttt_reclet_flag   : bool ref
  val ttt_recprove_flag : bool ref
  val ttt_rectac_time   : real ref
  val ttt_recproof_time : real ref
  val set_recording : unit -> unit

  (** Training **) 
  val ttt_namespacethm_flag : bool ref
  (* orthgonalization *)
  val ttt_ortho_flag   : bool ref
  val ttt_ortho_radius : int ref
  (* abstraction *)
  val ttt_thmlarg_flag   : bool ref
  val ttt_thmlarg_radius : int ref
  val ttt_recgl_flag   : bool ref
  val set_training : unit -> unit
  
  (** Evaluation **)
  (* evaluated theorems *)
  val one_in_option : (int * int) option ref
  val one_in_n      : unit -> bool
  val ttt_evlet_flag : bool ref
  val ttt_evprove_flag : bool ref
  val evaluation_filter : (string -> bool) ref
  (* preselection *)
  val ttt_presel_radius : int ref
  (* search *)
  val ttt_mcpol_coeff   : real ref
  val ttt_mcevnone_flag : bool ref
  val ttt_mcevtriv_flag : bool ref
  val ttt_mcev_radius   : int ref
  val ttt_mcev_coeff    : real ref
  val ttt_mcev_pint     : int ref
  val ttt_mcevinit_flag : bool ref
  val ttt_mcevfail_flag : bool ref
  (* metis *)
  val ttt_metis_flag   : bool ref
  val ttt_metis_time   : real ref
  val ttt_metis_radius : int ref
  (* proof presentation *)
  val ttt_prettify_flag : bool ref
  val ttt_minimize_flag : bool ref

  val set_evaluation : string -> unit
  
  (** Additional parameters **)
  (* eprover *)
  val ttt_eprover_flag     : bool ref
  val ttt_eprover_time     : int ref
  val ttt_eprover_radius   : int ref 
  val ttt_eprover_async    : int ref
  val ttt_eprovereval_flag : bool ref
  (* term predictions *)
  val ttt_termarg_flag : bool ref
  val ttt_termarg_radius : int ref
  val ttt_termarg_pint : int ref
  val ttt_selflearn_flag : bool ref




end
