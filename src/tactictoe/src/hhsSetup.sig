signature hhsSetup =
sig
  
  (* recording *)
  val hhs_internalthm_flag : bool ref
  val hhs_norecprove_flag  : bool ref
  val hhs_norecord_flag    : bool ref
  val hhs_nolet_flag       : bool ref
  
  (* learning *)
  val hhs_ortho_flag   : bool ref
  val hhs_ortho_number : int ref
  val hhs_ortho_metis  : bool ref
  val hhs_ortho_deep   : bool ref
  
  val hhs_thmortho_flag : bool ref

  val hhs_selflearn_flag : bool ref
  val hhs_succrate_flag  : bool ref
  
  (* evaluation *)
  val one_in_n      : unit -> bool
  val hhs_eval_flag : bool ref
  val hhs_noprove_flag : bool ref
  val hh_only_flag  : bool ref
  
  (* preselection *)
  val hhs_maxselect_pred : int ref
  
  (* search *)
  val hhs_cache_flag     : bool ref
  val hhs_mc_flag        : bool ref
  val hhs_mc_radius      : int ref
  val hhs_mc_preradius   : int ref
  val hhs_mc_coeff       : real ref
  val hhs_timedepth_flag : bool ref
  val hhs_width_coeff    : real ref
  
  (* metis + holyhammer + synthetizing *)
  val hhs_metis_flag  : bool ref
  val hhs_metis_time  : real ref
  val hhs_metis_npred : int ref (* used in learning *)
  val hh_stac_flag      : bool ref
  val hhs_stacpred_flag : bool ref (* synthetizing *)
  val hhs_stacpred_number : int ref
  
  (* minimization *)
  val hhs_prettify_flag : bool ref
  val hhs_minimize_flag : bool ref
  
  (* allows to test for the name of the theorem 
     before evaluation *)
  val test_eval_hook : (string -> bool) ref
  
  (* init search *)
  val set_isearch : unit -> unit
  val set_isearch_hook : (unit -> unit) ref
  val set_esearch : unit -> unit
  
  (* init record and eval *)
  val set_irecord : unit -> unit
  val set_erecord : unit -> unit

end
