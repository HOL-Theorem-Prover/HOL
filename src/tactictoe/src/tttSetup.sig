signature tttSetup =
sig

  (* Nearest neighbor *)
  val ttt_thmlarg_radius = ref 16
  val ttt_ortho_radius   = ref 10
  val ttt_presel_radius  = ref 500

  (* Recording *)
  val ttt_recprove_flag  = ref true
  val ttt_reclet_flag    = ref false
  val ttt_rectac_time    = ref 2.0
  val ttt_recproof_time  = ref 20.0

  (* Metis *)
  val init_metis : unit -> unit
  val ttt_metis_time   = ref 0.1
  val ttt_metis_radius = ref 16

  (* MCTS *)
  val ttt_policy_coeff = ref 0.5


end
