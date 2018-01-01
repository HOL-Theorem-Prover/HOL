signature pairSimps =
sig

  (* PAIR0_ss includes a whole bunch of obvious rewrites *)
  val PAIR0_ss : simpLib.ssfrag

  (* PAIR_ss = PAIR0_ss *)
  val PAIR_ss  : simpLib.ssfrag




val paired_forall_ss : simpLib.ssfrag
val paired_exists_ss : simpLib.ssfrag
val gen_beta_ss : simpLib.ssfrag




end
