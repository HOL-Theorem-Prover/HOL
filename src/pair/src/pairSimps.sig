signature pairSimps =
sig

  (* PAIR0_ss includes the conversion GEN_BETA_CONV for doing beta-reduction over
     UNCURRY terms, and a whole bunch of obvious rewrites *)
  val PAIR0_ss : simpLib.ssfrag

  (* PAIR_ss = PAIR0_ss + boolSimps.LET_ss
       (it's not really clear why LET_ss gets introduced at this point
  *)
  val PAIR_ss  : simpLib.ssfrag
end
