signature setSimps =
sig

  (* contains useful rewrites and theorems for all aspects of set theory *)
  val SET_ss : simpLib.ssdata

  (* contains AC normalisers for UNION and INTER *)
  val SET_AC_ss : simpLib.ssdata

end