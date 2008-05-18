(*****************************************************************************)
(*  HolSatLib.sml                                                            *)
(*                                                                           *)
(*  MJCG: Tue May 29, 2004                                                   *)
(*  HA  : Sun Mar 19, 2006                                                   *)
(*****************************************************************************)

structure HolSatLib :> HolSatLib = struct

exception SAT_cex = minisatProve.SAT_cex

open satTools dimacsTools SatSolvers minisatProve satConfig

end;


