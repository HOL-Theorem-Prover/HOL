(*
load "HolBdd";
load "StateEnum";
*)

open HolBdd StateEnum;


(*****************************************************************************)
(* Initialise BuDDy                                                          *)
(*****************************************************************************)

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();
