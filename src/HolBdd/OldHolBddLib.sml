(*
load "HolBdd";
load "StateEnum";
*)

open HolBdd StateEnum BddRules;


(*****************************************************************************)
(* Initialise BuDDy                                                          *)
(*****************************************************************************)

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();
