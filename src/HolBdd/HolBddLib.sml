(*
load "Varmap";
load "HolBddTheory";
load "PrimitiveBddRules";
load "DerivedBddRules";
*)

open HolBddTheory Varmap PrimitiveBddRules DerivedBddRules;


(*****************************************************************************)
(* Initialise BuDDy                                                          *)
(*****************************************************************************)

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();
