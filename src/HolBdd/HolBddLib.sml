structure HolBddLib =
struct

(*
load "Varmap";
load "HolBddTheory";
load "PrimitiveBddRules";
load "DerivedBddRules";
*)

open Varmap PrintBdd PrimitiveBddRules DerivedBddRules MachineTransitionTheory;


(*****************************************************************************)
(* Initialise BuDDy                                                          *)
(*****************************************************************************)

val _ = if not(bdd.isRunning()) then bdd.init 1000000 10000 else ();

end
