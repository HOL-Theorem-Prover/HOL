(* ===================================================================== *)
(* FILE          : mutual_induct_then.sig                                *)
(* DESCRIPTION   : Signature for a generalized induction tactic.         *)
(*                 for datatypes defined using Elsa Gunter's             *)
(*                 mutual recursive datatype libraries.                  *)
(*                 Adapted from the standard INDUCT_THEN operator,       *)
(*                 which was translated from the HOL 88 version.         *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* ADAPTOR       : Peter Vincent Homeier, University of Pennsylvania     *)
(* DATE          : March 27, 1998                                        *)
(* ===================================================================== *)


signature Mutual_induct_then_sig =
sig
structure Thm : Thm_sig
val MUTUAL_INDUCT_THEN : Thm.thm -> thm_tactic -> tactic
end;
