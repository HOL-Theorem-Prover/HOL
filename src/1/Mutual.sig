(* ===================================================================== *)
(* FILE          : Mutual.sig                                            *)
(* DESCRIPTION   : Signature for tools associated with datatypes         *)
(*                 defined by mutual recursion.                          *)
(*                 We provide an induction tactic, adapted from the      *)
(*                 standard INDUCT_THEN operator, which was translated   *)
(*                 from the HOL 88 version.                              *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* ADAPTOR       : Peter Vincent Homeier, University of Pennsylvania     *)
(* DATE          : March 27, 1998                                        *)
(* ===================================================================== *)


signature Mutual =
sig
   include Abbrev

   val MUTUAL_INDUCT_THEN : thm -> (thm -> tactic) -> tactic
   val MUTUAL_INDUCT_TAC : thm -> tactic
end
