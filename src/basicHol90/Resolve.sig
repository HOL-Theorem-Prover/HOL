(* ===================================================================== *)
(* FILE          : resolve.sig                                           *)
(* DESCRIPTION   : Signature for HOL-style resolution (MP + pattern      *)
(*                 matching). Translated from hol88.                     *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Resolve =
sig
val MATCH_ACCEPT_TAC : Abbrev.thm_tactic
val ANTE_RES_THEN    : Abbrev.thm_tactical
val RES_CANON        : Thm.thm -> Thm.thm list
val IMP_RES_THEN     : Abbrev.thm_tactic -> Thm.thm -> Abbrev.tactic
val RES_THEN         : Abbrev.thm_tactic -> Abbrev.tactic
val IMP_RES_TAC      : Abbrev.thm_tactic
val RES_TAC          : Abbrev.tactic
val MATCH_MP_TAC     : Abbrev.thm_tactic
end;
