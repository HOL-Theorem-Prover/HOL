(* ===================================================================== *)
(* FILE          : resolve.sig                                           *)
(* ===================================================================== *)


signature Ho_resolve =
sig
type thm = Thm.thm;
type tactic = Abbrev.tactic;
type conv = Abbrev.conv;

    val MATCH_MP : thm -> thm -> thm
    val MATCH_MP_TAC : thm -> tactic
    val BACKCHAIN_TAC : thm -> tactic
    val MATCH_ACCEPT_TAC : thm -> tactic
    val HIGHER_REWRITE_CONV : thm list -> conv
end (* sig *)
