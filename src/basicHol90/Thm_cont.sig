(* ===================================================================== *)
(* FILE          : thm_cont.sig                                          *)
(* DESCRIPTION   : Signature for theorem continuations. Translated from  *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHOR        : (c) Larry Paulson and others,                         *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Thm_cont =
sig

val THEN_TCL : Abbrev.thm_tactical * Abbrev.thm_tactical -> Abbrev.thm_tactical
val ORELSE_TCL : Abbrev.thm_tactical * Abbrev.thm_tactical -> Abbrev.thm_tactical
val REPEAT_TCL : Abbrev.thm_tactical -> Abbrev.thm_tactical
val REPEAT_GTCL : Abbrev.thm_tactical -> (Thm.thm -> Abbrev.tactic) -> Abbrev.thm_tactic
val ALL_THEN : Abbrev.thm_tactical
val NO_THEN : Abbrev.thm_tactical
val EVERY_TCL : Abbrev.thm_tactical list -> Abbrev.thm_tactical
val FIRST_TCL : Abbrev.thm_tactical list -> Abbrev.thm_tactical
val CONJUNCTS_THEN2 : Abbrev.thm_tactic -> Abbrev.thm_tactical
val CONJUNCTS_THEN : Abbrev.thm_tactical
val DISJ_CASES_THEN2 : Abbrev.thm_tactic -> Abbrev.thm_tactical
val DISJ_CASES_THEN : Abbrev.thm_tactical
val DISJ_CASES_THENL : Abbrev.thm_tactic list -> Abbrev.thm_tactic
val DISCH_THEN : Abbrev.thm_tactic -> Abbrev.tactic
val X_CHOOSE_THEN : Term.term -> Abbrev.thm_tactical
val CHOOSE_THEN : Abbrev.thm_tactical
val X_CASES_THENL : (('a list -> 'b list -> ('a * 'b) list) ->
                  Abbrev.thm_tactic list -> (Term.term list * Abbrev.thm_tactic) list) ->
                  Abbrev.thm_tactic list -> Abbrev.thm_tactic
val X_CASES_THEN : Term.term list list -> Abbrev.thm_tactical
val CASES_THENL : Abbrev.thm_tactic list -> Abbrev.thm_tactic
val STRIP_THM_THEN : Abbrev.thm_tactical
end;
