(* ========================================================================= *)
(* Tools for reasoning about wp and wlp.                                     *)
(* ========================================================================= *)

signature wpTools =
sig

  (* A useful tactic for case-splitting conditionals *)
  val if_cases_tac : Abbrev.thm_tactic -> Abbrev.tactic

  (* A theorem tactic for use with if_cases_tac for wlp calculation *)
  val wlp_assume_tac : Abbrev.thm_tactic

  (* The main tactics for reducing Leq pre (wlp prog post) *)
  val pure_wlp_tac : Abbrev.tactic
  val leq_tac      : Abbrev.tactic
  val wlp_tac      : Abbrev.tactic

end
