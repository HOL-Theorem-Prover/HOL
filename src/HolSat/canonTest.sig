(* ========================================================================= *)
(* PROBLEMS TO TEST THE HOL NORMALIZATION FUNCTIONS.                         *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature canonTest =
sig

  type term = Term.term
  type thm = Thm.thm
  type tactic = Abbrev.tactic

  (* The pigeon-hole principle, courtesy of Konrad Slind *)
  val pigeon : int -> term
  val var_pigeon : int -> term

end
