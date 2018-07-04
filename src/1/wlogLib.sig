(* wlogLib.sig - Without loss of generality tacticals

For the licensing information about HOL4 see the file "COPYRIGHT" in the
HOL4 distribution (note added by Mario Castelán Castro).                   UOK

For the avoidance of legal uncertainty, I (Mario Castelán Castro) hereby   UOK
place my modifications to this file in the public domain per the Creative
Commons CC0 1.0 public domain dedication <https://creativecommons.org/publ
icdomain/zero/1.0/legalcode>. This should not be interpreted as a personal
endorsement of permissive (non-Copyleft) licenses. *)

signature wlogLib =
sig
  include Abbrev

  val wlog_then : term quotation ->
                  term quotation list -> thm_tactic -> tactic
  val wlog_tac  : term quotation -> term quotation list -> tactic
end
