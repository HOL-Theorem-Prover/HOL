(* wlogLib.sml - Without loss of generality tacticals

   by Mario Castelán Castro                                                  UOK
      (see doc/copyrights/public-domain-contributions.txt)
*)

signature wlogLib =
sig
  include Abbrev

  val wlog_then : term quotation ->
                  term quotation list -> thm_tactic -> tactic
  val wlog_tac  : term quotation -> term quotation list -> tactic
end
