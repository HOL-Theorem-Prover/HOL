(*--------------------------------------------------------------------*
 * Define some type abbreviations.                                    *
 *--------------------------------------------------------------------*)

structure Abbrev =
struct
   local
      open Thm
      open Term
   in
      type conv = term -> thm
      type goal = term list * term
      type validation = thm list -> thm
      type tactic = goal -> goal list * validation;
      type thm_tactic = thm -> tactic
      type thm_tactical = thm_tactic -> thm_tactic;
   end;
end;
