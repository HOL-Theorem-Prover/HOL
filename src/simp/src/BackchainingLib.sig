signature BackchainingLib =
sig
 include Abbrev

  (* Applying theorems of the form

     !x y. R x y ==> !x' y'. some complicated condition ==> R x' y'

     is a bit tricky. However, such theorems occurs frequently when e.g. R is a
     relation between states and one wants to show that after certain steps
     the resulting states are still in this relation.

     Conditional rewriting (as implemented by the simplifier) requires
     finding instances for the variables "x" and "y". Such instances
     usually cannot be found by the simplifier, even if a term of the
     form "R a b" is present in the list of assumptions. Applying
     MATCH_MP_TAC is of course possible, but often tedious. Similarly,
     consequence conversions work, but easily loop or might - in the
     presence of multiple rules - pick up the wrong rule. IMP_RES_TAC
     and similar tools, easily produce too many instances and clutter
     the goal-state.

     This library tries to address that. Let "bc_thms" be a
     list of theorems of the form
     (!x1 ... xn y1 ... yn. P x1 ... xn ==> Q x1 ... xn y1 ... yn).
     Then "BACKCHAIN_THEN (fn thms => tac thms) bc_thms" is a tactic
     that tries to instantiate the variables x1 ... xn and discharge
     the precondition P. The resulting theorems are handed to a
     function to produce a tactic. This is done via matching against
     assumptions. BACKCHAIN_THEN is similar to IMP_RES_THEN. However,
     IMP_RES_THEN normalises P and Q, introduces many implications and
     resorts them. It applies a tactic to all theorems resulting from
     discharging one of these preconditions. In contrast
     BACKCHAIN_THEN only normalises the precondition P and returns all
     theorems resulting from discharging all preconditions produced by P.
     Moreover, BACKCHAIN_THEN applies a tactic to all resulting theorems instead
     of calling a theorem-tactic for each of them.

     BACKCHAIN_THEN is the basis of this library. By providing multiple
     instantiations for the tactic argument, the other tactics are derived.
  *)
  val BACKCHAIN_THEN : (thm list -> tactic) -> thm list -> tactic


  (* apply a theorem tactic to every resulting theorem *)
  val BACKCHAIN_EVERY_THEN : (thm -> tactic) -> thm list -> tactic

  (* Assume each resulting theorem or add it as a precondition to the goal. *)
  val BACKCHAIN_ASSUME_TAC : thm list -> tactic
  val BACKCHAIN_MP_TAC : thm list -> tactic

  (* Use the resulting theorems for backchaining via consequence conversions *)
  val BACKCHAIN_TAC : thm list -> tactic

  (* Use resulting theorems together with the simplifier *)
  val BC_SIMP_TAC      : simpLib.simpset -> thm list -> thm list -> tactic
  val ASM_BC_SIMP_TAC  : simpLib.simpset -> thm list -> thm list -> tactic
  val FULL_BC_SIMP_TAC : simpLib.simpset -> thm list -> thm list -> tactic

end
