signature Halts =
sig

  type term = Term.term
  type thm  = Thm.thm
  type tactic = Abbrev.tactic

   val guess_termination_relation : thm -> term list
   val halts  : tactic -> thm -> thm
   val prover : tactic
end
