signature word8CasesLib = sig

val word8Define : Term.term -> Thm.thm
val word8Cases_on : Term.term frag list -> Tactic.tactic

end