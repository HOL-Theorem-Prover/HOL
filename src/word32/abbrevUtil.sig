signature abbrevUtil =
sig
   val arithr_ss : simpLib.simpset
   val definition : string -> Abbrev.thm
   val LEFT_REWRITE_TAC : Abbrev.thm list -> Abbrev.tactic
   val RIGHT_REWRITE_TAC : Abbrev.thm list -> Abbrev.tactic
   val B_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val S_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val A_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val R_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val ASM_B_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val ASM_S_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val ASM_A_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val ASM_R_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val B_RW_TAC : Abbrev.thm list -> Abbrev.tactic
   val S_RW_TAC : Abbrev.thm list -> Abbrev.tactic
   val A_RW_TAC : Abbrev.thm list -> Abbrev.tactic
   val R_RW_TAC : Abbrev.thm list -> Abbrev.tactic
   val B_FULL_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val S_FULL_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val A_FULL_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
   val R_FULL_SIMP_TAC : Abbrev.thm list -> Abbrev.tactic
end
