signature Thms =
sig
 type thm = Thm.thm

   val WF_INDUCTION_THM:thm
   val WFREC_COROLLARY :thm
   val CUT_DEF         :thm
   val CUT_LEMMA       :thm
   val SELECT_AX       :thm
   val COND_CONG       :thm
   val IMP_CONG        :thm
   val LET_CONG        :thm
   val eqT             :thm
   val imp_elim        :thm
   val rev_eq_mp       :thm
   val simp_thm        :thm
end;
