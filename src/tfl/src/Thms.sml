structure Thms :> Thms =
struct

 open HolKernel Parse Drule Tactical Tactic Conv Resolve;
 infix THEN;
 type thm = Thm.thm

   val LET_DEF          = boolTheory.LET_DEF;
   val WF_INDUCTION_THM = relationTheory.WF_INDUCTION_THM
   val WFREC_COROLLARY  = relationTheory.WFREC_COROLLARY
   val CUT_DEF          = relationTheory.RESTRICT_DEF
   val CUT_LEMMA        = relationTheory.RESTRICT_LEMMA

   (* SELECT_AX = |- !P x. P x ==> P ($@ P) *)
   val SELECT_AX = boolTheory.SELECT_AX;
   val COND_CONG = boolTools.COND_CONG
   val LET_CONG  = boolTools.LET_CONG;

   local fun bval w t = (type_of t = Parse.Type`:bool`) andalso
                        (can (find_term is_var) t) andalso
                        (free_in t w)
   in val TAUT_CONV =
       C (curry prove)
         (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
           (C (curry op THEN) (Rewrite.REWRITE_TAC[]) o BOOL_CASES_TAC o hd
                               o sort free_in
                               o W(find_terms o bval) o snd))
         o Parse.Term
   end;

   val P = GEN_ALL o TAUT_CONV;

   val thm_eq    = P `x ==> y ==> (x = y)`
   val eqT       = P `(x = T) ==> x`
   val imp_elim  = P `P ==> (P ==> Q = P ==> R) = (P ==> Q = P ==> R)`
   val rev_eq_mp = P `(x = y) ==> y ==> x`
   val simp_thm  = P `(x==>y) ==> (x = x') ==> (x' ==> y)`

end;
