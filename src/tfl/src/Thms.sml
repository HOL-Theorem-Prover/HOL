structure Thms :> Thms =
struct

 open HolKernel Parse Drule Tactical Tactic Conv Resolve Rewrite;
 infix THEN;
 type thm = Thm.thm

   val LET_DEF          = boolTheory.LET_DEF;
   val WF_INDUCTION_THM = relationTheory.WF_INDUCTION_THM
   val WFREC_COROLLARY  = relationTheory.WFREC_COROLLARY
   val CUT_DEF          = relationTheory.RESTRICT_DEF
   val CUT_LEMMA        = relationTheory.RESTRICT_LEMMA

   val SELECT_AX = boolTheory.SELECT_AX;

   val COND_CONG = prove(
     --`!P P' (x:'a) x' y y'.
        (P = P') /\
        (P'  ==> (x = x')) /\
        (~P' ==> (y = y'))
           ==>
        ((if P then x else y) = (if P' then x' else y'))`--,
      REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC THEN REPEAT RES_TAC);

(* Forward proof attempt
val P_eq_P' = ASSUME (Term`P:bool = P'`)
val x_eq_x' = ASSUME (Term`P' ==> (x:'a = x')`)
val y_eq_y' = ASSUME (Term`~P' ==> (y:'a = y')`)
val lhs = Term`if P then x else y:'a`
val rhs = Term`if P' then x' else y':'a`;
val v = mk_var("v",bool);
val concl1 = SUBST [(P_eq_P',v)]
              (Term`^lhs = if ^v then x else y:'a`)
              (REFL lhs)
val concl2 = SUBST [(
*)
   val IMP_CONG = prove(
       --`!x x' y y'. 
             (x=x') /\ (x' ==> (y = y'))
                ==>
             (x ==> y = x' ==> y')`--,
     REPEAT GEN_TAC
     THEN BOOL_CASES_TAC(--`x':bool`--)
     THEN BOOL_CASES_TAC(--`x:bool`--) THEN REWRITE_TAC[]);


   val LET_CONG = prove(
     --`!f (g:'a->'b) M M'.
          (M = M') /\
          (!x:'a. (x = M') ==> (f x = g x))
           ==>
          (LET f M = LET g M')`--,
      REPEAT STRIP_TAC
      THEN REWRITE_TAC[boolTheory.LET_DEF]
      THEN BETA_TAC
      THEN RES_TAC
      THEN ASM_REWRITE_TAC[]);


   local fun bval w t = (type_of t = Parse.Type`:bool`) andalso
                        (can (find_term is_var) t) andalso
                        (free_in t w)
    val TAUT_CONV =
       C (curry prove)
         (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
           (C (curry op THEN) (Rewrite.REWRITE_TAC[]) o BOOL_CASES_TAC o hd
                               o sort free_in
                               o W(find_terms o bval) o snd))
         o Parse.Term
   val P = GEN_ALL o TAUT_CONV;
   in 
      val thm_eq    = P `x ==> y ==> (x = y)`
      val eqT       = P `(x = T) ==> x`
      val imp_elim  = P `P ==> (P ==> Q = P ==> R) = (P ==> Q = P ==> R)`
      val rev_eq_mp = P `(x = y) ==> y ==> x`
      val simp_thm  = P `(x==>y) ==> (x = x') ==> (x' ==> y)`
  end;

end;
