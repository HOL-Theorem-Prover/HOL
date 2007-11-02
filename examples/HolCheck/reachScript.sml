open HolKernel Parse boolLib bossLib 

val _ = new_theory("reach"); 

open pred_setTheory;
open pred_setLib;
open setLemmasTheory;

infix &&; infix 8 by;

val ReachNext_def = Define `ReachNext R s s' = R(s,s')`;

val ReachableRec_def = Define `
    (ReachableRec R s 0 = s) /\ 
    (ReachableRec R s (SUC n) = {s' | s' IN ReachableRec R s n \/ ?s''. ReachNext R s'' s'  /\ s'' IN ReachableRec R s n})`;

val ReachableRecSimp = save_thm("ReachableRecSimp",prove(``!R s n state. ReachableRec R s (SUC n) state = ReachableRec R s n state \/ ?state'. R (state',state) /\ ReachableRec R s n state'``,
REWRITE_TAC [ReachableRec_def]
THEN CONV_TAC (STRIP_QUANT_CONV (LHS_CONV (ONCE_REWRITE_CONV [GSYM (prove(``!x P. x IN P = P x``,PROVE_TAC [IN_DEF]))])))
THEN REWRITE_TAC [SET_SPEC_CONV ``state IN {s' | s' IN ReachableRec R s n \/ ?s''. ReachNext R s'' s' /\ s'' IN ReachableRec R s n}``]
THEN SIMP_TAC std_ss [IN_DEF,ReachNext_def]));

val Reachable_def = Define `Reachable R s = BIGUNION {P | ?n. P = ReachableRec R s n}`; 

val ReachableChain = prove(``!R s n. ReachableRec R s n SUBSET ReachableRec R s (SUC n)``,
Induct_on `n` THENL [
SIMP_TAC std_ss [ReachableRec_def,ReachNext_def,SUBSET_DEF,IN_SING,SET_SPEC],
FULL_SIMP_TAC std_ss [ReachableRec_def,ReachNext_def,SUBSET_DEF,SET_SPEC]
]);

val ReachableStable =prove(``!R s n. (ReachableRec R s n = ReachableRec R s (SUC n)) ==> 
			   !m. m >= n ==> (ReachableRec R s m = ReachableRec R s n)``, 
REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
THEN REPEAT STRIP_TAC THENL [
ASM_REWRITE_TAC [],
Induct_on `m` THENL [
 SIMP_TAC arith_ss [], (* 0 *)
 REWRITE_TAC [DECIDE ``(SUC m > n)=(m>=n)``]
 THEN REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
 THEN REPEAT STRIP_TAC THENL [

   FULL_SIMP_TAC std_ss [], (* m=n *)
   FULL_SIMP_TAC std_ss []
   THEN SIMP_TAC std_ss [ReachableRec_def,ReachNext_def,SET_SPEC] 
   THEN ASM_REWRITE_TAC []]]]);

val ReachableChainUnion = prove(``!R s n'. BIGUNION {P | ?n. n <= n' /\ (P = ReachableRec R s n)} = ReachableRec R s n'``,
REPEAT STRIP_TAC
THEN Induct_on `n'` THENL [
 REWRITE_TAC [DECIDE ``!n. n<=0 = (n=0)``]
 THEN REWRITE_TAC [BIGUNION]
 THEN SIMP_TAC std_ss [SET_SPEC]
 THEN SIMP_TAC std_ss [SET_SPEC,EXTENSION], (* 0 *)
 REWRITE_TAC [DECIDE ``!n n'. n<=(SUC n') = (n<=n' \/ (n=SUC n'))``]
 THEN REWRITE_TAC [DECIDE ``!a b c.((a\/b)/\c)=((a/\c)\/(b/\c))``]
 THEN SIMP_TAC std_ss [EXISTS_OR_THM]
 THEN SIMP_TAC std_ss [GSYM (SIMP_RULE std_ss [IN_DEF] UNION_DEF)]
 THEN SIMP_TAC std_ss [BIGUNION_UNION]
 THEN FULL_SIMP_TAC std_ss [SET_GSPEC]
 THEN SIMP_TAC std_ss [BIGUNION,IN_DEF]
 THEN SIMP_TAC std_ss [SET_GSPEC, ETA_CONV `` (\x. ReachableRec R s (SUC n') x)``]
 THEN PROVE_TAC [ReachableChain,SUBSET_UNION_ABSORPTION]]); 

val ReachableStableSubset = prove(``!R s n'.  (ReachableRec R s n' = ReachableRec R s (SUC n')) ==> (BIGUNION {P | ?n. n >= n' /\ (P = ReachableRec R s n)} SUBSET ReachableRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPECL [``(R :'a # 'a -> bool)``,``(s :'a->bool)``,``(n' :num)``] ReachableStable)
THEN UNDISCH_TAC ``ReachableRec R s n' = ReachableRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachableRec R s n' = ReachableRec R s (SUC n')) ==>
      !m. m >= n' ==> (ReachableRec R s m = ReachableRec R s n')``
THEN SPEC_TAC (``ReachableRec (R :'a # 'a -> bool) (s :'a->bool)``,``P:num->'a->bool``)
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,SUBSET_DEF]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN ASSUM_LIST PROVE_TAC);  

val ReachableLem1 = prove(``!R s n'. (ReachableRec R s n' = ReachableRec R s (SUC n')) ==>  
			  (ReachableRec R s n' UNION  BIGUNION {P | ?n. n >= n' /\ (P =ReachableRec R s n)} =  ReachableRec R s n')``,
REPEAT GEN_TAC
THEN ASSUME_TAC (SPEC_ALL ReachableStableSubset)
THEN UNDISCH_TAC ``(ReachableRec R s n' = ReachableRec R s (SUC n')) ==>
      BIGUNION {P | ?n. n >= n' /\ (P = ReachableRec R s n)} SUBSET
      ReachableRec R s n'``
THEN SPEC_TAC (``ReachableRec R s``,``P:num -> 'a -> bool``)
THEN REPEAT STRIP_TAC
THEN ONCE_REWRITE_TAC [UNION_COMM]
THEN ASSUM_LIST (fn t => PROVE_TAC (SUBSET_UNION_ABSORPTION::t)));

val ReachableLem2 = prove(``!R s n'. (ReachableRec R s n' = ReachableRec R s (SUC n')) ==> 
			  (BIGUNION {P | ?n. n <= n' /\ (P = ReachableRec R s n)} UNION 
			   BIGUNION {P | ?n. n >= n' /\ (P = ReachableRec R s n)} = 
			   ReachableRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (ReachableChainUnion::(tl t)))
THEN ASSUME_TAC (SPEC_ALL ReachableLem1)
THEN UNDISCH_TAC ``ReachableRec R s n' = ReachableRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachableRec R s n' = ReachableRec R s (SUC n')) ==>
      (ReachableRec R s n' UNION
       BIGUNION {P | ?n. n >= n' /\ (P = ReachableRec R s n)} =
       ReachableRec R s n')``
THEN SPEC_TAC (``ReachableRec R s``,``P:num -> 'a -> bool``)
THEN ASSUM_LIST PROVE_TAC);

val ReachableFP = save_thm("ReachableFP",prove(``!R s n'. (ReachableRec R s n' = ReachableRec R s (SUC n')) ==> (Reachable R s = ReachableRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPEC_ALL ReachableLem2)
THEN UNDISCH_TAC ``ReachableRec R s n' = ReachableRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachableRec R s n' = ReachableRec R s (SUC n')) ==>
      (BIGUNION {P | ?n. n <= n' /\ (P = ReachableRec R s n)} UNION
       BIGUNION {P | ?n. n >= n' /\ (P = ReachableRec R s n)} =
       ReachableRec R s n')``
THEN REWRITE_TAC [Reachable_def]
THEN SPEC_TAC (``ReachableRec R s``,``P:num -> 'a -> bool``)
THEN REWRITE_TAC [GSYM BIGUNION_SPLIT]
THEN ASSUM_LIST PROVE_TAC));

val _ = export_theory(); 


