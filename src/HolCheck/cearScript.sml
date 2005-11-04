open HolKernel Parse boolLib bossLib

val _ = new_theory("cear");

open envTheory
open pred_setTheory
open setLemmasTheory
open muSyntaxTheory
open muTheory
open ksTheory
open reachTheory

infix &&; infix 8 by;
val _ = intLib.deprecate_int();
fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end;

val Next_def = Define `Next R s s' = R(s,s')`;

val Prev_def = Define `Prev R s s' = R(s',s)`;

val ReachFromRec_def = Define `
    (ReachFromRec R s 0 = {s}) /\
    (ReachFromRec R s (SUC n) = {s' | s' IN ReachFromRec R s n \/ ?s''. Next R s'' s'  /\ s'' IN ReachFromRec R s n})`;

val ReachFrom_def = Define `ReachFrom R s = BIGUNION {P | ?n. P = ReachFromRec R s n}`;

val ReachToRec_def = Define `
    (ReachToRec R s 0 = {s}) /\
    (ReachToRec R s (SUC n) = {s' | s' IN ReachToRec R s n \/ ?s''. Prev R s'' s'  /\ s'' IN ReachToRec R s n})`;

val ReachTo_def = Define `ReachTo R s = BIGUNION {P | ?n. P = ReachToRec R s n}`;

val ReachFromChain = prove(``!R s n. ReachFromRec R s n SUBSET ReachFromRec R s (SUC n)``,
Induct_on `n` THENL [
SIMP_TAC std_ss [ReachFromRec_def,Next_def,SUBSET_DEF,IN_SING,SET_SPEC],
FULL_SIMP_TAC std_ss [ReachFromRec_def,Next_def,SUBSET_DEF,SET_SPEC]
]);

val ReachFromStable =prove(``!R s (n:num). (ReachFromRec R s n = ReachFromRec R s (SUC n)) ==>
			   !m. m >= n ==> (ReachFromRec R s m = ReachFromRec R s n)``,
REWRITE_TAC [DECIDE ``((m:num)>=n) = ((m=n) \/ (m>n))``]
THEN REPEAT STRIP_TAC THENL [
ASM_REWRITE_TAC [],
Induct_on `m` THENL [
 SIMP_TAC arith_ss [], (* 0 *)
 REWRITE_TAC [DECIDE ``(SUC m > n)=(m>=n)``]
 THEN REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
 THEN REPEAT STRIP_TAC THENL [

   FULL_SIMP_TAC std_ss [], (* m=n *)
   FULL_SIMP_TAC std_ss []
   THEN SIMP_TAC std_ss [ReachFromRec_def,Next_def,SET_SPEC]
   THEN ASM_REWRITE_TAC []]]]);

val ReachFromChainUnion = prove(``!R s n'. BIGUNION {P | ?n. n <= n' /\ (P = ReachFromRec R s n)} = ReachFromRec R s n'``,
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
 THEN SIMP_TAC std_ss [SET_GSPEC, ETA_CONV `` (\x. ReachFromRec R s (SUC n') x)``]
 THEN PROVE_TAC [ReachFromChain,SUBSET_UNION_ABSORPTION]]);

val ReachFromStableSubset = prove(``!R s n'.  (ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==> (BIGUNION {P | ?n. n >= n' /\ (P = ReachFromRec R s n)} SUBSET ReachFromRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPECL [``(R :'a # 'a -> bool)``,``(s :'a)``,``(n' :num)``] ReachFromStable)
THEN UNDISCH_TAC ``ReachFromRec R s n' = ReachFromRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==>
      !m. m >= n' ==> (ReachFromRec R s m = ReachFromRec R s n')``
THEN SPEC_TAC (``ReachFromRec (R :'a # 'a -> bool) (s :'a)``,``P:num->'a->bool``)
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,SUBSET_DEF]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN ASSUM_LIST PROVE_TAC);

val ReachFromLem1 = prove(``!R s n'. (ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==>
			  (ReachFromRec R s n' UNION  BIGUNION {P | ?n. n >= n' /\ (P =ReachFromRec R s n)} =  ReachFromRec R s n')``,
REPEAT GEN_TAC
THEN ASSUME_TAC (SPEC_ALL ReachFromStableSubset)
THEN UNDISCH_TAC ``(ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==>
      BIGUNION {P | ?n. n >= n' /\ (P = ReachFromRec R s n)} SUBSET
      ReachFromRec R s n'``
THEN SPEC_TAC (``ReachFromRec R s``,``P:num -> 'a -> bool``)
THEN REPEAT STRIP_TAC
THEN ONCE_REWRITE_TAC [UNION_COMM]
THEN ASSUM_LIST (fn t => PROVE_TAC (SUBSET_UNION_ABSORPTION::t)));

val ReachFromLem2 = prove(``!R s n'. (ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==>
			  (BIGUNION {P | ?n. n <= n' /\ (P = ReachFromRec R s n)} UNION
			   BIGUNION {P | ?n. n >= n' /\ (P = ReachFromRec R s n)} =
			   ReachFromRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (ReachFromChainUnion::(tl t)))
THEN ASSUME_TAC (SPEC_ALL ReachFromLem1)
THEN UNDISCH_TAC ``ReachFromRec R s n' = ReachFromRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==>
      (ReachFromRec R s n' UNION
       BIGUNION {P | ?n. n >= n' /\ (P = ReachFromRec R s n)} =
       ReachFromRec R s n')``
THEN SPEC_TAC (``ReachFromRec R s``,``P:num -> 'a -> bool``)
THEN ASSUM_LIST PROVE_TAC);

val ReachFromFP = save_thm("ReachFromFP",prove(``!R s n'. (ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==> (ReachFrom R s = ReachFromRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPEC_ALL ReachFromLem2)
THEN UNDISCH_TAC ``ReachFromRec R s n' = ReachFromRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachFromRec R s n' = ReachFromRec R s (SUC n')) ==>
      (BIGUNION {P | ?n. n <= n' /\ (P = ReachFromRec R s n)} UNION
       BIGUNION {P | ?n. n >= n' /\ (P = ReachFromRec R s n)} =
       ReachFromRec R s n')``
THEN REWRITE_TAC [ReachFrom_def]
THEN SPEC_TAC (``ReachFromRec R s``,``P:num -> 'a -> bool``)
THEN REWRITE_TAC [GSYM BIGUNION_SPLIT]
THEN ASSUM_LIST PROVE_TAC));

val ReachToChain = prove(``!R s n. ReachToRec R s n SUBSET ReachToRec R s (SUC n)``,
Induct_on `n` THENL [
SIMP_TAC std_ss [ReachToRec_def,Next_def,SUBSET_DEF,IN_SING,SET_SPEC],
FULL_SIMP_TAC std_ss [ReachToRec_def,Next_def,SUBSET_DEF,SET_SPEC]
]);

val ReachToStable =prove(``!R s n. (ReachToRec R s n = ReachToRec R s (SUC n)) ==>
			   !m. m >= n ==> (ReachToRec R s m = ReachToRec R s n)``,
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
   THEN SIMP_TAC std_ss [ReachToRec_def,Prev_def,SET_SPEC]
   THEN ASM_REWRITE_TAC []]]]);

val ReachToChainUnion = prove(``!R s n'. BIGUNION {P | ?n. n <= n' /\ (P = ReachToRec R s n)} = ReachToRec R s n'``,
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
 THEN SIMP_TAC std_ss [SET_GSPEC, ETA_CONV `` (\x. ReachToRec R s (SUC n') x)``]
 THEN PROVE_TAC [ReachToChain,SUBSET_UNION_ABSORPTION]]);

val ReachToStableSubset = prove(``!R s n'.  (ReachToRec R s n' = ReachToRec R s (SUC n')) ==> (BIGUNION {P | ?n. n >= n' /\ (P = ReachToRec R s n)} SUBSET ReachToRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPECL [``(R :'a # 'a -> bool)``,``(s :'a)``,``(n' :num)``] ReachToStable)
THEN UNDISCH_TAC ``ReachToRec R s n' = ReachToRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachToRec R s n' = ReachToRec R s (SUC n')) ==>
      !m. m >= n' ==> (ReachToRec R s m = ReachToRec R s n')``
THEN SPEC_TAC (``ReachToRec (R :'a # 'a -> bool) (s :'a)``,``P:num->'a->bool``)
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,SUBSET_DEF]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN ASSUM_LIST PROVE_TAC);

val ReachToLem1 = prove(``!R s n'. (ReachToRec R s n' = ReachToRec R s (SUC n')) ==>
			  (ReachToRec R s n' UNION  BIGUNION {P | ?n. n >= n' /\ (P =ReachToRec R s n)} =  ReachToRec R s n')``,
REPEAT GEN_TAC
THEN ASSUME_TAC (SPEC_ALL ReachToStableSubset)
THEN UNDISCH_TAC ``(ReachToRec R s n' = ReachToRec R s (SUC n')) ==>
      BIGUNION {P | ?n. n >= n' /\ (P = ReachToRec R s n)} SUBSET
      ReachToRec R s n'``
THEN SPEC_TAC (``ReachToRec R s``,``P:num -> 'a -> bool``)
THEN REPEAT STRIP_TAC
THEN ONCE_REWRITE_TAC [UNION_COMM]
THEN ASSUM_LIST (fn t => PROVE_TAC (SUBSET_UNION_ABSORPTION::t)));

val ReachToLem2 = prove(``!R s n'. (ReachToRec R s n' = ReachToRec R s (SUC n')) ==>
			  (BIGUNION {P | ?n. n <= n' /\ (P = ReachToRec R s n)} UNION
			   BIGUNION {P | ?n. n >= n' /\ (P = ReachToRec R s n)} =
			   ReachToRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (ReachToChainUnion::(tl t)))
THEN ASSUME_TAC (SPEC_ALL ReachToLem1)
THEN UNDISCH_TAC ``ReachToRec R s n' = ReachToRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachToRec R s n' = ReachToRec R s (SUC n')) ==>
      (ReachToRec R s n' UNION
       BIGUNION {P | ?n. n >= n' /\ (P = ReachToRec R s n)} =
       ReachToRec R s n')``
THEN SPEC_TAC (``ReachToRec R s``,``P:num -> 'a -> bool``)
THEN ASSUM_LIST PROVE_TAC);

val ReachToFP = save_thm("ReachToFP",prove(``!R s n'. (ReachToRec R s n' = ReachToRec R s (SUC n')) ==> (ReachTo R s = ReachToRec R s n')``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPEC_ALL ReachToLem2)
THEN UNDISCH_TAC ``ReachToRec R s n' = ReachToRec R s (SUC n')``
THEN UNDISCH_TAC ``(ReachToRec R s n' = ReachToRec R s (SUC n')) ==>
      (BIGUNION {P | ?n. n <= n' /\ (P = ReachToRec R s n)} UNION
       BIGUNION {P | ?n. n >= n' /\ (P = ReachToRec R s n)} =
       ReachToRec R s n')``
THEN REWRITE_TAC [ReachTo_def]
THEN SPEC_TAC (``ReachToRec R s``,``P:num -> 'a -> bool``)
THEN REWRITE_TAC [GSYM BIGUNION_SPLIT]
THEN ASSUM_LIST PROVE_TAC));

val R_REFL_def = Define `R_REFL R = !x. R(x,x)`;
val R_SYM_def = Define `R_SYM R = !x y. R(x,y) = R(y,x)`;
val R_TRANS_def = Define `R_TRANS R = !x y z. R(x,y) /\ R(y,z) ==> R(x,z)`;
val R_EQR_def = Define `R_EQR R = R_REFL R /\ R_SYM R /\ R_TRANS R`;

val ReachToClosed = save_thm("ReachToClosed",prove(``!si R s. R_EQR R ==> (s IN ReachTo R si = R(s,si))``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,ReachTo_def,SET_SPEC]
THEN EQ_TAC THENL [
REPEAT STRIP_TAC
THEN `s IN ReachToRec R si n` by ASSUM_LIST PROVE_TAC
THEN POP_ASSUM_LIST (fn l => ASSUME_TAC (List.hd l) THEN ASSUME_TAC (List.last l))
THEN (SUBGOAL_THEN ``!n (s:'a). s IN ReachToRec R si n ==> R(s,si)`` ASSUME_TAC) THENL [
  PAT_ASSUM ``s IN t`` (fn _ => ALL_TAC)
  THEN Induct_on `n` THENL [
    FULL_SIMP_TAC std_ss [ReachToRec_def,IN_SING,R_EQR_def,R_REFL_def], (* 0 *)
    FULL_SIMP_TAC std_ss [ReachToRec_def,SET_SPEC]
    THEN RW_TAC std_ss [] THEN RES_TAC
    THEN PAT_ASSUM ``!x. t`` (fn t => ASSUME_TAC (SPEC ``s'':'a`` t))
    THEN FULL_SIMP_TAC std_ss [Prev_def,R_EQR_def,R_TRANS_def]
    THEN ASSUM_LIST PROVE_TAC
  ],
  ASSUM_LIST PROVE_TAC
 ], (* ==> *)
DISCH_TAC
THEN EXISTS_TAC ``ReachToRec (R:'a#'a->bool) si (SUC 0)``
THEN CONJ_TAC THENL [
 EXISTS_TAC ``SUC 0`` THEN REFL_TAC,
 SIMP_TAC std_ss [ReachToRec_def,SET_SPEC,Prev_def]
 THEN DISJ2_TAC
 THEN EXISTS_TAC ``si:'a``
 THEN FULL_SIMP_TAC std_ss [IN_SING]
 ]
]));

val ReachFromClosed = save_thm("ReachFromClosed",prove(``!si R s. R_EQR R ==> (s IN ReachFrom R si = R(si,s))``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,ReachFrom_def,SET_SPEC]
THEN EQ_TAC THENL [
REPEAT STRIP_TAC
THEN `s IN ReachFromRec R si n` by ASSUM_LIST PROVE_TAC
THEN POP_ASSUM_LIST (fn l => ASSUME_TAC (List.hd l) THEN ASSUME_TAC (List.last l))
THEN (SUBGOAL_THEN ``!n (s:'a). s IN ReachFromRec R si n ==> R(si,s)`` ASSUME_TAC) THENL [
  PAT_ASSUM ``s IN t`` (fn _ => ALL_TAC)
  THEN Induct_on `n` THENL [
    FULL_SIMP_TAC std_ss [ReachFromRec_def,IN_SING,R_EQR_def,R_REFL_def], (* 0 *)
    FULL_SIMP_TAC std_ss [ReachFromRec_def,SET_SPEC]
    THEN RW_TAC std_ss [] THEN RES_TAC
    THEN PAT_ASSUM ``!x. t`` (fn t => ASSUME_TAC (SPEC ``s'':'a`` t))
    THEN FULL_SIMP_TAC std_ss [Next_def,R_EQR_def,R_TRANS_def]
    THEN ASSUM_LIST PROVE_TAC
  ],
  ASSUM_LIST PROVE_TAC
 ], (* ==> *)
DISCH_TAC
THEN EXISTS_TAC ``ReachFromRec (R:'a#'a->bool) si (SUC 0)``
THEN CONJ_TAC THENL [
 EXISTS_TAC ``SUC 0`` THEN REFL_TAC,
 SIMP_TAC std_ss [ReachFromRec_def,SET_SPEC,Next_def]
 THEN DISJ2_TAC
 THEN EXISTS_TAC ``si:'a``
 THEN FULL_SIMP_TAC std_ss [IN_SING]
 ]
]));

val SCC_def =  save_thm("SCC_def",Define `SCC R s = ReachFrom R s UNION ReachTo R s`);

(* At the moment am not defining the ap field since we don't know that simply by looking at the formal M *)
(* TODO: since aks.ap is simply the set of abstract state variables, we could pass it in to ABS_KS_def *)
(* this is possible since the online abs ks would have been created before we use the definition below *)
val ABS_KS_def =  save_thm("ABS_KS_def",Define `ABS_KS M (h:('a#'b)->bool) =
                                       <| S := UNIV:'b->bool;
                                          S0:= { sh | ?s'. (s' IN M.S0) /\ h(s',sh)};
					  T := \a. \(sh,sh'). ?s' s''. (M.T a)(s',s'') /\ h(s',sh) /\ h(s'',sh');
					  L:= \sh. BIGUNION { X | ?s.  (X = (M.L s)) /\ h(s,sh)}
					|>`);


val wf_absKS = save_thm("wf_absKS",prove(``!ks h. wfKS ks ==> wfKS (ABS_KS ks h)``,
FULL_SIMP_TAC std_ss [wfKS_def,ABS_KS_def,KS_accfupds,combinTheory.K_DEF,SUBSET_UNIV]));

val def1 = Define `QP2 h q q' = h(q,q')`;
val def2 = Define `QP3(h,q) q' = QP2 h q q'`;

val lem1 = prove(``!h q. h(q,@qh. h(q,qh)) = ?qh. h(q,qh)``,
 REWRITE_TAC [GSYM def1]
 THEN SPEC_TAC(``QP2 (h :'a # 'b -> bool) (q :'a)``,``Q:'b->bool``)
 THEN  REWRITE_TAC [SELECT_THM]);

val ABS_CONS_LEM = save_thm("ABS_CONS_LEM",prove(``!(f:'prop mu) h (ks:('prop,'state) KS) s sh (e:string -> 'state -> bool) (eh:string -> 'astate -> bool).
wfKS ks ==>
(!Q. ~SUBFORMULA (~RV Q) (NNF f)) ==>
(!s. ?sh. h(s,sh)) ==>
(!a g. ~SUBFORMULA (<<a>> g) (NNF f)) ==>
(!p. SUBFORMULA (AP p) f ==> p IN ks.ap) ==>
(!s1 s2 sh. h(s1,sh) /\ h(s2,sh) ==> !p. p IN ks.ap ==> (s1 IN STATES (AP p) ks e = s2 IN STATES (AP p) ks e)) ==>
(!Q s sh. h(s,sh) ==> (sh IN eh Q ==> s IN e Q)) ==>
h(s,sh) ==>
sh IN STATES (NNF f) (ABS_KS ks h) eh ==> s IN STATES (NNF f) ks e``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THENL [
SIMP_TAC std_ss [STATES_def,NNF_def,IN_UNIV,wfKS_def,wf_absKS], (* T *)
SIMP_TAC std_ss [STATES_def,NNF_def,NOT_IN_EMPTY,wfKS_def], (* F *)
RW_TAC std_ss [NNF_def,STATES_def,INTER_DEF,SET_SPEC,MU_SUB_def]
THEN FULL_SIMP_TAC std_ss [SUB_AP_CONJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN RES_TAC
THEN ASM_REWRITE_TAC [], (* /\ *)
RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,MU_SUB_def]
THEN FULL_SIMP_TAC std_ss [UNION_DEF,SET_SPEC,SUB_AP_DISJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN RES_TAC
THEN ASM_REWRITE_TAC [], (* \/ *)
RW_TAC std_ss [MU_SUB_def,NNF_def,STATES_def,SET_SPEC] THENL [
 FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV],
 FULL_SIMP_TAC std_ss [ABS_KS_def,KS_accfupds,combinTheory.K_DEF,IN_UNIV,BIGUNION]
 THEN WEAKEN_TAC (fn t => Term.compare(t,T)=EQUAL)
 THEN FULL_SIMP_TAC std_ss [SET_SPEC]
 THEN POP_ASSUM (fn t => PAT_ASSUM ``p' = ks.L s'`` (fn t' => ASSUME_TAC (REWRITE_RULE [t'] t)))
 THEN ASSUM_LIST (fn t => PROVE_TAC (wfKS_def::IN_UNIV::t))
], (* AP *)
RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,IN_UNIV,NOT_IN_EMPTY,DIFF_DEF,wfKS_def]
THEN ASSUM_LIST (fn t => PROVE_TAC [IN_DEF]), (* RV *)
RW_TAC std_ss [NNF_def,SUB_DMD_DMD], (* <> *)
RW_TAC std_ss []
THEN FULL_SIMP_TAC std_ss [NNF_def,SUB_DMD_BOX,SUB_AP_BOX,SUB_RV_BOX,STATES_def,SET_SPEC,IN_UNIV,wfKS_def,
		      REWRITE_RULE [wfKS_def] wf_absKS]
THEN POP_ASSUM MP_TAC
THEN ASSUM_LIST (fn l => SIMP_TAC std_ss (l@[REWRITE_RULE [wfKS_def] wf_absKS,IN_UNIV]))
THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
			 QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
THEN REPEAT STRIP_TAC
THEN PAT_ASSUM ``!q. (ABS_KS ks h).T a (sh,q) ==> q IN STATES (NNF f) (ABS_KS ks h) eh`` (fn t => ASSUME_TAC (CONV_RULE (QUANT_CONV (RATOR_CONV(RAND_CONV(SIMP_CONV std_ss [ABS_KS_def,KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF])))) t))
THEN PAT_ASSUM ``!s1 s2 sh'. h (s1,sh') /\ h (s2,sh') ==> !p. p IN ks.ap ==> (s1 IN ks.S /\ p IN ks.L s1 = s2 IN ks.S /\ p IN ks.L s2)``
    (fn t => PAT_ASSUM ``ks.S = UNIV`` (fn t' => ASSUME_TAC t' THEN ASSUME_TAC (SIMP_RULE std_ss [IN_UNIV,t'] t)))
THEN PAT_ASSUM ``!s. ?sh. h (s,sh)`` (fn t => ASSUME_TAC t THEN ASSUME_TAC (Q.SPEC `q` t))
THEN NTAC 6 (POP_ASSUM MP_TAC) THEN POP_ASSUM (fn t => REPEAT DISCH_TAC THEN RES_TAC THEN ASSUME_TAC t)
THEN NTAC 2 (POP_ASSUM MP_TAC) THEN NTAC 2 (POP_ASSUM (fn _ => ALL_TAC)) THEN REPEAT DISCH_TAC
THEN PAT_ASSUM ``!a b c d e g. t`` (fn t => ALL_TAC)
THEN POP_ASSUM (fn t => POP_ASSUM (fn t' => ASSUME_TAC t THEN ASSUME_TAC (SPEC ``q:'state``  (SPEC ``@qh. h((q:'state),(qh:'astate))`` t'))))
THEN PAT_ASSUM ``!q. (?s' s''. ks.T a (s',s'') /\ h (s',sh) /\ h (s'',q)) ==>
            q IN STATES (NNF f) (ABS_KS ks h) eh`` (fn t =>  ASSUME_TAC (SPEC ``@qh. h((q:'state),(qh:'astate))`` t))
THEN (SUBGOAL_THEN ``(?(s':'state) s''. (ks:('prop,'state) KS).T a (s',s'') /\ h (s',(sh:'astate)) /\ h (s'',@qh. h (q,qh)))`` ASSUME_TAC) THENL [
 MAP_EVERY Q.EXISTS_TAC [`s:'state`,`q:'state`]
 THEN ASM_REWRITE_TAC [lem1],
 ASSUM_LIST metisLib.METIS_TAC
], (* [] *)
SIMP_TAC std_ss [FV_def,STATES_def,NNF_def,SET_SPEC]
THEN NTAC 17 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_MU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_MU,SUB_AP_MU,SUB_RV_MU]
THEN RES_TAC
THEN POP_ASSUM (fn t => NTAC 5 (POP_ASSUM (fn _ => ALL_TAC)) THEN ASSUME_TAC t)
THEN (SUBGOAL_THEN (mk_forall(``n:num``,list_mk_forall([``sh:'astate``,``s:'state``],mk_imp(``(h :'state # 'astate -> bool)(s,sh)``,mk_imp(``(sh:'astate) IN FP (NNF f) Q (ABS_KS (ks:('prop,'state) KS) h) eh[[[Q<--{}]]] n``,``s IN FP (NNF f) Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n``))))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  SIMP_TAC std_ss [STATES_def,ENV_EVAL,NOT_IN_EMPTY],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF f) Q (ABS_KS (ks:('prop,'state) KS) (h :'state # 'astate -> bool)) eh[[[Q<--{}]]] n``,``X:'astate -> bool``)
  THEN SPEC_TAC (``FP (NNF f) Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n``,``Y:'state->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN (SUBGOAL_THEN ``!e eh sh s. (!Q s (sh:'astate). (h:'state # 'astate -> bool)(s,sh) ==> (sh IN eh Q ==> s IN e Q)) ==> h(s,sh) ==> sh IN STATES (NNF f) (ABS_KS (ks:('prop,'state) KS) h) eh ==> s IN STATES (NNF f) (ks:('prop,'state) KS) e`` ASSUME_TAC) THENL [
   NTAC 3 (POP_ASSUM (fn _ => ALL_TAC))
   THEN PAT_ASSUM ``!Q s sh.  h (s,sh) ==> (sh IN eh Q ==> s IN e Q)`` (fn _ => ALL_TAC)
   THEN PAT_ASSUM ``h (s,sh)`` (fn _ => ALL_TAC)
   THEN RES_TAC
   THEN RW_TAC std_ss []
   THEN POP_ASSUM_LIST (fn t => PROVE_TAC (List.take(t,4))),
   POP_ASSUM (fn t => ASSUME_TAC (SPECL [``(e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]]``,``(eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]``] t))
   THEN (SUBGOAL_THEN``(!(Q' :string) (s :'state) (sh :'astate). (h:'state # 'astate -> bool)(s,sh) ==> (sh IN (eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]
			 Q' ==> s IN (e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]] Q'))`` ASSUME_TAC) THENL [
    PAT_ASSUM ``!sh s.  h (s,sh) ==> sh IN X ==> s IN Y`` (fn t => PAT_ASSUM ``!Q s sh. h (s,sh) ==> (sh IN eh Q ==> s IN e Q)``
							(fn t'=> POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN Cases_on `Q=Q'` THENL [
     FULL_SIMP_TAC std_ss [ENV_EVAL] THEN ASSUM_LIST PROVE_TAC,
     FULL_SIMP_TAC std_ss [ENV_UPDATE_INV] THEN ASSUM_LIST PROVE_TAC
     ],
    POP_ASSUM (fn t => POP_ASSUM (fn t' => POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN  POP_ASSUM (fn t => ASSUME_TAC (SPECL [``sh':'astate``,``s':'state``] t))
    THEN ASSUM_LIST PROVE_TAC
    ]
   ]
  ],
  RES_TAC
  THEN NTAC 5 (POP_ASSUM (fn _ => ALL_TAC))
  THEN POP_ASSUM (fn t => POP_ASSUM_LIST (fn _ => ASSUME_TAC t))
  THEN ASSUM_LIST PROVE_TAC
 ], (* mu *)
SIMP_TAC std_ss [STATES_def,NNF_def,SET_SPEC]
THEN NTAC 17 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_MU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_NU,SUB_AP_NU,SUB_RV_NU]
THEN RES_TAC
THEN POP_ASSUM (fn t => NTAC 5 (POP_ASSUM (fn _ => ALL_TAC)) THEN ASSUME_TAC t)
THEN (SUBGOAL_THEN (mk_forall(``n:num``,list_mk_forall([``sh:'astate``,``s:'state``],mk_imp(``(h :'state # 'astate -> bool)(s,sh)``,mk_imp(``sh IN FP (NNF f) Q (ABS_KS (ks:('prop,'state) KS) h) eh[[[Q<--(ABS_KS (ks:('prop,'state) KS) (h:'state # 'astate -> bool)).S]]] n``,``s IN FP (NNF f) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n``))))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,wfKS_def,wf_absKS,IN_UNIV],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF f) Q (ABS_KS (ks:('prop,'state) KS) (h :'state # 'astate -> bool)) eh[[[Q<--(ABS_KS (ks:('prop,'state) KS) h).S]]] n``,``X:'astate -> bool``)
  THEN SPEC_TAC (``FP (NNF f) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n``,``Y:'state->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN (SUBGOAL_THEN ``!e eh sh s. (!Q s (sh:'astate). (h:'state # 'astate -> bool)(s,sh) ==> (sh IN eh Q ==> s IN e Q)) ==> h(s,sh) ==> sh IN STATES (NNF f) (ABS_KS ks h) eh ==> s IN STATES (NNF f) (ks:('prop,'state) KS) e`` ASSUME_TAC) THENL [
   NTAC 2 (POP_ASSUM (fn _ => ALL_TAC))
   THEN PAT_ASSUM ``!Q s sh.  h (s,sh) ==> sh IN eh Q ==> s IN e Q`` (fn _ => ALL_TAC)
   THEN PAT_ASSUM ``h (s,sh)`` (fn _ => ALL_TAC)
   THEN RES_TAC
   THEN RW_TAC std_ss []
   THEN POP_ASSUM_LIST (fn t => PROVE_TAC (List.take(t,4))),
   POP_ASSUM (fn t => ASSUME_TAC (SPECL [``(e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]]``,``(eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]``] t))
   THEN (SUBGOAL_THEN``(!(Q' :string) (s :'state) (sh :'astate). (h:'state # 'astate -> bool)(s,sh) ==> sh IN (eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]
			 Q' ==> s IN (e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]] Q')`` ASSUME_TAC) THENL [
    PAT_ASSUM ``!sh s.  h (s,sh) ==> sh IN X ==> s IN Y`` (fn t => PAT_ASSUM ``!Q s sh. h (s,sh) ==> sh IN eh Q ==> s IN e Q``
							(fn t'=> POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN Cases_on `Q=Q'` THENL [
     FULL_SIMP_TAC std_ss [ENV_EVAL] THEN ASSUM_LIST PROVE_TAC,
     FULL_SIMP_TAC std_ss [ENV_UPDATE_INV] THEN ASSUM_LIST PROVE_TAC
     ],
    POP_ASSUM (fn t => POP_ASSUM (fn t' => POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN  POP_ASSUM (fn t => ASSUME_TAC (SPECL [``sh':'astate``,``s':'state``] t))
    THEN ASSUM_LIST PROVE_TAC
    ]
   ]
  ],
  RES_TAC
  THEN NTAC 5 (POP_ASSUM (fn _ => ALL_TAC))
  THEN POP_ASSUM (fn t => POP_ASSUM_LIST (fn _ => ASSUME_TAC t))
  THEN ASSUM_LIST PROVE_TAC
 ], (* nu *)
SIMP_TAC std_ss [STATES_def,NNF_def,NOT_IN_EMPTY,wfKS_def], (* ~T *)
SIMP_TAC std_ss [STATES_def,NNF_def,IN_UNIV,wfKS_def,wf_absKS], (* ~F *)
RW_TAC std_ss [NNF_def,STATES_def,UNION_DEF,SET_SPEC,MU_SUB_def]
THEN FULL_SIMP_TAC std_ss [SUB_AP_DISJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN RES_TAC
THEN ASM_REWRITE_TAC [], (* ~/\*)
RW_TAC std_ss [NNF_def,STATES_def,INTER_DEF,SET_SPEC,MU_SUB_def]
THEN FULL_SIMP_TAC std_ss [SUB_AP_CONJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN RES_TAC
THEN ASM_REWRITE_TAC [], (* ~\/ *)
FULL_SIMP_TAC std_ss [MU_SUB_def,NNF_def,DIFF_DEF,STATES_def,SET_SPEC]
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV]
THEN FULL_SIMP_TAC std_ss [ABS_KS_def,KS_accfupds,combinTheory.K_DEF,IN_UNIV,BIGUNION]
THEN WEAKEN_TAC (fn t => Term.compare(t,T)=EQUAL)
THEN FULL_SIMP_TAC std_ss [SET_SPEC]
THEN POP_ASSUM (fn t => ASSUME_TAC (SPEC ``(ks:('prop,'state) KS).L (s:'state)`` t))
THEN FULL_SIMP_TAC std_ss []
THEN POP_ASSUM (fn t => ASSUME_TAC (SPEC ``s:'state`` t))
THEN FULL_SIMP_TAC std_ss [], (* ~AP *)
RW_TAC std_ss [NNF_def,MU_SUB_def], (* ~RV *)
FULL_SIMP_TAC std_ss [NNF_def,SUB_DMD_BOX,SUB_AP_NEG_DMD,SUB_RV_BOX,STATES_def,SET_SPEC,IN_UNIV,wfKS_def,REWRITE_RULE [wfKS_def] wf_absKS]
THEN NTAC 17 STRIP_TAC
THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
			 QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
THEN REPEAT STRIP_TAC
THEN PAT_ASSUM ``!q. (ABS_KS ks h).T a (sh,q) ==> q IN STATES (NNF f) (ABS_KS ks h) eh`` (fn t => ASSUME_TAC (CONV_RULE (QUANT_CONV (RATOR_CONV(RAND_CONV(SIMP_CONV std_ss [ABS_KS_def,KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF])))) t))
THEN POP_ASSUM (fn t => POP_ASSUM (fn t' => POP_ASSUM (fn t'' => ASSUME_TAC t THEN ASSUME_TAC t' THEN RES_TAC THEN ASSUME_TAC t'')))
THEN POP_ASSUM (fn t => POP_ASSUM (fn t' => NTAC 2 (POP_ASSUM (fn _ => ALL_TAC)) THEN ASSUME_TAC t THEN ASSUME_TAC t'))
THEN PAT_ASSUM ``!a b c d e g. t`` (fn t => ALL_TAC)
THEN POP_ASSUM (fn t => ASSUME_TAC (SPEC ``q:'state`` (SPEC ``@qh. h((q:'state),(qh:'astate))`` t)))
THEN POP_ASSUM (fn t => POP_ASSUM (fn t' => POP_ASSUM (fn t''' => POP_ASSUM (fn t'' => ASSUME_TAC t THEN ASSUME_TAC t' THEN ASSUME_TAC t''' THEN ASSUME_TAC (SPEC ``@qh. h((q:'state),(qh:'astate))`` t'')))))
THEN (SUBGOAL_THEN ``(?(s':'state) s''. (ks:('prop,'state) KS).T a (s',s'') /\ h (s',(sh:'astate)) /\ h (s'',@qh. h (q,qh)))`` ASSUME_TAC) THENL [
 MAP_EVERY EXISTS_TAC [``s:'state``,``q:'state``]
 THEN ASM_REWRITE_TAC [lem1],
 ASSUM_LIST metisLib.METIS_TAC
], (* ~<> *)
SIMP_TAC std_ss [NNF_def,SUB_DMD_DMD], (* ~[] *)
SIMP_TAC std_ss [NNF_def,SUB_AP_NEG_NEG], (* ~~ *)
SIMP_TAC std_ss [STATES_def,NNF_def,SET_SPEC]
THEN NTAC 17 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_MU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_NU,SUB_AP_NEG_MU,SUB_RV_NU]
THEN RES_TAC
THEN POP_ASSUM (fn t => NTAC 5 (POP_ASSUM (fn _ => ALL_TAC)) THEN ASSUME_TAC t)
THEN (SUBGOAL_THEN (mk_forall(``n:num``,list_mk_forall([``sh:'astate``,``s:'state``],mk_imp(``(h :'state # 'astate -> bool)(s,sh)``,mk_imp(``sh IN FP (NNF (RVNEG Q ~f)) Q (ABS_KS (ks:('prop,'state) KS) (h :'state # 'astate -> bool)) eh[[[Q<--(ABS_KS (ks:('prop,'state) KS) h).S]]] n``,``s IN FP (NNF (RVNEG Q ~f)) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n``))))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,wfKS_def,wf_absKS,IN_UNIV],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ABS_KS (ks:('prop,'state) KS) (h :'state # 'astate -> bool) ) eh[[[Q<--(ABS_KS (ks:('prop,'state) KS) h).S]]] n``,``X:'astate -> bool``)
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n``,``Y:'state->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN (SUBGOAL_THEN ``!e eh sh s. (!Q s (sh:'astate). (h :'state # 'astate -> bool)(s,sh) ==> (sh IN eh Q ==> s IN e Q)) ==> h(s,sh) ==> sh IN STATES (NNF (RVNEG Q ~f)) (ABS_KS ks h) eh ==> s IN STATES (NNF (RVNEG Q ~f)) (ks:('prop,'state) KS) e`` ASSUME_TAC) THENL [
   NTAC 2 (POP_ASSUM (fn _ => ALL_TAC))
   THEN PAT_ASSUM ``!Q s sh.  h (s,sh) ==> sh IN eh Q ==> s IN e Q`` (fn _ => ALL_TAC)
   THEN PAT_ASSUM ``h (s,sh)`` (fn _ => ALL_TAC)
   THEN RES_TAC
   THEN RW_TAC std_ss []
   THEN POP_ASSUM_LIST (fn t => PROVE_TAC (List.take(t,4))),
   POP_ASSUM (fn t => ASSUME_TAC (SPECL [``(e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]]``,``(eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]``] t))
   THEN (SUBGOAL_THEN``(!(Q' :string) (s :'state) (sh :'astate). (h :'state # 'astate -> bool)(s,sh) ==> sh IN (eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]
			 Q' ==> s IN (e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]] Q')`` ASSUME_TAC) THENL [
    PAT_ASSUM ``!sh s.  h (s,sh) ==> sh IN X ==> s IN Y`` (fn t => PAT_ASSUM ``!Q s sh. h (s,sh) ==> sh IN eh Q ==> s IN e Q``
							(fn t'=> POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN Cases_on `Q=Q'` THENL [
     FULL_SIMP_TAC std_ss [ENV_EVAL] THEN ASSUM_LIST PROVE_TAC,
     FULL_SIMP_TAC std_ss [ENV_UPDATE_INV] THEN ASSUM_LIST PROVE_TAC
     ],
    POP_ASSUM (fn t => POP_ASSUM (fn t' => POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN  POP_ASSUM (fn t => ASSUME_TAC (SPECL [``sh':'astate``,``s':'state``] t))
    THEN ASSUM_LIST PROVE_TAC
    ]
   ]
  ],
  RES_TAC
  THEN NTAC 5 (POP_ASSUM (fn _ => ALL_TAC))
  THEN POP_ASSUM (fn t => POP_ASSUM_LIST (fn _ => ASSUME_TAC t))
  THEN ASSUM_LIST PROVE_TAC
 ], (* ~mu *)
SIMP_TAC std_ss [FV_def,STATES_def,NNF_def,SET_SPEC]
THEN NTAC 17 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_MU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_MU,SUB_AP_NEG_NU,SUB_RV_MU]
THEN RES_TAC
THEN POP_ASSUM (fn t => NTAC 5 (POP_ASSUM (fn _ => ALL_TAC)) THEN ASSUME_TAC t)
THEN (SUBGOAL_THEN (mk_forall(``n:num``,list_mk_forall([``sh:'astate``,``s:'state``],mk_imp(``(h :'state # 'astate -> bool)(s,sh)``,mk_imp(``sh IN FP (NNF (RVNEG Q ~f)) Q (ABS_KS (ks:('prop,'state) KS) (h :'state # 'astate -> bool)) eh[[[Q<--{}]]] n``,``s IN FP (NNF (RVNEG Q ~f)) Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n``))))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  SIMP_TAC std_ss [STATES_def,ENV_EVAL,NOT_IN_EMPTY],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ABS_KS (ks:('prop,'state) KS) (h :'state # 'astate -> bool)) eh[[[Q<--{}]]] n``,``X:'astate -> bool``)
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n``,``Y:'state->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN (SUBGOAL_THEN ``!e eh sh s. (!Q s (sh:'astate). (h :'state # 'astate -> bool)(s,sh) ==> (sh IN eh Q ==> s IN e Q)) ==> h(s,sh) ==> sh IN STATES (NNF (RVNEG Q ~f)) (ABS_KS ks h) eh ==> s IN STATES (NNF(RVNEG Q ~f) ) (ks:('prop,'state) KS) e`` ASSUME_TAC) THENL [
   PAT_ASSUM ``!Q s sh.  h (s,sh) ==> (sh IN eh Q ==> s IN e Q)`` (fn _ => ALL_TAC)
   THEN PAT_ASSUM ``h (s,sh)`` (fn _ => ALL_TAC)
   THEN RES_TAC
   THEN RW_TAC std_ss []
   THEN POP_ASSUM_LIST (fn t => PROVE_TAC (List.take(t,4))),
   POP_ASSUM (fn t => ASSUME_TAC (SPECL [``(e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]]``,``(eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]``] t))
   THEN (SUBGOAL_THEN``(!(Q' :string) (s :'state) (sh :'astate). (h :'state # 'astate -> bool)(s,sh) ==> (sh IN (eh :string -> 'astate -> bool)[[[(Q :string)<--(X :'astate -> bool)]]]
			 Q' ==> s IN (e :string -> 'state -> bool)[[[Q<--(Y :'state -> bool)]]] Q'))`` ASSUME_TAC) THENL [
    PAT_ASSUM ``!sh s.  h (s,sh) ==> sh IN X ==> s IN Y`` (fn t => PAT_ASSUM ``!Q s sh. h (s,sh) ==> (sh IN eh Q ==> s IN e Q)``
							(fn t'=> POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN Cases_on `Q=Q'` THENL [
     FULL_SIMP_TAC std_ss [ENV_EVAL] THEN ASSUM_LIST PROVE_TAC,
     FULL_SIMP_TAC std_ss [ENV_UPDATE_INV] THEN ASSUM_LIST PROVE_TAC
     ],
    POP_ASSUM (fn t => POP_ASSUM (fn t' => POP_ASSUM_LIST (fn _ => ASSUME_TAC t THEN ASSUME_TAC t')))
    THEN REPEAT GEN_TAC
    THEN  POP_ASSUM (fn t => ASSUME_TAC (SPECL [``sh':'astate``,``s':'state``] t))
    THEN ASSUM_LIST PROVE_TAC
    ]
   ]
  ],
  RES_TAC
  THEN NTAC 5 (POP_ASSUM (fn _ => ALL_TAC))
  THEN POP_ASSUM (fn t => POP_ASSUM_LIST (fn _ => ASSUME_TAC t))
  THEN ASSUM_LIST PROVE_TAC
 ] (* ~nu *)
]));


val ABS_CONS_STATES = save_thm("ABS_CONS_STATES",SIMP_RULE std_ss [wf_absKS,STATES_NNF_ID] ABS_CONS_LEM);

val ABS_INIT = save_thm("ABS_INIT",prove(``!ks h s sh. h(s,sh) ==> s IN ks.S0 ==> sh IN (ABS_KS ks h).S0``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [ABS_KS_def,ksTheory.KS_accfupds,combinTheory.K_DEF,SET_SPEC]
THEN Q.EXISTS_TAC `s`
THEN ASM_REWRITE_TAC []));

(* note <== direction is not provable because h may make unreachable s reachable *)
val ABS_REACH = save_thm("ABS_REACH",prove(``!ks h a s sh. (!s. ?sh. h(s,sh)) ==> h(s,sh) ==> s IN Reachable (ks.T a) ks.S0 ==> sh IN Reachable ((ABS_KS ks h).T a) ((ABS_KS ks h).S0)``,
NTAC 7 STRIP_TAC
THEN SIMP_TAC std_ss [Reachable_def,BIGUNION,SET_SPEC]
THEN STRIP_TAC
THEN POP_ASSUM (fn t => POP_ASSUM (fn t' => ASSUME_TAC (REWRITE_RULE [t'] t)))
THEN Q.EXISTS_TAC `ReachableRec ((ABS_KS ks h).T a) ((ABS_KS ks h).S0) n`
THEN CONJ_TAC THENL [
 Q.EXISTS_TAC `n` THEN REFL_TAC,
 POP_ASSUM_LIST (MAP_EVERY MP_TAC)
 THEN STRIP_TAC
 THEN MAP_EVERY Q.SPEC_TAC [(`s`,`s`),(`sh`,`sh`)]
 THEN Induct_on `n` THENL [
  SIMP_TAC std_ss [ReachableRec_def,ABS_KS_def,ksTheory.KS_accfupds,combinTheory.K_DEF,SET_SPEC]
  THEN RW_TAC std_ss []
  THEN Q.EXISTS_TAC `s`
  THEN ASM_REWRITE_TAC [],
  SIMP_TAC std_ss [ReachableRec_def,SET_SPEC]
  THEN RW_TAC std_ss [] THENL [
   DISJ1_TAC THEN RES_TAC,
   DISJ2_TAC
   THEN FULL_SIMP_TAC std_ss [ReachNext_def]
   THEN CONV_TAC (QUANT_CONV (LAND_CONV (SIMP_CONV std_ss [ABS_KS_def,ksTheory.KS_accfupds,combinTheory.K_DEF])))
   THEN Q.PAT_ASSUM `!s. ?sh. h (s,sh)` (fn t => ASSUME_TAC t THEN ASSUME_TAC (Q.SPEC `s''` t))
   THEN FULL_SIMP_TAC std_ss []
   THEN Q.EXISTS_TAC `@xh. h(s'',xh)`
   THEN RW_TAC std_ss [] THENL [
    SELECT_ELIM_TAC
    THEN RW_TAC std_ss []
    THEN MAP_EVERY Q.EXISTS_TAC [`s''`,`s`]
    THEN ASM_REWRITE_TAC [],
    SELECT_ELIM_TAC
    THEN RW_TAC std_ss []
    THEN RES_TAC
   ]
  ]
 ]
]));

val IS_ABS_FUN_def = Define `IS_ABS_FUN (ks:('prop,'state) KS) e h = (!s. ?(sh:'astate). h(s,sh)) /\ (!s1 s2 (sh:'astate). h(s1,sh) /\ h(s2,sh) ==> !p. p IN ks.ap ==> (s1 IN STATES (AP p) ks e = s2 IN STATES (AP p) ks e))`;

val ABS_CONS_MODEL = save_thm("ABS_CONS_MODEL",prove(``!f h (ks:('prop,'state) KS) (e:string -> 'state -> bool) (eh:string -> 'astate -> bool). wfKS ks ==> (!Q. ~SUBFORMULA (~RV Q) (NNF f)) ==> (!a g. ~SUBFORMULA (<<a>> g) (NNF f)) ==> (!p. SUBFORMULA (AP p) f ==> p IN ks.ap) ==> IS_ABS_FUN (ks:('prop,'state) KS) e h ==> (!Q s sh. h(s,sh) ==> (sh IN eh Q ==> s IN e Q)) ==> MU_MODEL_SAT f (ABS_KS ks h) eh ==> MU_MODEL_SAT f ks e``,
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MU_MODEL_SAT_def,MU_SAT_def,IS_ABS_FUN_def]
THEN REPEAT STRIP_TAC
THEN Q.PAT_ASSUM `!s. ?sh. h (s,sh)` (fn t => ASSUME_TAC t THEN ASSUME_TAC(Q.SPEC `s` t))
THEN FULL_SIMP_TAC std_ss []
THEN Q.PAT_ASSUM `!s. s IN (ABS_KS ks h).S0 ==> s IN STATES f (ABS_KS ks h) eh` (fn t => ASSUME_TAC (Q.SPEC `sh` t))
THEN IMP_RES_TAC ABS_INIT
THEN IMP_RES_TAC ABS_CONS_STATES
THEN FULL_SIMP_TAC std_ss []));

val SCC_FOLD_BASE = save_thm ("SCC_FOLD_BASE",
			      prove(``!f g pf R s sh k. (s IN {s | !i. i<=k ==> SCC (R i) (f i (0:num)) (pf i s)} = g (0:num) sh)
				    /\ (s IN {s | !i. i<=k ==> SCC (R i) (f i (1:num)) (pf i s)} = g (1:num) sh)
				    =
				    (s IN {s | !j. j<=1 ==> (s IN {s | !i. i<=k ==>  (pf i s) IN (SCC (R i) (f i j))}
							     = (g j sh))})``,
REPEAT STRIP_TAC THEN EQ_TAC THENL [
 STRIP_TAC THEN SIMP_TAC std_ss [SET_SPEC] THEN Induct_on `j` THENL [
  FULL_SIMP_TAC arith_ss [IN_DEF,DECIDE ``SUC (j:num) <= 1 = (j=0)``,SET_SPEC],
  DISCH_TAC THEN FULL_SIMP_TAC arith_ss [DECIDE ``SUC (j:num) <= 1 = (j=0)``,IN_DEF,SET_SPEC]
 ],
 SIMP_TAC std_ss [SET_SPEC] THEN DISCH_TAC
 THEN CONJ_TAC THENL [
  POP_ASSUM (fn t => ASSUME_TAC (SPEC ``0:num`` t))
  THEN FULL_SIMP_TAC arith_ss [IN_DEF],
  POP_ASSUM (fn t => ASSUME_TAC (SPEC ``1:num`` t))
  THEN FULL_SIMP_TAC arith_ss [IN_DEF]
 ]
]));

val SCC_FOLD_STEP = save_thm("SCC_FOLD_STEP",prove(``!f g pf R s sh k n.
						      s IN {s | !(j:num). j<=n ==> (s IN {s | !i. i<=k ==> SCC (R i) (f i j) (pf i s)} = (g j sh))}
						   /\ (s IN {s | !i. i<=k ==> SCC (R i) (f i (SUC n)) (pf i s)} = g (SUC n) sh)
						   = s IN {s | !(j:num). j<=(SUC n) ==> (s IN {s | !i. i<=k ==> SCC (R i) (f i j) (pf i s)} = (g j sh))}``,
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [SET_SPEC,IN_DEF]
THEN EQ_TAC THEN DISCH_TAC THEN (TRY CONJ_TAC) THEN (TRY (Induct_on `j`)) THEN RW_TAC std_ss [] THENL [
 Cases_on `j=n`
 THEN FULL_SIMP_TAC arith_ss [],
 Cases_on `j=n`
 THEN FULL_SIMP_TAC arith_ss []
]));

val SCC_INNER_FOLD_BASE1 = save_thm("SCC_INNER_FOLD_BASE1",prove(``!R j f pf s. SCC (R 0) (f 0 j) (pf 0 s) = s IN {s | !i. i<=0 ==> SCC (R i) (f i j) (pf i s)}``,
SIMP_TAC arith_ss [SET_SPEC]));

val SCC_INNER_FOLD_BASE = save_thm("SCC_INNER_FOLD_BASE",prove(``!f pf R s sh j. (SCC (R 0) (f 0 j) (pf 0 s)) /\ (SCC (R 1) (f 1 j) (pf 1 s)) = s IN {s | !i. i<=1 ==> ((pf i s) IN SCC (R i) (f i j))}``,
REPEAT STRIP_TAC THEN EQ_TAC THENL [
 STRIP_TAC THEN SIMP_TAC std_ss [SET_SPEC] THEN Induct_on `i` THENL [
  FULL_SIMP_TAC arith_ss [IN_DEF],
  DISCH_TAC THEN FULL_SIMP_TAC arith_ss [DECIDE ``SUC (i:num) <= 1 = (i=0)``,IN_DEF]
 ],
 SIMP_TAC std_ss [SET_SPEC] THEN DISCH_TAC
 THEN CONJ_TAC THENL [
  POP_ASSUM (fn t => ASSUME_TAC (SPEC ``0:num`` t))
  THEN FULL_SIMP_TAC arith_ss [IN_DEF],
  POP_ASSUM (fn t => ASSUME_TAC (SPEC ``1:num`` t))
  THEN FULL_SIMP_TAC arith_ss [IN_DEF]
 ]
]));

val SCC_INNER_FOLD_STEP = save_thm("SCC_INNER_FOLD_STEP",prove(``!f pf R s sh j n. s IN {s | !(i:num). i<=n ==> ((pf i s) IN SCC (R i) (f i j))} /\ (SCC (R (SUC n)) (f (SUC n) j) (pf (SUC n) s)) = s IN {s | !(i:num). i<=(SUC n) ==> ((pf i s) IN SCC (R i) (f i j))}``,
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [SET_SPEC,IN_DEF]
THEN EQ_TAC THEN DISCH_TAC THEN (TRY CONJ_TAC) THEN (TRY (Induct_on `i`)) THEN RW_TAC std_ss [] THENL [
 Cases_on `i=n`
 THEN FULL_SIMP_TAC arith_ss []
 THEN PAT_ASSUM ``!i. t`` (fn t => ASSUME_TAC (SPEC ``SUC i`` t)) THEN FULL_SIMP_TAC arith_ss [],
 FULL_SIMP_TAC arith_ss []
]));

val SCC_REL = save_thm("SCC_REL",prove(``!R s si. R_EQR R ==> (s IN SCC R si = R(s,si))``,
 FULL_SIMP_TAC std_ss [R_EQR_def,R_SYM_def,SCC_def,ReachFromClosed,ReachToClosed,UNION_DEF,SET_SPEC]));

val SCC_REL_IMP = save_thm("SCC_REL_IMP",prove(``!R s1 s2 si. R_EQR R ==> (s1 IN SCC R si /\ s2 IN SCC R si) ==> R(s1,s2)``,
PROVE_TAC [SCC_REL,R_EQR_def,R_SYM_def,R_TRANS_def]));

val BIGOR_OVER_AND = store_thm(
  "BIGOR_OVER_AND",
  ``!P Q k. (?i. i<=k /\ P i) /\ (?i. i<=k /\ Q i)
         =  ?i j. i<=k /\ j<=k /\ (P i /\ Q j)``,
  PROVE_TAC []);

val abst_lem1 = save_thm("abst_lem1",prove(``!f sh k i j. ((!i. i<=k /\ f i sh ==> !j. j<=k /\ f j sh ==> (i=j)) ==> i<=k /\ j<=k /\ f i sh /\ f j sh ==> (i=j))``,
REPEAT STRIP_TAC THEN RES_TAC));

val _ = export_theory();

