open HolKernel Parse boolLib bossLib

val _ = new_theory("decomp");

open envTheory
open muTheory
open muSyntaxTheory
open setLemmasTheory
open pred_setTheory
open ksTheory
open pairSyntax
open metisLib

infix &&; infix 8 by;

fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end;

(* gen ap extension proof *)
(* note: the assumptions on L and T are very strong only because ks1 and ks2 are practically the same *)
(* so these assumptions can be discharged for the cases for which AP_EXT is intended to be used *)
(* i.e. when ks1 and ks2 are different only in ap, and all the ap in f are in ap1 and ap1 SUBSET ap2 *)
(* noting that all ap must have the same semantics *)
val AP_EXT = save_thm("AP_EXT",prove(list_mk_forall ([``f:'prop mu``,``ks1:('state1,'prop) KS``,``ks2:('state2,'prop) KS``,``(e:string -> 'state1 -> bool)``,``(e':string -> 'state2 -> bool)``,``s1:'state1``,``s2:'state2``],
list_mk_imp([
``wfKS (ks1:('state1,'prop) KS)``,
``wfKS (ks2:('state2,'prop) KS)``,
``!p (s1:'state1) (s2:'state2). p IN ks1.ap ==> (p IN (ks1:('prop,'state1) KS).L s1 = p IN (ks2:('prop,'state2) KS).L s2)``,
``!a s1 s1' s2 s2'. ((s1>--(ks1:('prop,'state1) KS)/a-->s1' = s2>--(ks2:('prop,'state2) KS)/a-->s2'))``,
mk_forall(``Q:string``,mk_pforall(``s1:'state1``,mk_forall(``s2:'state2``,
					      ``s1 IN ((e:string -> 'state1 -> bool) Q) = s2 IN ((e':string -> 'state2 -> bool) Q)``))),
``IMF (f:'prop mu)``,
``!p. SUBFORMULA (AP p) f ==> p IN (ks1:('prop,'state1) KS).ap``
],
``(s1 IN STATES (f:'prop mu) (ks1:('prop,'state1) KS) (e:string -> 'state1 -> bool) = s2 IN STATES f (ks2:('prop,'state2) KS) (e':string -> 'state2 -> bool))``)),
Induct_on `f` THEN REPEAT CONJ_TAC THENL [
SIMP_TAC std_ss [STATES_def,IN_UNIV,wfKS_def], (* T *)
SIMP_TAC std_ss [STATES_def, NOT_IN_EMPTY], (* F *)
RW_TAC std_ss [STATES_def,DIFF_DEF,SET_SPEC,IN_UNIV]
THEN FULL_SIMP_TAC std_ss [IMF_def,SUB_AP_NEG]
THEN RES_TAC
THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV], (* ~ *)
RW_TAC std_ss [STATES_def,INTER_DEF,SET_SPEC]
THEN FULL_SIMP_TAC std_ss [SUB_AP_CONJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN RES_TAC
THEN FULL_SIMP_TAC std_ss []
THEN ASSUM_LIST METIS_TAC, (* /\ *)
RW_TAC std_ss [STATES_def,UNION_DEF,SET_SPEC]
THEN FULL_SIMP_TAC std_ss [SUB_AP_DISJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN RES_TAC
THEN FULL_SIMP_TAC std_ss []
THEN ASSUM_LIST METIS_TAC, (* \/ *)
RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV,wfKS_def]
THEN FULL_SIMP_TAC std_ss [IN_DEF], (* RV *)
RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV,wfKS_def]
THEN FULL_SIMP_TAC std_ss (MU_SUB_def::(tsimps "mu"))
THEN ASSUM_LIST PROVE_TAC, (* AP *)
RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV]
THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
		QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
THEN FULL_SIMP_TAC std_ss [SUB_AP_DMD,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN EQ_TAC THENL [
 REPEAT STRIP_TAC
 THEN RES_TAC
 THEN EXISTS_TAC ``s2:'state2``
 THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV],
 REPEAT STRIP_TAC
 THEN RES_TAC
 THEN EXISTS_TAC ``q:'state1``
 THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV]
], (* <> *)
RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV]
THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
		QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
THEN FULL_SIMP_TAC std_ss [SUB_AP_BOX,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
THEN EQ_TAC THENL [
REPEAT STRIP_TAC THENL [
 FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV],
 RES_TAC THEN FULL_SIMP_TAC std_ss []
 ],
REPEAT STRIP_TAC THENL [
 FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV],
 RES_TAC THEN FULL_SIMP_TAC std_ss []
 ]
],(* [] *)
SIMP_TAC std_ss [STATES_def,SET_SPEC]
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [SUB_AP_MU,IMF_def,STATES_def,SET_SPEC]
THEN (SUBGOAL_THEN (list_mk_forall([``n:num``,``s1:'state1``,``s2:'state2``],``s1 IN FP f s (ks1:('prop,'state1) KS) e[[[s<--{}]]] n = s2 IN FP f s (ks2:('prop,'state2) KS) e'[[[s<--{}]]] n``)) ASSUME_TAC) THENL [
Induct_on `n` THENL [
 RW_TAC std_ss [STATES_def,ENV_EVAL,NOT_IN_EMPTY], (* 0 *)
 REWRITE_TAC [STATES_def,ENV_UPDATE]
 THEN  (PAT_ASSUM ``!q1 q2 q3 q4 q5 q6. t`` (fn t => ASSUME_TAC (ISPECL [``(ks1:('prop,'state1) KS)``,``(ks2:('prop,'state2) KS)``,``e[[[s <-- FP f s (ks1:('prop,'state1) KS) e[[[s<--{}]]] n]]]``, ``e'[[[s<--FP f s (ks2:('prop,'state2) KS) e'[[[s<--{}]]] n]]]``] t)))
  THEN RES_TAC
  THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN SUBGOAL_THEN (fst(dest_imp(concl t))) ASSUME_TAC) THENL [
  REPEAT GEN_TAC
  THEN POP_ASSUM_LIST (MAP_EVERY (fn t => ASSUME_TAC (SPEC_ALL t)))
  THEN Cases_on `Q=s` THENL [
    FULL_SIMP_TAC std_ss [ENV_EVAL],
    FULL_SIMP_TAC std_ss [ENV_UPDATE_INV]
   ],
  FULL_SIMP_TAC std_ss [IMF_def]
  ]
 ],
POP_ASSUM (fn t => METIS_TAC [t])
], (* mu *)
SIMP_TAC std_ss [STATES_def,SET_SPEC]
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [SUB_AP_NU,IMF_def]
THEN (SUBGOAL_THEN (list_mk_forall([``n:num``,``s1:'state1``,``s2:'state2``],``s1 IN FP f s (ks1:('prop,'state1) KS) e[[[s<--ks1.S]]] n = s2 IN FP f s (ks2:('prop,'state2) KS) e'[[[s<--ks2.S]]] n``)) ASSUME_TAC) THENL [
Induct_on `n` THENL [
  FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,IN_UNIV,wfKS_def], (* 0 *)
  REWRITE_TAC [STATES_def,ENV_UPDATE]
  THEN (PAT_ASSUM ``!q1 q2 q3 q4 q5 q6. t`` (fn t => ASSUME_TAC (ISPECL [``(ks1:('prop,'state1) KS)``,``(ks2:('prop,'state2) KS)``,``e[[[s <-- FP f s (ks1:('prop,'state1) KS) e[[[s<--ks1.S]]] n]]]``, ``e'[[[s<--FP f s (ks2:('prop,'state2) KS) e'[[[s<--ks2.S]]] n]]]``] t)))
  THEN RES_TAC
  THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN SUBGOAL_THEN (fst(dest_imp(concl t))) ASSUME_TAC) THENL [
  REPEAT GEN_TAC
  THEN POP_ASSUM_LIST (MAP_EVERY (fn t => ASSUME_TAC (SPEC_ALL t)))
  THEN Cases_on `Q=s` THENL [
    FULL_SIMP_TAC std_ss [ENV_EVAL],
    FULL_SIMP_TAC std_ss [ENV_UPDATE_INV]
   ],
   FULL_SIMP_TAC std_ss [IMF_def]
  ]
 ],
POP_ASSUM (fn t => METIS_TAC [t])
] (* nu *)
]));

val lem3a = REWRITE_RULE [GSYM IMF_MU_NNF] (ISPECL [``ks:('prop,'state) KS``,``(NNF f):'prop mu``,``e:string->'state->bool``,``Y:'state->bool``,``X:'state->bool``,``Q:string``] (REWRITE_RULE [SUBSET_DEF] (GEN_ALL (SIMP_RULE std_ss [] (REWRITE_RULE [SUBSET_REFL] (ISPECL [``f:'prop mu``,``ks:('prop,'state) KS``,``e:string -> 'state -> bool``,``e:string -> 'state -> bool``,``Q:string``,``X:'state->bool``,``Y:'state->bool``] STATES_MONO))))));

(* gen decomp proof *)
val DECOMP = save_thm("DECOMP",SIMP_RULE std_ss [STATES_NNF_ID] (prove(list_mk_pforall ([``(f:'prop mu)``,``s:'state``,``(e:string -> 'state -> bool)``,``Q:string``,``ks1:('prop,'state) KS``,``ks2:('prop,'state) KS``],list_mk_imp([``IMF mu (Q:string) .. (f:'prop mu)``,``!a g. ~SUBFORMULA (<<a>> g) (NNF (f:'prop mu))``,``wfKS (ks1:('prop,'state) KS)``,``wfKS (ks2:('prop,'state) KS)``,``(ks1:('prop,'state) KS).ap=(ks2:('prop,'state) KS).ap``,``(ks1:('prop,'state) KS).L=(ks2:('prop,'state) KS).L``,``!a s s'. ((ks2:('prop,'state) KS).T a)(s,s') ==> ((ks1:('prop,'state) KS).T a)(s,s')``],``s IN STATES (NNF (f:'prop mu)) (ks1:('prop,'state) KS) e ==> s IN STATES (NNF f) (ks2:('prop,'state) KS) e``)),
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THENL [
SIMP_TAC std_ss [NNF_def,STATES_def,wfKS_def,IN_UNIV], (* T *)
SIMP_TAC std_ss [NNF_def,STATES_def], (* F *)
(*RW_TAC std_ss [STATES_def,DIFF_DEF,SET_SPEC,IN_UNIV,REWRITE_RULE [wfKS_def] wfKS_p2ks,REWRITE_RULE [wfKS_def] wfKS_aks], (* ~ *)*)
RW_TAC std_ss [NNF_def,SUB_DMD_CONJ,IMF_MU_CONJ,STATES_def,INTER_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC, (* /\ *)
RW_TAC std_ss [NNF_def,SUB_DMD_DISJ,IMF_MU_DISJ,STATES_def,UNION_DEF,SET_SPEC] THENL [
 DISJ1_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC,
 DISJ2_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC], (* \/ *)
RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,IN_UNIV,wfKS_def], (* AP *)
RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,IN_UNIV,wfKS_def], (* RV *)
SIMP_TAC std_ss [NNF_def,SUB_DMD_DMD], (* <> *)
FULL_SIMP_TAC std_ss [NNF_def,SUB_DMD_BOX,IMF_MU_BOX,STATES_def,SET_SPEC,IN_UNIV,wfKS_def]
THEN NTAC 15 STRIP_TAC
THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
			 QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
THEN REPEAT STRIP_TAC
THEN RES_TAC
THEN ASSUM_LIST PROVE_TAC, (* [] *)
SIMP_TAC std_ss [STATES_def,NNF_def,SET_SPEC]
THEN NTAC 15 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_MU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_MU]
THEN RES_TAC
THEN (SUBGOAL_THEN (mk_forall(``n:num``,list_mk_forall([``s:'state``],mk_imp(``s IN FP (NNF f) Q (ks1:('prop,'state) KS) e[[[Q<--{}]]] n``,``s IN FP (NNF f) Q (ks2:('prop,'state) KS) e[[[Q<--{}]]] n``)))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  SIMP_TAC std_ss [STATES_def,ENV_EVAL],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF f) Q  (ks1:('prop,'state) KS) e[[[Q<--{}]]] n``,``X:'state -> bool``)
  THEN SPEC_TAC (``FP (NNF f) Q  (ks2:('prop,'state) KS)e[[[Q<--{}]]] n``,``Y:'state->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN IMP_RES_TAC lem3a
  THEN FULL_SIMP_TAC std_ss []
  ],
 ASSUM_LIST PROVE_TAC
 ], (* mu *)
SIMP_TAC std_ss [STATES_def,NNF_def,SET_SPEC]
THEN NTAC 15 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_NU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_NU]
THEN RES_TAC
THEN (SUBGOAL_THEN (mk_forall(``n:num``,mk_forall(``s:'state``,mk_imp(``s IN FP (NNF f) Q (ks1:('prop,'state) KS) e[[[Q<--ks1.S]]] n``,``s IN FP (NNF f) Q (ks2:('prop,'state) KS) e[[[Q<--ks2.S]]] n``)))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  SIMP_TAC std_ss [STATES_def,ENV_EVAL]
  THEN FULL_SIMP_TAC std_ss [wfKS_def],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF f) Q (ks1:('prop,'state) KS) e[[[Q<--ks1.S]]] n``,``X:'state -> bool``)
  THEN SPEC_TAC (``FP (NNF f) Q (ks2:('prop,'state) KS) e[[[Q<--ks2.S]]] n``,``Y:'state ->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN IMP_RES_TAC lem3a
  THEN FULL_SIMP_TAC std_ss []
  ],
 ASSUM_LIST PROVE_TAC
 ], (* nu *)
SIMP_TAC std_ss [NNF_def,STATES_def], (* ~T *)
SIMP_TAC std_ss [NNF_def,STATES_def,wfKS_def,IN_UNIV], (* ~F *)
RW_TAC std_ss [NNF_def,SUB_DMD_DISJ,IMF_MU_NEG_CONJ,STATES_def,UNION_DEF,SET_SPEC] THENL [
 DISJ1_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC,
 DISJ2_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC], (* ~/\ *)
RW_TAC std_ss [NNF_def,SUB_DMD_CONJ,IMF_MU_NEG_DISJ,STATES_def,INTER_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC, (* ~\/ *)
RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,IN_UNIV,wfKS_def], (* ~AP *)
RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,IN_UNIV,wfKS_def], (* ~RV *)
FULL_SIMP_TAC std_ss [NNF_def,STATES_def,IMF_MU_NEG_DMD,SET_SPEC,IN_UNIV,wfKS_def]
THEN NTAC 15 STRIP_TAC
THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
			 QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [SUB_DMD_BOX]
THEN RES_TAC
THEN ASSUM_LIST PROVE_TAC, (* ~<>*)
SIMP_TAC std_ss [NNF_def,SUB_DMD_DMD], (* ~[] *)
SIMP_TAC std_ss [NNF_def,SUB_DMD_NEG_NEG,IMF_MU_NEG_NEG], (* ~~ *)
SIMP_TAC std_ss [STATES_def,NNF_def,SET_SPEC]
THEN NTAC 15 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_NEG_MU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_NU]
THEN POP_ASSUM (fn t => ASSUME_TAC (ONCE_REWRITE_RULE [IMF_MU_INV_RVNEG] t))
THEN RES_TAC
THEN (SUBGOAL_THEN (mk_forall(``n:num``,mk_forall(``s:'state``,mk_imp(``s IN FP (NNF (RVNEG Q ~f)) Q (ks1:('prop,'state) KS) e[[[Q<--ks1.S]]] n``,``s IN FP (NNF (RVNEG Q ~f)) Q (ks2:('prop,'state) KS) e[[[Q<--ks2.S]]] n``)))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,wfKS_def],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ks1:('prop,'state) KS) e[[[Q<--ks1.S]]] n``,``X:'state -> bool``)
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ks2:('prop,'state) KS) e[[[Q<--ks2.S]]] n``,``Y:'state->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN IMP_RES_TAC lem3a
  THEN FULL_SIMP_TAC std_ss []
  ],
 ASSUM_LIST PROVE_TAC
 ], (* ~mu *)
SIMP_TAC std_ss [STATES_def,NNF_def,SET_SPEC]
THEN NTAC 15 STRIP_TAC
THEN IMP_RES_TAC IMF_MU_NEG_NU
THEN FULL_SIMP_TAC std_ss [SUB_DMD_MU]
THEN POP_ASSUM (fn t => ASSUME_TAC (ONCE_REWRITE_RULE [IMF_MU_INV_RVNEG] t))
THEN RES_TAC
THEN (SUBGOAL_THEN (mk_forall(``n:num``,mk_forall(``s:'state``,mk_imp(``s IN FP (NNF (RVNEG Q ~f)) Q (ks1:('prop,'state) KS) e[[[Q<--{}]]] n``,``s IN FP (NNF (RVNEG Q ~f)) Q (ks2:('prop,'state) KS) e[[[Q<--{}]]] n``)))) ASSUME_TAC) THENL [
 Induct_on `n` THENL [
  SIMP_TAC std_ss [STATES_def,ENV_EVAL],
  SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC t THEN UNDISCH_TAC (concl t))
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ks1:('prop,'state) KS) e[[[Q<--{}]]] n``,``X:'state -> bool``)
  THEN SPEC_TAC (``FP (NNF (RVNEG Q ~f)) Q (ks2:('prop,'state) KS) e[[[Q<--{}]]] n``,``Y:'state ->bool``)
  THEN REPEAT GEN_TAC
  THEN STRIP_TAC
  THEN IMP_RES_TAC lem3a
  THEN FULL_SIMP_TAC std_ss []
  ],
 ASSUM_LIST PROVE_TAC
 ] (* ~nu*)
])));


val _ = export_theory();