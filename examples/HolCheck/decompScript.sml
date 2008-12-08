open HolKernel Parse boolLib bossLib

val _ = new_theory("decomp");

(* app load ["envTheory","muTheory","muSyntaxTheory","setLemmasTheory","pred_setTheory","ksTheory",
             "pairSyntax","metisLib","commonTools"] *)

open pairSyntax metisLib
open envTheory muTheory muSyntaxTheory setLemmasTheory pred_setTheory ksTheory commonTools

infix &&; infix 8 by;

(* NOTE: decompTheory imposes the restriction that prop types are always of the form state_ty --> bool *)
(* otherwise AP_EXT_THM  won't work*)

(*take f:('state1->bool) mu and return f:('state2->bool) mu*)
(*lesson: we _can_ muck around with types within the object logic, using choice and extensionality*)
val AP_EXT_def = Define `
(AP_EXT (T:('state1->bool) mu) = (T:(('state1#'state2)->bool) mu)) /\
(AP_EXT F = F) /\
(AP_EXT (~f) = ~(AP_EXT f)) /\
(AP_EXT (f1 /\ f2) = (AP_EXT f1) /\ (AP_EXT f2)) /\
(AP_EXT (f1 \/ f2) = (AP_EXT f1) \/ (AP_EXT f2)) /\
(AP_EXT (RV Q) = (RV Q)) /\
(AP_EXT (AP p) = AP (@p'. !(s1:'state1) (s2:'state2). p s1 = p' (s1,s2))) /\
(AP_EXT (<<a>> f) = <<a>> (AP_EXT f)) /\
(AP_EXT ([[a]] f) = [[a]] (AP_EXT f)) /\
(AP_EXT (mu Q.. f) = (mu Q.. (AP_EXT f)))  /\
(AP_EXT (nu Q.. f) =  (nu Q.. (AP_EXT f)))`;


val APEXT_RV = prove(``!f Q. (RV Q = AP_EXT f) = (f = RV Q)``,
Induct_on `f` THEN  FULL_SIMP_TAC std_ss ([AP_EXT_def,MU_SUB_def]@(tsimps ``:'a mu``)) THEN PROVE_TAC [])

val APEXT_RV_SUBF = prove(``!f (Q:string). ~RV Q SUBF f = ~RV Q SUBF (AP_EXT f)``,
Induct_on `f` THEN  FULL_SIMP_TAC std_ss ([AP_EXT_def,MU_SUB_def]@(tsimps ``:'a mu``))
THEN METIS_TAC [APEXT_RV])

val APEXT_RVNEG = prove(
  ``!f Q. AP_EXT (RVNEG Q f) = RVNEG Q (AP_EXT f)``,
  Induct_on `f` THEN
  FULL_SIMP_TAC std_ss ([AP_EXT_def,RVNEG_def]@(tsimps ``:'a mu``)) THENL [
    MAP_EVERY Q.X_GEN_TAC [`s`, `Q`] THEN Cases_on `Q=s` THENL [
      FULL_SIMP_TAC std_ss ([AP_EXT_def,RVNEG_def]@(tsimps ``:'a mu``)),
      METIS_TAC [APEXT_RV]
    ],
    MAP_EVERY Q.X_GEN_TAC [`s`, `Q`] THEN Cases_on `Q=s` THEN
    FULL_SIMP_TAC std_ss ([AP_EXT_def,RVNEG_def]@(tsimps ``:'a mu``)),
    MAP_EVERY Q.X_GEN_TAC [`s`, `Q`] THEN Cases_on `Q=s` THEN
    FULL_SIMP_TAC std_ss ([AP_EXT_def,RVNEG_def]@(tsimps ``:'a mu``))
  ]);

val APEXT_NNF =  save_thm("APEXT_NNF",prove(``!f. AP_EXT (NNF f) = NNF (AP_EXT f)``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC
THEN RW_TAC std_ss ([MU_SUB_def,NNF_def,RVNEG_def,AP_EXT_def]@(tsimps ``:'a mu``))
THEN  FULL_SIMP_TAC std_ss ([APEXT_RVNEG,AP_EXT_def,RVNEG_def]@(tsimps ``:'a mu``))))

val APEXT_IMF = save_thm("APEXT_IMF",prove(``!f. IMF f = IMF (AP_EXT f)``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC
THEN RW_TAC std_ss ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def,AP_EXT_def]@(tsimps ``:'a mu``)) THENL [
 METIS_TAC ([APEXT_NNF,APEXT_RV_SUBF,AP_EXT_def,RVNEG_def]@(tsimps ``:'a mu``)),
 METIS_TAC ([APEXT_NNF,APEXT_RV_SUBF,AP_EXT_def,RVNEG_def]@(tsimps ``:'a mu``)),
 REWRITE_TAC [GSYM APEXT_NNF,GSYM APEXT_RV_SUBF]
 THEN METIS_TAC [APEXT_RVNEG,IMF_INV_RVNEG],
 REWRITE_TAC [GSYM APEXT_NNF,GSYM APEXT_RV_SUBF]
 THEN METIS_TAC [APEXT_RVNEG,IMF_INV_RVNEG]
]))

(* gen ap extension proof *)
(* basic idea is that if f holds in some model then it should hold in the same model with extra ap's thrown in,
   where the new ap's may possibly introduce new state vars*)
(* note: the assumptions on L and T are very strong only because ks1 and ks2 are more or less the same
   so these assumptions can be discharged for the cases for which AP_EXT is intended to be used
   i.e. when ks1 and ks2 are different only in ap, and all the ap in f are in ap1 and ap1 SUBSET ap2
   noting that all ap must have the same semantics *)
(* since all the ap's type changes if new state vars are introduced, we have to resort to a little trickery (via AP_EXT)
   to "lift" f to the new ap type that has extra state vars *)
(* ASSERT: note also that this only works if the L are defined as \s p. p s; the 3rd and 4th assums *)
val AP_EXT_THM = store_thm(
  "AP_EXT_THM",
  ``!ks1 ks2 s1 s2 e1 e2 f.
       wfKS ks1 ==> wfKS ks2 ==>
       (!p s1. p IN ks1.L s1 = p s1) ==>
       (!p s1 s2. p IN ks2.L (s1,s2) = p (s1,s2)) ==>
       (!p. p IN ks1.ap ==>
            ?p'. !s1 s2. p IN ks1.L s1 = p' IN ks2.L (s1,s2)) ==>
       (!a s1 s1' s2 s2'. s1>--ks1/a-->s1' = (s1,s2)>--ks2/a-->(s1',s2')) ==>
       (!Q s1 s2. s1 IN e1 Q = (s1,s2) IN e2 Q) ==>
       IMF f ==>
       (!p. AP p SUBF f ==> p IN ks1.ap)
     ==>
       (s1 IN STATES f ks1 e1 = (s1,s2) IN STATES (AP_EXT f) ks2 e2)``,
  Induct_on `f` THEN REPEAT CONJ_TAC THENL [
    SIMP_TAC std_ss [STATES_def,IN_UNIV,wfKS_def,AP_EXT_def], (* T *)
    SIMP_TAC std_ss [STATES_def, NOT_IN_EMPTY,AP_EXT_def], (* F *)
    RW_TAC std_ss [STATES_def,DIFF_DEF,SET_SPEC,IN_UNIV,AP_EXT_def]
    THEN FULL_SIMP_TAC std_ss [IMF_def,SUB_AP_NEG]
    THEN RES_TAC
    THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV], (* ~ *)
    RW_TAC std_ss [STATES_def,INTER_DEF,SET_SPEC,AP_EXT_def]
    THEN FULL_SIMP_TAC std_ss [SUB_AP_CONJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
    THEN RES_TAC
    THEN FULL_SIMP_TAC std_ss []
    THEN METIS_TAC [AP_EXT_def], (* /\ *)
    RW_TAC std_ss [STATES_def,UNION_DEF,SET_SPEC,AP_EXT_def]
    THEN FULL_SIMP_TAC std_ss [SUB_AP_DISJ,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
    THEN RES_TAC
    THEN FULL_SIMP_TAC std_ss []
    THEN METIS_TAC [AP_EXT_def], (* \/ *)

    RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV,wfKS_def,AP_EXT_def]
    THEN FULL_SIMP_TAC std_ss [IN_DEF], (* RV *)

    RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV,wfKS_def,AP_EXT_def]
    THEN FULL_SIMP_TAC std_ss (MU_SUB_def::(tsimps ``:'a mu``))
    THEN SELECT_ELIM_TAC
    THEN PROVE_TAC [], (* AP *)

    RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV,AP_EXT_def]
    THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
                    QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
    THEN FULL_SIMP_TAC std_ss [SUB_AP_DMD,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
    THEN EQ_TAC THENL [
     REPEAT STRIP_TAC
     THEN RES_TAC
     THEN Q.EXISTS_TAC `(q,s2)`
     THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV],
     REPEAT STRIP_TAC
     THEN RES_TAC
     THEN Q.EXISTS_TAC `FST q`
     THEN METIS_TAC ([wfKS_def,IN_UNIV]@(get_ss_rewrs pairTheory.pair_rwts))
    ], (* <> *)

    RW_TAC std_ss [STATES_def,SET_SPEC,IN_UNIV,AP_EXT_def]
    THEN CONV_TAC (FORK_CONV(QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV)),
                    QUANT_CONV (FORK_CONV(REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,combinTheory.K_DEF],ALL_CONV))))
    THEN FULL_SIMP_TAC std_ss [SUB_AP_BOX,IMF_def,FORALL_AND_THM,DISJ_IMP_THM]
    THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THENL [
     FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV],
     RES_TAC THEN METIS_TAC (get_ss_rewrs pairTheory.pair_rwts)
     ],
    REPEAT STRIP_TAC THENL [
     FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV],
     RES_TAC THEN  METIS_TAC (get_ss_rewrs pairTheory.pair_rwts)
     ]
    ],(* [] *)

    Q.X_GEN_TAC `s` THEN SIMP_TAC std_ss [STATES_def,SET_SPEC,AP_EXT_def]
    THEN REPEAT STRIP_TAC
    THEN FULL_SIMP_TAC std_ss [SUB_AP_MU,IMF_def,STATES_def,SET_SPEC]
    THEN Q.SUBGOAL_THEN `!n s1 s2. s1 IN FP f s ks1 e1[[[s<--{}]]] n = (s1,s2) IN FP (AP_EXT f) s ks2 e2[[[s<--{}]]] n` ASSUME_TAC
    THENL [
     Induct_on `n` THENL [
      RW_TAC std_ss [STATES_def,ENV_EVAL,NOT_IN_EMPTY], (* 0 *)
      REPEAT GEN_TAC
      THEN REWRITE_TAC [STATES_def,ENV_UPDATE]
      THEN (Q.PAT_ASSUM `!q1 q2 q3 q4 q5 q6. t` (fn t => ASSUME_TAC (Q.SPECL [`ks1`,`ks2`,`s1`,`s2`,`e1[[[s <-- FP (f:('a -> bool) mu) s ks1 e1[[[s<--{}]]] n]]]`, `e2[[[s<--FP (AP_EXT (f:('a -> bool) mu)) s  (ks2 :('a#'b -> bool,'a#'b) KS) e2[[[s<--{}]]] n]]]`] t)))
      THEN RES_TAC
      THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
      THEN POP_ASSUM (fn t => ASSUME_TAC t THEN SUBGOAL_THEN (fst(dest_imp(concl t))) ASSUME_TAC) THENL [
       NTAC 2 (POP_ASSUM (K ALL_TAC))
       THEN REPEAT GEN_TAC
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

    Q.X_GEN_TAC `s` THEN
    SIMP_TAC std_ss [STATES_def,SET_SPEC,AP_EXT_def]
    THEN REPEAT STRIP_TAC
    THEN FULL_SIMP_TAC std_ss [SUB_AP_NU,IMF_def]
    THEN Q.SUBGOAL_THEN `!n s1 s2. s1 IN FP f s ks1 e1[[[s<--ks1.S]]] n = (s1,s2) IN FP (AP_EXT f) s ks2 e2[[[s<--ks2.S]]] n` ASSUME_TAC THENL [
     Induct_on `n` THENL [
      FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,IN_UNIV,wfKS_def], (* 0 *)
      REPEAT GEN_TAC
      THEN REWRITE_TAC [STATES_def,ENV_UPDATE]
      THEN (Q.PAT_ASSUM `!q1 q2 q3 q4 q5 q6. t` (fn t => ASSUME_TAC (Q.SPECL [`ks1`,`ks2`,`s1`,`s2`,`e1[[[s <-- FP (f:('a -> bool) mu) s ks1 e1[[[s<--ks1.S]]] n]]]`, `e2[[[s<--FP (AP_EXT (f:('a -> bool) mu)) s (ks2 :('a#'b -> bool,'a#'b) KS) e2[[[s<--ks2.S]]] n]]]`] t)))
      THEN RES_TAC
      THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
      THEN POP_ASSUM (fn t => ASSUME_TAC t THEN SUBGOAL_THEN (fst(dest_imp(concl t))) ASSUME_TAC) THENL [
      NTAC 2 (POP_ASSUM (K ALL_TAC))
      THEN REPEAT GEN_TAC
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
  ])

val lem3a = REWRITE_RULE [GSYM IMF_MU_NNF] (ISPECL [``ks:('prop,'state) KS``,``(NNF f):'prop mu``,``e:string->'state->bool``,``Y:'state->bool``,``X:'state->bool``,``Q:string``] (REWRITE_RULE [SUBSET_DEF] (GEN_ALL (SIMP_RULE std_ss [] (REWRITE_RULE [SUBSET_REFL] (ISPECL [``f:'prop mu``,``ks:('prop,'state) KS``,``e:string -> 'state -> bool``,``e:string -> 'state -> bool``,``Q:string``,``X:'state->bool``,``Y:'state->bool``] STATES_MONO))))));

(* gen decomp proof *)
(* this is bascially that a universal property holding in M holds in M||M', where || is parallel synchronous composition,
   assuming that whenever M||M' can do an action, M can as well *)
val DECOMP = SIMP_RULE std_ss [STATES_NNF_ID] (prove(
list_mk_pforall ([``(f:'prop mu)``,``s:'state``,``(e:string -> 'state -> bool)``,``Q:string``,``ks1:('prop,'state) KS``,``ks2:('prop,'state) KS``],
list_mk_imp([
``IMF mu (Q:string) .. (f:'prop mu)``,
``!a g. ~SUBFORMULA (<<a>> g) (NNF (f:'prop mu))``,
``wfKS (ks1:('prop,'state) KS)``,
``wfKS (ks2:('prop,'state) KS)``,
``(ks1:('prop,'state) KS).ap=(ks2:('prop,'state) KS).ap``,
``(ks1:('prop,'state) KS).L=(ks2:('prop,'state) KS).L``,
``!a s s'. ((ks2:('prop,'state) KS).T a)(s,s') ==> ((ks1:('prop,'state) KS).T a)(s,s')``],
``s IN STATES (NNF (f:'prop mu)) (ks1:('prop,'state) KS) e ==> s IN STATES (NNF f) (ks2:('prop,'state) KS) e``)),
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THENL [
  SIMP_TAC std_ss [NNF_def,STATES_def,wfKS_def,IN_UNIV], (* T *)
  SIMP_TAC std_ss [NNF_def,STATES_def], (* F *)
  RW_TAC std_ss [NNF_def,SUB_DMD_CONJ,IMF_MU_CONJ,STATES_def,INTER_DEF,
                 SET_SPEC] THEN PROVE_TAC [], (* /\ *)

  RW_TAC std_ss [NNF_def,SUB_DMD_DISJ,IMF_MU_DISJ,STATES_def,UNION_DEF,
                 SET_SPEC]
  THENL [
    DISJ1_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC,
    DISJ2_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC
  ], (* \/ *)

  RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,IN_UNIV,wfKS_def], (* AP *)
  RW_TAC std_ss [NNF_def,STATES_def,SET_SPEC,IN_UNIV,wfKS_def], (* RV *)

  SIMP_TAC std_ss [NNF_def,SUB_DMD_DMD], (* <> *)

  FULL_SIMP_TAC std_ss [NNF_def,SUB_DMD_BOX,IMF_MU_BOX,STATES_def,SET_SPEC,
                        IN_UNIV,wfKS_def] THEN
  NTAC 15 STRIP_TAC THEN
  CONV_TAC (FORK_CONV
                (QUANT_CONV
                     (FORK_CONV
                          (REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,
                                         combinTheory.K_DEF],
                           ALL_CONV)),
                     QUANT_CONV
                         (FORK_CONV
                              (REWRITE_CONV [KS_TRANSITION_def,KS_accfupds,
                                             combinTheory.K_DEF],
                               ALL_CONV)))) THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN PROVE_TAC [], (* [] *)

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

  RW_TAC std_ss [NNF_def,SUB_DMD_DISJ,IMF_MU_NEG_CONJ,STATES_def,UNION_DEF,
                 SET_SPEC]
  THENL [
   DISJ1_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC,
   DISJ2_TAC THEN FULL_SIMP_TAC std_ss [] THEN ASSUM_LIST PROVE_TAC
  ], (* ~/\ *)

  RW_TAC std_ss [NNF_def,SUB_DMD_CONJ,IMF_MU_NEG_DISJ,STATES_def,INTER_DEF,
                 SET_SPEC] THEN PROVE_TAC [], (* ~\/ *)

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
]));

val DECOMP2 =
 CONV_RULE (STRIP_QUANT_CONV (PUSHN_IMP_CONV 6))
(CONV_RULE (STRIP_QUANT_CONV (PUSHN_IMP_CONV 6))
(CONV_RULE (PUSH_QUANT_CONV SWAP_VARS_CONV 4)
(CONV_RULE (LAST_FORALL_CONV FORALL_IMP_CONV)
(CONV_RULE (QUANT_CONV (QUANT_CONV (QUANT_CONV (PUSH_QUANT_CONV SWAP_VARS_CONV 2)))) DECOMP))))

val DECOMP3 = save_thm("PAR_SYNC_DECOMP", prove(``!s e ks1 ks2 f.
         wfKS ks1 ==>
         wfKS ks2 ==>
         (ks1.ap = ks2.ap) ==>
         (ks1.L = ks2.L) ==>
         (!a s s'. ks2.T a (s,s') ==> ks1.T a (s,s')) ==>
         (IMF f) ==>
         (!a g. ~(<<a>> g SUBF NNF f)) ==>
         s IN STATES f ks1 e ==>
         s IN STATES f ks2 e``, METIS_TAC [IMF_MU_EXT,DECOMP2]))

val _ = export_theory();
