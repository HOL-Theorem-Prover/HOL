open HolKernel Parse boolLib bossLib

val _ = new_theory("cache")


open bossLib
open pairTheory
open pairLib
open pairTools
open pairSyntax
open pred_setTheory
open pred_setLib
open listTheory
open stringTheory
open sumTheory
open simpLib
open stringLib
open numLib
open metisLib
open ksTheory
open setLemmasTheory
open reachTheory
open muSyntaxTheory
open envTheory
open muTheory

infix &&; infix 8 by;

fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end

(* thms for environment-invariant satisfiability *)

val MU_SAT_RV_ENV_EQ = save_thm("MU_SAT_RV_ENV_EQ",prove(``!(ks: ('prop,'state) KS) . wfKS ks ==> (!s Q e e' X. ((MU_SAT (RV Q) ks e s = X) /\ (e Q = e' Q)) ==> (MU_SAT (RV Q) ks e' s = X))``,SIMP_TAC std_ss [wfKS_def,MU_SAT_def,STATES_def,MU_SAT_RV]))

val SAT_T_ENV_INV = save_thm("SAT_T_ENV_INV", GENL [``ks: ('prop,'state) KS``,``e:string -> 'state -> bool``,``e':string -> 'state -> bool``] (EXT (GEN ``s:'state`` (SPEC_ALL (prove(``!(ks: ('prop,'state) KS)  e e' s. MU_SAT T ks e s = MU_SAT T ks e' s``,SIMP_TAC std_ss [MU_SAT_def,STATES_def]))))))

val SAT_F_ENV_INV = save_thm("SAT_F_ENV_INV", GENL [``ks: ('prop,'state) KS``,``e:string -> 'state -> bool``,``e':string -> 'state -> bool``] (EXT (GEN ``s:'state`` (SPEC_ALL (prove(``!(ks: ('prop,'state) KS)  e e' s. MU_SAT F ks e s = MU_SAT F ks e' s``,SIMP_TAC std_ss [MU_SAT_def,STATES_def]))))))

val SAT_AP_ENV_INV = save_thm("SAT_AP_ENV_INV", GENL [``ks: ('prop,'state) KS``,``p:'prop``,``e:string -> 'state -> bool``,``e':string -> 'state -> bool``] (EXT (GEN ``s:'state`` (SPEC_ALL (prove(``!(ks: ('prop,'state) KS)  (p:'prop) e e' s. MU_SAT (AP p) ks e s = MU_SAT (AP p) ks e' s``,SIMP_TAC std_ss [MU_SAT_def,STATES_def]))))))

val SAT_RV_ENV_INV = save_thm("SAT_RV_ENV_INV",prove(``!(ks: ('prop,'state) KS)  Q e e'. (e Q = e' Q) ==> (MU_SAT (RV Q) ks e = MU_SAT (RV Q) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [MU_SAT_def,STATES_def,MU_SAT_RV]))

val SAT_ENV_INV_META = prove(``(!e e'. MU_SAT (f:'prop mu) (ks : ('prop,'state) KS) e = MU_SAT (f:'prop mu) (ks : ('prop,'state) KS) e') = (!e e' (s:'state).  MU_SAT (f:'prop mu) (ks : ('prop,'state) KS) e s = MU_SAT (f:'prop mu) (ks : ('prop,'state) KS) e' s)``,SIMP_TAC std_ss [GEN_ALL (FUN_EQ_CONV ``MU_SAT (f :'prop mu) (ks :('prop,'state) KS) (e: string -> 'state -> bool)= MU_SAT f ks (e' :string -> 'state -> bool)``)])

val SAT_ENV_INV_META2=FUN_EQ_CONV ``MU_SAT (f:'prop mu) (ks : ('prop,'state) KS) e = MU_SAT (f:'prop mu) (ks : ('prop,'state) KS) e'``

val SAT_NEG_ENV_INV = save_thm("SAT_NEG_ENV_INV", prove(``!(ks:('prop,'state) KS) . wfKS ks ==> (!(f:'prop mu) e e'. ((!e e'. MU_SAT f ks e = MU_SAT f ks e') ==> (MU_SAT (~f) ks e = MU_SAT (~f) ks e')))``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META,MU_SAT_def,STATES_def,wfKS_def,UNIV_DEF,DIFF_DEF,SET_SPEC] THEN FULL_SIMP_TAC std_ss [IN_DEF]))


val SAT_NEG_ENV_INV2 = save_thm("SAT_NEG_ENV_INV2", prove(``!(ks:('prop,'state) KS) . wfKS ks ==> (!(f:'prop mu) e e'. ((MU_SAT f ks e = MU_SAT f ks e') ==> (MU_SAT (~f) ks e = MU_SAT (~f) ks e')))``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META2,MU_SAT_def,STATES_def,wfKS_def,UNIV_DEF,DIFF_DEF,SET_SPEC]))

val SAT_CONJ_ENV_INV = save_thm("SAT_CONJ_ENV_INV", prove(``!(ks:('prop,'state) KS)  (f:'prop mu) (g:'prop mu) e e'. ((!e e'. MU_SAT f ks e = MU_SAT f ks e') /\ (!e e'. MU_SAT g ks e = MU_SAT g ks e')) ==> (MU_SAT (f /\ g) ks e = MU_SAT (f /\ g) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META,MU_SAT_def,STATES_def,INTER_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_CONJ_ENV_INV2 = save_thm("SAT_CONJ_ENV_INV2", prove(``!(ks:('prop,'state) KS)  f (g:'prop mu) e e'. ((MU_SAT f ks e = MU_SAT f ks e') /\ (MU_SAT g ks e = MU_SAT g ks e')) ==> (MU_SAT (f /\ g) ks e = MU_SAT (f /\ g) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META2,MU_SAT_def,STATES_def,INTER_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_DISJ_ENV_INV = save_thm("SAT_DISJ_ENV_INV", prove(``!(ks:('prop,'state) KS)  f (g:'prop mu) e e'. ((!e e'. MU_SAT f ks e = MU_SAT f ks e') /\ (!e e'. MU_SAT g ks e = MU_SAT g ks e')) ==> (MU_SAT (f \/ g) ks e = MU_SAT (f \/ g) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META,MU_SAT_def,STATES_def,UNION_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_DISJ_ENV_INV2 = save_thm("SAT_DISJ_ENV_INV2", prove(``!(ks:('prop,'state) KS)  f (g:'prop mu) e e'. ((MU_SAT f ks e = MU_SAT f ks e') /\ (MU_SAT g ks e = MU_SAT g ks e')) ==> (MU_SAT (f \/ g) ks e = MU_SAT (f \/ g) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META2,MU_SAT_def,STATES_def,UNION_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_DMD_ENV_INV = save_thm("SAT_DMD_ENV_INV", prove(``!(ks:('prop,'state) KS)  a f e e'. (!e e'. MU_SAT f ks e = MU_SAT f ks e') ==> (MU_SAT (<<a>> f) ks e = MU_SAT (<<a>> f) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META,MU_SAT_def,STATES_def,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_DMD_ENV_INV2 = save_thm("SAT_DMD_ENV_INV2", prove(``!(ks:('prop,'state) KS)  a f e e'. (MU_SAT f ks e = MU_SAT f ks e') ==> (MU_SAT (<<a>> f) ks e = MU_SAT (<<a>> f) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META2,MU_SAT_def,STATES_def,UNION_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_BOX_ENV_INV = save_thm("SAT_BOX_ENV_INV", prove(``!(ks:('prop,'state) KS)  a f e e'. (!e e'. MU_SAT f ks e = MU_SAT f ks e') ==> (MU_SAT ([[a]] f) ks e = MU_SAT ([[a]] f) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META,MU_SAT_def,STATES_def,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_BOX_ENV_INV2 = save_thm("SAT_BOX_ENV_INV2", prove(``!(ks:('prop,'state) KS)  a f e e'. (MU_SAT f ks e = MU_SAT f ks e') ==> (MU_SAT ([[a]] f) ks e = MU_SAT ([[a]] f) ks e')``,REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META2,MU_SAT_def,STATES_def,INTER_DEF,SET_SPEC] THEN ASSUM_LIST PROVE_TAC))

val SAT_LFP_ENV_INV =
    save_thm("SAT_LFP_ENV_INV",
	     prove(``!(ks:('prop,'state) KS)  s Q f e e'. (!s X e e'. MU_SAT f ks e[[[Q<--X]]] s = MU_SAT f ks e'[[[Q<--X]]] s)
		      ==> (MU_SAT (mu Q.. f) ks e s = MU_SAT (mu Q .. f) ks e' s)``,
		      SIMP_TAC std_ss [MU_SAT_def,STATES_def,SET_SPEC]
		      THEN REPEAT STRIP_TAC
		      THEN (SUBGOAL_THEN ``!(n:num) (s: 'state) . (s :'state) IN
		      FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
		      (e :string -> 'state -> bool)[[[Q<--{}]]] n = s IN FP f Q (ks: ('prop,'state) KS)
								  (e' :string -> 'state -> bool)[[[Q<--{}]]] n``
								  (fn th => ASSUM_LIST (fn t => PROVE_TAC (th::t))))
		      THEN Induct_on `n`
		      THENL [SIMP_TAC std_ss [STATES_def,ENV_UPDATE_def,NOT_IN_EMPTY],
			     FULL_SIMP_TAC std_ss [IN_DEF,STATES_def,SYM (ISPECL [`` FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
										     (e :string -> 'state -> bool)[[[Q<--{}]]]
										     (n :num)``,``FP (f :'prop mu) (Q :string)
										     (ks :('prop,'state) KS)
										     (e':string -> 'state -> bool)[[[Q<--{}]]]
										     (n :num)``] FUN_EQ_THM),ENV_UPDATE]]))

val SAT_LFP_ENV_INV2 =
    save_thm("SAT_LFP_ENV_INV2",
	     prove(``!(ks:('prop,'state) KS)  Q f e e'. (!X. MU_SAT f ks e[[[Q<--X]]] = MU_SAT f ks e'[[[Q<--X]]])
		      ==> (MU_SAT (mu Q.. f) ks e = MU_SAT (mu Q .. f) ks e')``,
		      REPEAT STRIP_TAC
		      THEN CONV_TAC FUN_EQ_CONV
		      THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META2,MU_SAT_def,STATES_def,SET_SPEC]
		      THEN REPEAT STRIP_TAC
		      THEN (SUBGOAL_THEN ``!(n:num) (s: 'state) . (s :'state) IN
		      FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
		      (e :string -> 'state -> bool)[[[Q<--{}]]] n = s IN FP f Q (ks: ('prop,'state) KS)
								  (e' :string -> 'state -> bool)[[[Q<--{}]]] n``
								  (fn th => ASSUM_LIST (fn t => PROVE_TAC (th::t))))
		      THEN Induct_on `n`
		      THENL [SIMP_TAC std_ss [STATES_def,ENV_UPDATE_def,NOT_IN_EMPTY],
			     FULL_SIMP_TAC std_ss [IN_DEF,STATES_def,SYM (ISPECL [`` FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
										     (e :string -> 'state -> bool)[[[Q<--{}]]]
										     (n :num)``,``FP (f :'prop mu) (Q :string)
										     (ks :('prop,'state) KS)
										     (e':string -> 'state -> bool)[[[Q<--{}]]]
										     (n :num)``] FUN_EQ_THM),ENV_UPDATE]]))

val SAT_GFP_ENV_INV =
    save_thm("SAT_GFP_ENV_INV",
	     prove(``!(ks:('prop,'state) KS)  s Q f e e'. (!s X e e'. MU_SAT f ks e[[[Q<--X]]] s = MU_SAT f ks e'[[[Q<--X]]] s)
		      ==> (MU_SAT (nu Q.. f) ks e s = MU_SAT (nu Q .. f) ks e' s)``,
		      SIMP_TAC std_ss [MU_SAT_def,STATES_def,SET_SPEC]
		      THEN REPEAT STRIP_TAC
		      THEN (SUBGOAL_THEN ``!(n:num) (s: 'state) . (s :'state) IN
		      FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
		      (e :string -> 'state -> bool)[[[Q<--ks.S]]] n = s IN FP f Q (ks: ('prop,'state) KS)
								  (e' :string -> 'state -> bool)[[[Q<--ks.S]]] n``
								  (fn th => ASSUM_LIST (fn t => PROVE_TAC (th::t))))
		      THEN Induct_on `n`
		      THENL [SIMP_TAC std_ss [STATES_def,ENV_UPDATE_def,NOT_IN_EMPTY],
			     FULL_SIMP_TAC std_ss [IN_DEF,STATES_def,SYM (ISPECL [`` FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
										   (e :string -> 'state -> bool)[[[Q<--ks.S]]]
										   (n :num)``,``FP (f :'prop mu) (Q :string)
										   (ks :('prop,'state) KS)
										   (e':string -> 'state -> bool)[[[Q<--ks.S]]]
										   (n :num)``] FUN_EQ_THM),ENV_UPDATE]]))

val SAT_GFP_ENV_INV2 =
    save_thm("SAT_GFP_ENV_INV2",
	     prove(``!(ks:('prop,'state) KS)  Q f e e'. (!X. MU_SAT f ks e[[[Q<--X]]] = MU_SAT f ks e'[[[Q<--X]]])
		      ==> (MU_SAT (nu Q.. f) ks e = MU_SAT (nu Q .. f) ks e')``,
		      REPEAT STRIP_TAC
		      THEN CONV_TAC FUN_EQ_CONV
		      THEN FULL_SIMP_TAC std_ss [SAT_ENV_INV_META2,MU_SAT_def,STATES_def,SET_SPEC]
		      THEN REPEAT STRIP_TAC
		      THEN (SUBGOAL_THEN ``!(n:num) (s: 'state) . (s :'state) IN
		      FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
		      (e :string -> 'state -> bool)[[[Q<--ks.S]]] n = s IN FP f Q (ks: ('prop,'state) KS)
								  (e' :string -> 'state -> bool)[[[Q<--ks.S]]] n``
								  (fn th => ASSUM_LIST (fn t => PROVE_TAC (th::t))))
		      THEN Induct_on `n`
		      THENL [SIMP_TAC std_ss [STATES_def,ENV_UPDATE_def,NOT_IN_EMPTY],
			     FULL_SIMP_TAC std_ss [IN_DEF,STATES_def,SYM (ISPECL [`` FP (f :'prop mu) (Q :string) (ks :('prop,'state) KS)
										   (e :string -> 'state -> bool)[[[Q<--ks.S]]]
										   (n :num)``,``FP (f :'prop mu) (Q :string)
										   (ks :('prop,'state) KS)
										   (e':string -> 'state -> bool)[[[Q<--ks.S]]]
										   (n :num)``] FUN_EQ_THM),ENV_UPDATE]]))


(* thms used by checker for ado *)

val STATES_LFP_2_LEM = prove(``!f ks e P X Y Q.
         IMF (mu Q.. f) /\ IMF (mu P.. f) /\ wfKS ks /\ X SUBSET Y ==> STATES f ks e[[[P<--X]]][[[Q<--{}]]] SUBSET
         STATES f ks e[[[P<--Y]]][[[Q<--{}]]]``,
REPEAT STRIP_TAC
THEN Q.SUBGOAL_THEN `(!Q'.
            (if ~RV Q' SUBF NNF f then
               e[[[P<--X]]] Q' = e[[[P<--Y]]] Q' else e[[[P<--X]]] Q' SUBSET e[[[P<--Y]]] Q'))` ASSUME_TAC THENL [
FULL_SIMP_TAC std_ss [IMF_def]
THEN GEN_TAC
THEN Cases_on `Q'=P` THENL [
FULL_SIMP_TAC std_ss [ENV_EVAL],
IMP_RES_TAC (INST_TYPE [alpha|->beta] ENV_UPDATE_INV)
THEN Cases_on `~RV Q' SUBF NNF f` THENL [
FULL_SIMP_TAC std_ss [],
FULL_SIMP_TAC std_ss [SUBSET_REFL]]],
ASSUM_LIST (fn t=> METIS_TAC (STATES_MONO::SUBSET_REFL::t))])

val STATES_LFP_2 = prove(``!f ks e P X Y Q. IMF (mu Q..f) /\ IMF (mu P.. f) /\ wfKS ks /\ X SUBSET Y  ==> (!n. FP f Q ks e[[[P<--X]]][[[Q<--{}]]] n SUBSET FP f Q ks e[[[P<--Y]]][[[Q<--{}]]] n)``,
REPEAT STRIP_TAC
THEN `!e. STATES f ks e[[[P<--X]]][[[Q<--{}]]] SUBSET STATES f ks e[[[P<--Y]]][[[Q<--{}]]]` by IMP_RES_TAC STATES_LFP_2_LEM
THEN POP_ASSUM (fn t => ASSUME_TAC (Q.SPEC `e` t))
THEN Cases_on `P=Q` THENL [
POP_ASSUM (fn t => ASSUME_TAC (SYM t))
THEN FULL_SIMP_TAC std_ss [ENV_UPDATE,SUBSET_REFL],
IMP_RES_TAC (INST_TYPE [alpha|->beta] ENV_SWAP)
THEN Q.PAT_ASSUM `t SUBSET t'`  MP_TAC
THEN ASM_REWRITE_TAC []
THEN Q.SPEC_TAC (`e[[[Q<--{}]]]`,`e`)
THEN POP_ASSUM (fn _ => ALL_TAC)
THEN POP_ASSUM (fn t => ASSUME_TAC (CONV_RULE (RAND_CONV SYM_CONV) t))
THEN REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
FULL_SIMP_TAC std_ss [STATES_def,ENV_UPDATE,ENV_UPDATE_INV,SUBSET_REFL],
SIMP_TAC std_ss [STATES_def,ENV_EVAL,ENV_UPDATE]
THEN Q.SUBGOAL_THEN `(!Q'.
            (if ~RV Q' SUBF NNF f then
               e[[[P<--X]]] Q' = e[[[P<--Y]]] Q' else e[[[P<--X]]] Q' SUBSET e[[[P<--Y]]] Q'))` ASSUME_TAC THENL [
FULL_SIMP_TAC std_ss [IMF_def]
THEN GEN_TAC
THEN Cases_on `Q'=P` THENL [
FULL_SIMP_TAC std_ss [ENV_EVAL],
IMP_RES_TAC (INST_TYPE [alpha|->beta] ENV_UPDATE_INV)
THEN Cases_on `~RV Q' SUBF NNF f` THENL [
FULL_SIMP_TAC std_ss [],
FULL_SIMP_TAC std_ss [SUBSET_REFL]]],
IMP_RES_TAC STATES_MONO
]]])

val STATES_FP_BIGUNION_2 =  save_thm("STATES_FP_BIGUNION_2",prove(``!f ks e Q1 X Y Q. IMF (mu Q..f) /\ IMF (mu Q1.. f) /\ wfKS ks /\ X SUBSET Y  ==> BIGUNION {P | ?n. (P = FP f Q ks e[[[Q1<--X]]][[[Q<--{}]]] n)} SUBSET BIGUNION {P | ?n. (P = FP f Q ks e[[[Q1<--Y]]][[[Q<--{}]]] n)}``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,SET_SPEC,SUBSET_DEF]
THEN REPEAT STRIP_TAC
THEN RW_TAC std_ss []
THEN Q.EXISTS_TAC `FP f Q ks e[[[Q1<--Y]]][[[Q<--{}]]] n`
THEN CONV_TAC LEFT_AND_EXISTS_CONV
THEN Q.EXISTS_TAC `n`
THEN REWRITE_TAC []
THEN POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`x`,`x`)
THEN REWRITE_TAC [GSYM SUBSET_DEF]
THEN METIS_TAC [STATES_LFP_2]))

val GEN_STATES_LFP =  prove(``!f ks e e' Q. wfKS ks /\ IMF (mu Q.. f) /\
         (!Q'. (if ~RV Q' SUBF NNF f then e Q' = e' Q' else e Q' SUBSET e' Q')) ==>
			    (!n. FP f Q ks e[[[Q<--{}]]] n SUBSET FP f Q ks e'[[[Q<--{}]]] n)``,
REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
FULL_SIMP_TAC std_ss [STATES_def,ENV_UPDATE,SUBSET_REFL,ENV_EVAL],
FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,ENV_UPDATE]
THEN METIS_TAC [STATES_MONO,SUBSET_REFL]])

val GEN_STATES_FP_BIGUNION = save_thm("GEN_STATES_FP_BIGUNION",prove(``!f ks e e' Q.  wfKS ks /\ IMF (mu Q.. f) /\
         (!Q'. (if ~RV Q' SUBF NNF f then e Q' = e' Q' else e Q' SUBSET e' Q')) ==>
		  BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)} SUBSET BIGUNION {P | ?n. (P = FP f Q ks e'[[[Q<--{}]]] n)}``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,SET_SPEC,SUBSET_DEF]
THEN REPEAT STRIP_TAC
THEN RW_TAC std_ss []
THEN Q.EXISTS_TAC `FP f Q ks e'[[[Q<--{}]]] n`
THEN CONV_TAC LEFT_AND_EXISTS_CONV
THEN Q.EXISTS_TAC `n`
THEN REWRITE_TAC []
THEN POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`x`,`x`)
THEN REWRITE_TAC [GSYM SUBSET_DEF]
THEN METIS_TAC [GEN_STATES_LFP]))

val STATES_DEF_SYM_MU = save_thm("STATES_DEF_SYM_MU",prove(``!f ks e Q n. STATES f ks e[[[Q<--FP f Q ks e[[[Q<--{}]]] n]]] = FP f Q ks e[[[Q<--{}]]] (SUC n)``,SIMP_TAC std_ss [STATES_def,ENV_UPDATE]))

val STATES_GFP_2_LEM = prove(``!f ks e P X Y Q.
         IMF (nu Q.. f) /\ IMF (nu P.. f) /\ wfKS ks /\ X SUBSET Y ==> STATES f ks e[[[P<--X]]][[[Q<--ks.S]]] SUBSET
         STATES f ks e[[[P<--Y]]][[[Q<--ks.S]]]``,
REPEAT STRIP_TAC
THEN Q.SUBGOAL_THEN `(!Q'.
            (if ~RV Q' SUBF NNF f then
               e[[[P<--X]]] Q' = e[[[P<--Y]]] Q' else e[[[P<--X]]] Q' SUBSET e[[[P<--Y]]] Q'))` ASSUME_TAC THENL [
FULL_SIMP_TAC std_ss [IMF_def]
THEN GEN_TAC
THEN Cases_on `Q'=P` THENL [
FULL_SIMP_TAC std_ss [ENV_EVAL],
IMP_RES_TAC (INST_TYPE [alpha|->beta] ENV_UPDATE_INV)
THEN Cases_on `~RV Q' SUBF NNF f` THENL [
FULL_SIMP_TAC std_ss [],
FULL_SIMP_TAC std_ss [SUBSET_REFL]]],
FULL_SIMP_TAC std_ss [GSYM IMF_MU_IFF_IMF_NU]
THEN ASSUM_LIST (fn t=> METIS_TAC (STATES_MONO::SUBSET_REFL::t))])

val STATES_GFP_2 = prove(``!f ks e P X Y Q. IMF (nu Q..f) /\ IMF (nu P.. f) /\ wfKS ks /\ X SUBSET Y  ==> (!n. FP f Q ks e[[[P<--X]]][[[Q<--ks.S]]] n SUBSET FP f Q ks e[[[P<--Y]]][[[Q<--ks.S]]] n)``,
REPEAT STRIP_TAC
THEN `!e. STATES f ks e[[[P<--X]]][[[Q<--ks.S]]] SUBSET STATES f ks e[[[P<--Y]]][[[Q<--ks.S]]]` by IMP_RES_TAC STATES_GFP_2_LEM
THEN POP_ASSUM (fn t => ASSUME_TAC (Q.SPEC `e` t))
THEN Cases_on `P=Q` THENL [
POP_ASSUM (fn t => ASSUME_TAC (SYM t))
THEN FULL_SIMP_TAC std_ss [ENV_UPDATE,SUBSET_REFL],
IMP_RES_TAC (INST_TYPE [alpha|->beta] ENV_SWAP)
THEN Q.PAT_ASSUM `t SUBSET t'`  MP_TAC
THEN ASM_REWRITE_TAC []
THEN Q.SPEC_TAC (`e[[[Q<--ks.S]]]`,`e`)
THEN POP_ASSUM (fn _ => ALL_TAC)
THEN POP_ASSUM (fn t => ASSUME_TAC (CONV_RULE (RAND_CONV SYM_CONV) t))
THEN REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
FULL_SIMP_TAC std_ss [STATES_def,ENV_UPDATE,ENV_UPDATE_INV,SUBSET_REFL],
SIMP_TAC std_ss [STATES_def,ENV_EVAL,ENV_UPDATE]
THEN Q.SUBGOAL_THEN `(!Q'.
            (if ~RV Q' SUBF NNF f then
               e[[[P<--X]]] Q' = e[[[P<--Y]]] Q' else e[[[P<--X]]] Q' SUBSET e[[[P<--Y]]] Q'))` ASSUME_TAC THENL [
FULL_SIMP_TAC std_ss [IMF_def]
THEN GEN_TAC
THEN Cases_on `Q'=P` THENL [
FULL_SIMP_TAC std_ss [ENV_EVAL],
IMP_RES_TAC (INST_TYPE [alpha|->beta] ENV_UPDATE_INV)
THEN Cases_on `~RV Q' SUBF NNF f` THENL [
FULL_SIMP_TAC std_ss [],
FULL_SIMP_TAC std_ss [SUBSET_REFL]]],
FULL_SIMP_TAC std_ss [GSYM IMF_MU_IFF_IMF_NU]
THEN IMP_RES_TAC STATES_MONO
]]])


val STATES_FP_BIGINTER_2 =  save_thm("STATES_FP_BIGINTER_2",prove(``!f ks e Q1 X Y Q. IMF (nu Q..f) /\ IMF (nu Q1.. f) /\ wfKS ks /\ X SUBSET Y  ==> BIGINTER {P | ?n. (P = FP f Q ks e[[[Q1<--X]]][[[Q<--ks.S]]] n)} SUBSET BIGINTER {P | ?n. (P = FP f Q ks e[[[Q1<--Y]]][[[Q<--ks.S]]] n)}``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGINTER,SET_SPEC,SUBSET_DEF]
THEN REPEAT STRIP_TAC
THEN PAT_ASSUM ``!x. t`` (fn t => ASSUME_TAC (CONV_RULE ((QUANT_CONV LEFT_IMP_EXISTS_CONV) THENC SWAP_VARS_CONV) t))
THEN POP_ASSUM  (fn t => ASSUME_TAC (Q.SPECL [`n`,`FP f Q ks e[[[Q1<--X]]][[[Q<--ks.S]]] n`] t))
THEN RW_TAC std_ss []
THEN POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`x`,`x`)
THEN REWRITE_TAC [GSYM SUBSET_DEF]
THEN METIS_TAC [STATES_GFP_2]))

val GEN_STATES_GFP =  prove(``!f ks e e' Q.wfKS ks /\ IMF (nu Q.. f) /\
         (!Q'. (if ~RV Q' SUBF NNF f then e Q' = e' Q' else e Q' SUBSET e' Q'))  ==>
			    (!n. FP f Q ks e[[[Q<--ks.S]]] n SUBSET FP f Q ks e'[[[Q<--ks.S]]] n)``,
REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
FULL_SIMP_TAC std_ss [STATES_def,ENV_UPDATE,SUBSET_REFL,ENV_EVAL],
FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,ENV_UPDATE,GSYM IMF_MU_IFF_IMF_NU]
THEN METIS_TAC [STATES_MONO,SUBSET_REFL]])

val GEN_STATES_FP_BIGINTER =  save_thm("GEN_STATES_FP_BIGINTER",prove(``!f ks e e' Q. wfKS ks /\ IMF (nu Q.. f) /\
         (!Q'. (if ~RV Q' SUBF NNF f then e Q' = e' Q' else e Q' SUBSET e' Q'))  ==>
         BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} SUBSET BIGINTER {P | ?n. (P = FP f Q ks e'[[[Q<--ks.S]]] n)}``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGINTER,SET_SPEC,SUBSET_DEF]
THEN REPEAT STRIP_TAC
THEN PAT_ASSUM ``!x. t`` (fn t => ASSUME_TAC (CONV_RULE ((QUANT_CONV LEFT_IMP_EXISTS_CONV) THENC SWAP_VARS_CONV) t))
THEN POP_ASSUM  (fn t => ASSUME_TAC (Q.SPECL [`n`,`FP f Q ks e[[[Q<--ks.S]]] n`] t))
THEN RW_TAC std_ss []
THEN POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`x`,`x`)
THEN REWRITE_TAC [GSYM SUBSET_DEF]
THEN METIS_TAC [GEN_STATES_GFP]))

val STATES_DEF_SYM_NU = save_thm("STATES_DEF_SYM_NU",prove(``!f ks e Q n. STATES f ks e[[[Q<--FP f Q ks e[[[Q<--ks.S]]] n]]] = FP f Q ks e[[[Q<--ks.S]]] (SUC n)``,SIMP_TAC std_ss [STATES_def,ENV_UPDATE]))

val _ = export_theory()