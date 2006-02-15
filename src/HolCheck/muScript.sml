

(* Useful in interactive sessions:
app load ["bossLib","stringTheory","stringLib","HolBddLib","pairTheory","pred_setLib","listLib","boolSimps","pairSimps","combinSimps",
          "optionSimps", "numSimps", "listSimps","pairTools","pairLib","pairSyntax","pred_setTheory","sumTheory","ksTheory","numLib",
	  "setLemmasTheory"];
*)


open HolKernel Parse boolLib bossLib

val _ = new_theory("mu")


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

infix &&; infix 8 by;

fun tsimps ty = let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end


(* semantics of mu-calc: [|formula|]_{ks,e} = set of states in which formula is true, for a given (k)ripke (s)tructure and (e)nv *)

(* set of states of ks in which f is true, under the environment e *)
val sdefn = Hol_defn "STATES" `
	(STATES TR (ks:('prop,'state) KS) (e:string -> ('state -> bool)) = (ks.S)) /\
	(STATES FL ks e  = {}) /\
	(STATES (AP p) ks e = {s | (s IN (ks.S)) /\ (p IN ((ks.L) s))} ) /\
	(STATES (RV Q) ks e = {s | (s IN (ks.S)) /\ ((e Q)s) }) /\
	(STATES (~f) ks e = ( (ks.S) DIFF (STATES f ks e))) /\
	(STATES (f \/ g) ks e = (STATES f ks e) UNION (STATES g ks e)) /\
	(STATES (f /\ g) ks e = (STATES f ks e) INTER (STATES g ks e)) /\
	(STATES (<<a>> f) ks e = { s | ?q.((q IN (ks.S)) /\ (s>--ks/a-->q /\  (q IN (STATES f ks e)))) } ) /\
	(STATES ([[a]] f) ks e = { s | !q.((q IN (ks.S)) /\ (s>--ks/a-->q ==> (q IN (STATES f ks e)))) } ) /\
	(STATES (nu Q .. f) ks e = {s | !n. s IN FP f Q ks e[[[Q <-- ks.S]]] n}) /\
	(STATES (mu Q .. f) ks e = {s | ?n. s IN FP f Q ks e[[[Q <-- {}]]] n}) /\
        (FP f Q ks e 0 = e Q) /\
        (FP f Q ks e (SUC n) = STATES f ks e[[[Q <-- FP f Q ks e n]]])`

val (STATES_def,STATES_IND_def) = Defn.tprove(sdefn,(WF_REL_TAC `inv_image ($< LEX $<) (\v.if (ISL v) then(mu_size2(FST(OUTL v)),0) else (mu_size2(FST(OUTR v)), SND(SND(SND(SND(OUTR v))))))`) THEN (RW_TAC std_ss [sumTheory.ISL,sumTheory.OUTL,sumTheory.OUTR]) THEN RW_TAC arith_ss [mu_size_def,mu_size2_def])
val _ = save_thm("STATES_def",STATES_def)


val MU_SAT_def = save_thm("MU_SAT_def",Define `MU_SAT f ks e s = s IN STATES f ks e`)

val MU_MODEL_SAT_def = Define `MU_MODEL_SAT f ks e = (!s. s IN ks.S0 ==> MU_SAT f ks e s)`

(* thms about state sets *)

val STATES_SUBSET = prove(``!f ks e. wfKS ks ==> STATES f ks e SUBSET ks.S``,RW_TAC std_ss [wfKS_def,SUBSET_DEF,IN_UNIV])

val MU_BIGUNION = save_thm("MU_BIGUNION",prove(``!f ks e Q. wfKS ks
					       ==> (STATES (mu Q.. f) ks e = BIGUNION { P | ?n. P = FP f Q ks e[[[Q<--{}]]] n})``,
RW_TAC std_ss [wfKS_def,STATES_def,BIGUNION,SET_SPEC,IN_UNIV,EXTENSION,ENV_UPDATE_def] THEN PROVE_TAC []))

val NU_BIGINTER = save_thm("NU_BIGINTER",prove(``!f ks e Q. wfKS ks
				   ==> (STATES (nu Q.. f) ks e = BIGINTER { P | ?n. P = FP f Q ks e[[[Q<--ks.S]]]  n})``,
RW_TAC std_ss [wfKS_def,STATES_def,BIGINTER,SET_SPEC,IN_UNIV,EXTENSION,ENV_UPDATE_def] THEN PROVE_TAC []))

val env3 = prove(``!f (ks:('prop,'state) KS) (e:string -> 'state -> bool) Q (s:'state ->bool).
(!(e:string -> 'state -> bool) Q (s:'state -> bool). (STATES (RVNEG Q f) ks e[[[Q <-- UNIV DIFF s]]] =  STATES f ks e[[[Q <-- s]]])) ==>
       (!n Q' X. ~(Q=Q') ==> (FP (RVNEG Q f) Q' ks e[[[Q <-- UNIV DIFF s]]][[[Q'<--X]]] n = FP f Q' ks e[[[Q<--s]]][[[Q'<--X]]] n))``,
RW_TAC std_ss [] THEN Induct_on `n` THENL
[RW_TAC std_ss [STATES_def,ENV_UPDATE_def],
 RW_TAC std_ss [STATES_def,ENV_UPDATE]
 THEN Q.SPEC_TAC (`FP f Q' ks e[[[Q<--s]]][[[Q'<--X]]] n`,`Z`)
 THEN PAT_ASSUM ``~t`` (fn t=> RW_TAC std_ss [t,ENV_SWAP])])

val RV_NEG_NEG = prove(``!ks. wfKS ks ==> (!f e Q s. STATES (RVNEG Q f) ks e[[[Q <-- UNIV DIFF s]]] =  STATES f ks e[[[Q <-- s]]])``,
REWRITE_TAC [wfKS_def] THEN GEN_TAC THEN DISCH_TAC THEN Induct_on `f` THENL [
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* T *)
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* F *)
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* ~ *)
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* /\ *)
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* \/ *)
REWRITE_TAC [STATES_def,RVNEG_def,ENV_UPDATE_def] THEN REPEAT STRIP_TAC THEN Cases_on `Q=s` THENL [
RW_TAC std_ss [STATES_def,wfKS_def,EXTENSION,SET_SPEC,IN_UNIV,DIFF_DEF]
THEN RW_TAC std_ss [SET_GSPEC,SPECIFICATION],
RW_TAC std_ss [IN_UNIV,DIFF_DEF,EXTENSION,SET_SPEC,SET_GSPEC,SPECIFICATION]
THEN RW_TAC std_ss [STATES_def]
THEN RW_TAC std_ss [UNIV_DEF,DIFF_DEF,EXTENSION,SET_SPEC,SET_GSPEC,SPECIFICATION]], (* RV *)
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* AP *)
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* << >> *)
RW_TAC std_ss [STATES_def,RVNEG_def,wfKS_def], (* [[ ]] *)
RW_TAC std_ss [RVNEG_def,wfKS_def]  THENL [
RW_TAC std_ss [STATES_def,EXTENSION,SET_SPEC,SET_GSPEC,SPECIFICATION,ENV_UPDATE_def],
RW_TAC std_ss [STATES_def,EXTENSION,SET_SPEC]
THEN RW_TAC std_ss [IN_DEF]
THEN ASSUM_LIST (fn t => RW_TAC std_ss (env3::t))], (* mu *)
RW_TAC std_ss [RVNEG_def,wfKS_def] THENL [
RW_TAC std_ss [STATES_def,EXTENSION,SET_SPEC,SET_GSPEC,SPECIFICATION,ENV_UPDATE_def],
RW_TAC std_ss [STATES_def,EXTENSION,SET_SPEC]
THEN RW_TAC std_ss [IN_DEF]
THEN ASSUM_LIST (fn t => RW_TAC std_ss (env3::t))]] (* nu *))

val MU_FP_NEG_NEG = prove(``!ks. wfKS ks ==> (!n f e Q. (FP (~(RVNEG Q f)) Q ks e[[[Q<--ks.S]]] n = UNIV DIFF FP f Q ks e[[[Q<--{}]]] n))``,
GEN_TAC THEN DISCH_TAC THEN Induct_on `n` THENL [
RW_TAC std_ss [STATES_def,wfKS_def,DIFF_EMPTY,ENV_UPDATE_def]
THEN ASSUM_LIST (fn t => PROVE_TAC (wfKS_def::t)), (* n = 0 *)
RW_TAC std_ss [STATES_def,wfKS_def]
THEN REWRITE_TAC [UNIV_DIFF_EQ]
THEN REWRITE_TAC [ENV_UPDATE]
THEN ASSUM_LIST (fn t => PROVE_TAC (RV_NEG_NEG::wfKS_def::t))])


val NU2MU_LEMMA = prove(``!ks. wfKS ks ==> (!f e Q. STATES (nu Q.. ~(RVNEG Q f)) ks e =
                                 BIGINTER { P | ?n. P = UNIV DIFF (FP f Q ks e[[[Q<--{}]]] n)})``,
RW_TAC std_ss [MU_FP_NEG_NEG,NU_BIGINTER])

val NEG_OVER_MU = prove(``!ks. wfKS ks ==> (!f e Q. STATES (~(mu Q.. f)) ks e = STATES (nu Q.. ~(RVNEG Q f)) ks e)``,
FULL_SIMP_TAC std_ss [NU2MU_LEMMA]
THEN ONCE_REWRITE_TAC [STATES_def]
THEN RW_TAC std_ss [wfKS_def,MU_BIGUNION]
THEN RW_TAC std_ss [DIFF_OVER_BIGUNION])

val NU_FP_NEG_NEG = prove (``!ks. wfKS ks ==> (!n f e Q. (FP (~(RVNEG Q f)) Q ks e[[[Q<--{}]]] n = UNIV DIFF FP f Q ks e[[[Q<--ks.S]]] n))``,
REWRITE_TAC [wfKS_def] THEN GEN_TAC THEN DISCH_TAC
THEN ASM_REWRITE_TAC [] THEN Induct_on `n` THENL [
RW_TAC std_ss [STATES_def,wfKS_def,DIFF_EMPTY,ENV_UPDATE_def]
THEN RW_TAC std_ss [DIFF_DEF,IN_UNIV,EXTENSION,SET_SPEC,NOT_IN_EMPTY], (* n = 0 *)
RW_TAC std_ss [STATES_def,wfKS_def]
THEN REWRITE_TAC [UNIV_DIFF_EQ]
THEN REWRITE_TAC [ENV_UPDATE]
THEN ASSUM_LIST (fn t => PROVE_TAC (RV_NEG_NEG::wfKS_def::t))])

val MU2NU_LEMMA = prove(``!ks. wfKS ks ==> (!f e Q. STATES (mu Q.. ~(RVNEG Q f)) ks e =
                                 BIGUNION { P | ?n. P = UNIV DIFF (FP f Q ks e[[[Q<--ks.S]]] n)})``,
RW_TAC std_ss [NU_FP_NEG_NEG,MU_BIGUNION])

val NEG_OVER_NU = prove(``!ks. wfKS ks ==> (!f e Q. STATES (~(nu Q.. f)) ks e = STATES (mu Q.. ~(RVNEG Q f)) ks e)``,
FULL_SIMP_TAC std_ss [MU2NU_LEMMA]
THEN ONCE_REWRITE_TAC [STATES_def]
THEN RW_TAC std_ss [wfKS_def,NU_BIGINTER]
THEN RW_TAC std_ss [DIFF_OVER_BIGINTER])

val STATES_FP_EQ = prove(``!ks. (!f g. (!e. STATES f ks e = STATES g ks e) ==> (!n e Q. FP f Q ks e n = FP g Q ks e n))``,
GEN_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC
THEN Induct_on `n` THENL [
RW_TAC std_ss [STATES_def,SUBSET_DEF],
FULL_SIMP_TAC std_ss [STATES_def,SUBSET_DEF]])


val NU_STATES  = prove (``!ks. wfKS ks ==> (!f g e. (!e. STATES f ks e = STATES g ks e) ==> (STATES (nu Q.. f) ks e = STATES (nu Q.. g) ks e))``, RW_TAC std_ss  [BIGINTER_LEMMA1,STATES_FP_EQ,NU_BIGINTER])

val MU_STATES = prove(``!ks. wfKS ks ==> (!f g e. (!e. STATES f ks e = STATES g ks e) ==> (STATES (mu Q.. f) ks e = STATES (mu Q.. g) ks e))``, RW_TAC std_ss  [BIGUNION_LEMMA1,STATES_FP_EQ,MU_BIGUNION])

val STATES_NNF_ID = save_thm("STATES_NNF_ID",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e. wfKS ks ==> (STATES (NNF f) ks e = STATES f ks e)``,
recInduct NNF_IND_def THEN RW_TAC std_ss [wfKS_def] THENL [ (* 21 subgoals *)
RW_TAC std_ss [NNF_def,STATES_def], (* T *)
RW_TAC std_ss [NNF_def,STATES_def], (* F *)
RW_TAC std_ss [NNF_def,STATES_def], (* /\ *)
RW_TAC std_ss [NNF_def,STATES_def], (* \/ *)
RW_TAC std_ss [NNF_def,STATES_def], (* <> *)
RW_TAC std_ss [NNF_def,STATES_def], (* [] *)
RW_TAC std_ss [NNF_def,STATES_def], (* AP *)
RW_TAC std_ss [NNF_def,STATES_def], (* RV *)
ASSUM_LIST (fn t => RW_TAC std_ss (MU_STATES::NNF_def::wfKS_def::t)), (* mu *)
ASSUM_LIST (fn t => RW_TAC std_ss (NU_STATES::NNF_def::wfKS_def::t)), (* nu *)
RW_TAC std_ss [NNF_def,STATES_def,DIFF_EQ_EMPTY], (* ~T *)
RW_TAC std_ss [NNF_def,STATES_def,DIFF_EMPTY], (* ~F *)
REPEAT STRIP_TAC THEN REWRITE_TAC [NNF_def,STATES_def]
THEN ASSUM_LIST (fn t=> RW_TAC std_ss (STATES_def::STATES_SUBSET::DIFF_OVER_INTER::wfKS_def::t)), (* ~ /\ *)
REPEAT STRIP_TAC THEN REWRITE_TAC [NNF_def,STATES_def]
THEN ASSUM_LIST (fn t=> RW_TAC std_ss (STATES_def::STATES_SUBSET::DIFF_OVER_UNION::wfKS_def::t)), (* ~\/ *)
RW_TAC std_ss [NNF_def], (* ~AP *)
RW_TAC std_ss [NNF_def], (* ~RV *)
RW_TAC std_ss [STATES_def,NNF_def,DIFF_DEF,IN_UNIV,SET_SPEC,EXTENSION] THEN PROVE_TAC [], (* ~<> *)
RW_TAC std_ss [STATES_def,NNF_def,DIFF_DEF,IN_UNIV,SET_SPEC,EXTENSION] THEN PROVE_TAC [], (* ~[] *)
RW_TAC std_ss [STATES_def,NNF_def,IN_UNIV,DIFF_DEF,SET_SPEC,EXTENSION], (* ~~ *)
ASSUM_LIST (fn t => RW_TAC std_ss (NNF_def::wfKS_def::NEG_OVER_MU::t))
THEN REWRITE_TAC [SYM (SPECL [``Q:string``,``f:'prop mu``] (List.last (CONJUNCTS RVNEG_def)))]
THEN ASSUM_LIST (fn t => RW_TAC std_ss (wfKS_def::NU_STATES::t)), (* ~mu *)
ASSUM_LIST (fn t => RW_TAC std_ss (NNF_def::wfKS_def::NEG_OVER_NU::t))
THEN REWRITE_TAC [SYM (SPECL [``Q:string``,``f:'prop mu``] (List.last (CONJUNCTS RVNEG_def)))]
THEN ASSUM_LIST (fn t => RW_TAC std_ss (wfKS_def::MU_STATES::t))])) (* ~nu *)

val MU_FP_LEMMA = prove(``(!n. FP (f:'prop mu) Q (ks:('prop,'state) KS)  e[[[Q<--{}]]] n SUBSET FP f Q ks e'[[[Q<--{}]]] n) ==>
    !x. (?n. x IN FP f Q ks e[[[Q<--{}]]] n) ==> ?n. x IN FP f Q ks e'[[[Q<--{}]]] n``,
PROVE_TAC [SUBSET_DEF])

val MU_NEG_FP_LEMMA = prove (``(!n. FP (f:'prop mu) Q (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--{}]]] n SUBSET FP f Q ks e[[[Q'<--X]]][[[Q<--{}]]] n) ==>
    ((?n. x IN FP f Q ks e'[[[Q'<--Y]]][[[Q<--{}]]] n) ==> ?n. x IN FP f Q ks e[[[Q'<--X]]][[[Q<--{}]]] n)``,
PROVE_TAC [SUBSET_DEF])

(* thms about satisfiability *)

val MU_SAT_NEG =  save_thm("MU_SAT_NEG",prove(``!s ks e. (wfKS ks ==> (!f. (MU_SAT (~f) ks e s = ~MU_SAT f ks e s)))``,
			     REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
			     [RW_TAC std_ss [MU_SAT_def,STATES_def,DIFF_DEF,IN_UNIV,SET_SPEC],
			     RW_TAC std_ss [MU_SAT_def,STATES_def,DIFF_DEF,IN_UNIV,SET_SPEC]
			     THEN PROVE_TAC [IN_UNIV,wfKS_def]]))

val MU_SAT_CONJ = save_thm("MU_SAT_CONJ",prove(``!s ks e. (wfKS ks ==> (!f g. (MU_SAT (f:'prop mu /\ g) ks e s = (MU_SAT f ks e s) /\ (MU_SAT g ks e s))))``,
			     RW_TAC std_ss [wfKS_def,INTER_DEF,MU_SAT_def,STATES_def,SET_SPEC_CONV ``s IN {x | x IN STATES f ks e /\ x IN STATES g ks e}``]))


val MU_SAT_DISJ = save_thm("MU_SAT_DISJ",prove (``!s ks e. (wfKS ks ==> (!f g.(MU_SAT (f:'prop mu \/ g) ks e s = (MU_SAT f ks e s) \/ (MU_SAT g ks e s))))``,
                         RW_TAC std_ss [wfKS_def,UNION_DEF,MU_SAT_def,STATES_def,SET_SPEC_CONV ``s IN {x | x IN STATES f ks e \/ x IN STATES g ks e}``]))

val MU_SAT_T = save_thm("MU_SAT_T",prove(``!s ks e. (wfKS ks ==> ((MU_SAT TR ks e s) = T))``,
			  RW_TAC std_ss [wfKS_def,IN_UNIV,MU_SAT_def,STATES_def]))


val MU_SAT_F = save_thm("MU_SAT_F",prove(``!s ks e. (wfKS ks ==> ((MU_SAT FL ks e s) = F))``,
			  RW_TAC std_ss [wfKS_def,NOT_IN_EMPTY,MU_SAT_def,STATES_def]))

val MU_SAT_DMD = save_thm("MU_SAT_DMD",prove(``!s ks e.  (wfKS ks ==> (!a f. MU_SAT (<<a>> f) ks e s = ?q. (ks.T a)(s,q) /\ MU_SAT f ks e q))``, RW_TAC std_ss [MU_SAT_def,STATES_def,KS_TRANSITION_def,SET_SPEC,wfKS_def,IN_UNIV]))

val MU_SAT_BOX = save_thm("MU_SAT_BOX",prove(``!s ks e.  (wfKS ks ==> (!a f. MU_SAT ([[a]] f) ks e s = !q. (ks.T a)(s,q) ==> MU_SAT f ks e q))``, RW_TAC std_ss [MU_SAT_def,STATES_def,KS_TRANSITION_def,SET_SPEC,wfKS_def,IN_UNIV]))

val MU_SAT_RV = save_thm("MU_SAT_RV",prove(``!s ks e. (wfKS ks ==> (!Q. MU_SAT (RV Q) ks e s = (e Q) s))``,
			    RW_TAC std_ss [MU_SAT_def,STATES_def,SET_SPEC,wfKS_def,IN_UNIV]))

val MU_SAT_AP = save_thm("MU_SAT_AP",prove(``!s ks e. wfKS ks ==> !a. MU_SAT (AP a) ks e s = ks.L s a``,SIMP_TAC std_ss [MU_SAT_def,STATES_def,SET_SPEC,wfKS_def,IN_UNIV] THEN SIMP_TAC std_ss [IN_DEF]))

val MU_SAT_LFP = save_thm("MU_SAT_LFP",prove(``!s ks e. (wfKS ks ==> (!Q f. MU_SAT (mu Q .. f) ks e s = ?n. s IN FP f Q ks e[[[Q<--{}]]] n))``,RW_TAC std_ss [MU_SAT_def,STATES_def,SET_SPEC,wfKS_def]))

val MU_SAT_GFP = save_thm("MU_SAT_GFP",prove(``!s ks e. (wfKS ks ==> (!Q f. MU_SAT (nu Q .. f) ks e s = !n. s IN FP f Q ks e[[[Q<--ks.S]]] n))``,RW_TAC std_ss [MU_SAT_def,STATES_def,SET_SPEC,wfKS_def]))

val SAT_OVER_DISJ = prove(``!(f:'prop mu) (g:'prop mu) (ks:('prop,'state) KS) e s. MU_SAT (f \/ g) ks e s = MU_SAT f ks e s \/ MU_SAT g ks e s``,
RW_TAC std_ss [MU_SAT_def,STATES_def,UNION_DEF,SET_SPEC])

val SAT_OVER_CONJ = prove(``!(f:'prop mu) (g:'prop mu) (ks:('prop,'state) KS) e s. MU_SAT (f /\ g) ks e s = MU_SAT f ks e s /\ MU_SAT g ks e s``,
RW_TAC std_ss [MU_SAT_def,STATES_def,INTER_DEF,SET_SPEC])

val SAT_OVER_NEG = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e s. wfKS ks ==> (MU_SAT (~f) ks e s = ~MU_SAT f ks e s)``,
RW_TAC std_ss [wfKS_def,MU_SAT_def,STATES_def,DIFF_DEF,SET_SPEC,IN_UNIV])

val SAT_OVER_DMD = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e s a. wfKS ks ==> (MU_SAT <<a>> f ks e s = ?q. ks.T a (s,q) /\ MU_SAT f ks e q)``,
RW_TAC std_ss [MU_SAT_def,STATES_def,KS_TRANSITION_def,SET_SPEC,wfKS_def,IN_UNIV])

(* the monotonicity thm and its lemmas *)

val STATES_MONO_LEM4 = prove(`` ((!Q'.
   (if SUBFORMULA (~RV Q') (NNF (RVNEG Q ~(f:'prop mu))) then e Q' = e' Q' else
      e Q' SUBSET e' Q')) /\ (~SUBFORMULA (~RV Q') (NNF (RVNEG Q ~f))) /\ (X SUBSET Y)) ==>
 (!Q''. (if SUBFORMULA (~RV Q'') (NNF (RVNEG Q ~f)) then e[[[Q'<--X]]] Q'' = e'[[[Q'<--Y]]] Q''
    else e[[[Q'<--X]]] Q'' SUBSET e'[[[Q'<--Y]]] Q''))``,
REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [
 Cases_on `Q'=Q''` THENL [
  FULL_SIMP_TAC std_ss [],
  FULL_SIMP_TAC std_ss [ENV_UPDATE_def]
  THEN ASSUM_LIST PROVE_TAC],
 Cases_on `Q'=Q''` THENL [
  FULL_SIMP_TAC std_ss [ENV_UPDATE_def],
  FULL_SIMP_TAC std_ss [ENV_UPDATE_def]
  THEN ASSUM_LIST PROVE_TAC]])

val STATES_MONO_LEM5 = prove(``
     ( (!(ks':('prop,'state) KS) e'' e''' Q'' X' Y'.
       ((ks'.S0 SUBSET ks'.S)  /\ (ks'.S = UNIV)) /\ (~SUBFORMULA (~RV Q'') (NNF (RVNEG Q ~f)) /\
        IMF (RVNEG Q ~f)) /\ X' SUBSET Y' /\ (!Q'. (if SUBFORMULA (~RV Q') (NNF (RVNEG Q ~f)) then e'' Q' = e''' Q'
        else e'' Q' SUBSET e''' Q')) ==>STATES (RVNEG Q ~f) ks' e''[[[Q''<--X']]] SUBSET STATES (RVNEG Q ~f) ks' e'''[[[Q''<--Y']]]) /\
       ((ks: ('prop,'state) KS).S0 SUBSET UNIV) /\ (  ks.S = UNIV) /\(  !Q''. (if SUBFORMULA (~RV Q'') (NNF (RVNEG Q ~f)) then
               e[[[Q'<--X]]] Q'' = e'[[[Q'<--Y]]] Q'' else e[[[Q'<--X]]] Q'' SUBSET e'[[[Q'<--Y]]] Q'')) /\
      (UNIV DIFF X' SUBSET UNIV DIFF Y') /\ (  !Q. IMF (RVNEG Q ~f)) /\ (~SUBFORMULA (~RV Q) (NNF (RVNEG Q ~f)))) ==>
      (STATES (RVNEG Q ~f) ks e[[[Q'<--X]]][[[Q<--UNIV DIFF X']]] SUBSET STATES (RVNEG Q ~f) ks e'[[[Q'<--Y]]][[[Q<--UNIV DIFF Y']]])``,
FULL_SIMP_TAC std_ss [])

val STATES_MONO_NEG_NU_LEM1 = prove(``!Q' Q (f:'prop mu) . SUBFORMULA (~RV Q') (NNF ~nu Q.. f) = SUBFORMULA (~RV Q') (NNF (RVNEG Q ~f))``,
SIMP_TAC std_ss ([NNF_def,MU_SUB_def]@(tsimps ``:'prop mu``)))

val STATES_MONO_LEM7 = prove(``  ((~SUBFORMULA (~RV Q') (NNF (f:'prop mu))) /\
 (X SUBSET Y) /\ (!Q'.   (if SUBFORMULA (~RV Q') (NNF f) then e Q' = e' Q' else e Q' SUBSET e' Q'))) ==>
 (!Q''.(if SUBFORMULA (~RV Q'') (NNF f) then e[[[Q'<--X]]] Q''= e'[[[Q'<--Y]]] Q'' else e[[[Q'<--X]]] Q'' SUBSET e'[[[Q'<--Y]]] Q''))``,
REPEAT STRIP_TAC THEN COND_CASES_TAC THENL [
 Cases_on `Q'=Q''` THENL [
  FULL_SIMP_TAC std_ss [],
  FULL_SIMP_TAC std_ss [ENV_UPDATE_def]
  THEN ASSUM_LIST PROVE_TAC],
 Cases_on `Q'=Q''` THENL [
  FULL_SIMP_TAC std_ss [ENV_UPDATE_def],
  FULL_SIMP_TAC std_ss [ENV_UPDATE_def]
  THEN ASSUM_LIST PROVE_TAC]])

val GEN_COND_SPLIT_LEM = prove(``!c1 c2 P Q. (!x. (if (c1 x \/ c2 x) then P x else Q x)) /\ (!x. (P x==>Q x)) ==> (!x. if c1 x then P x else Q x) /\ (!x. if c2 x then P x else Q x)``,REPEAT STRIP_TAC THENL [ASSUM_LIST PROVE_TAC,ASSUM_LIST PROVE_TAC])

val NU_NEG_FP_LEMMA = prove(``(!n. FP (f:'prop mu) Q (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--UNIV]]] n SUBSET FP f Q ks e[[[Q'<--X]]][[[Q<--UNIV]]] n) ==> (!x. (!n. x IN FP f Q ks e'[[[Q'<--Y]]][[[Q<--UNIV]]] n) ==> !n. x IN FP f Q ks e[[[Q'<--X]]][[[Q<--UNIV]]] n)``,
PROVE_TAC [SUBSET_DEF])

val NU_FP_LEMMA = prove(``(!n. FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--ks.S]]] n SUBSET FP f Q ks e'[[[Q'<--Y]]][[[Q<--ks.S]]] n) ==>  (!x. (!n. x IN FP f Q ks e[[[Q'<--X]]][[[Q<--ks.S]]] n) ==> !n. x IN FP f Q ks e'[[[Q'<--Y]]][[[Q<--ks.S]]] n)``,
PROVE_TAC [SUBSET_DEF])

val STATES_MONO_LEMMA = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e e' Q X Y.
      (wfKS ks /\ (IMF mu Q.. f) /\ (X SUBSET Y) /\
      (!Q'. if (SUBFORMULA (~RV Q') (NNF f)) then (e Q' = e' Q') else (e Q' SUBSET e' Q'))) ==>
	    (STATES (NNF f) ks e[[[Q<--X]]] SUBSET STATES (NNF f) ks e'[[[Q<--Y]]])``,
recInduct NNF_IND_def THEN REPEAT CONJ_TAC THEN BETA_TAC THENL [ (* 21 subgoals *)
RW_TAC std_ss [STATES_def,NNF_def,SUBSET_DEF,IN_UNIV], (* T *)
RW_TAC std_ss [STATES_def,NNF_def,SUBSET_DEF,NOT_IN_EMPTY], (* F *)
REWRITE_TAC [IMF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,INTER_DEF,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ASSUME_TAC (GEN ``Q:string`` (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``(e:string -> 'state -> bool) Q``,``(e':string -> 'state -> bool) Q``] EQ_IMP_SUBSET)))
THEN IMP_RES_TAC (BETA_RULE (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``\Q. SUBFORMULA (~RV Q) (NNF (f:'prop mu))``,``\Q. SUBFORMULA (~RV Q) (NNF (g:'prop mu))``,``\Q. ((e:string -> 'state -> bool) Q = (e':string -> 'state -> bool) Q)``,``\Q.((e:string -> 'state -> bool) Q SUBSET (e':string -> 'state -> bool) Q)``] GEN_COND_SPLIT_LEM)))
THEN PAT_ASSUM ``IMF f`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``IMF g`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``!Q'. (if SUBFORMULA (~RV Q') (NNF f) \/ SUBFORMULA (~RV Q') (NNF g) then e Q' = e' Q'
 else !x. x IN e Q' ==> x IN e' Q')`` (fn t=> ALL_TAC)
THEN PAT_ASSUM ``!Q. (e Q = e' Q) ==> !x. x IN e Q ==> x IN e' Q`` (fn t => ALL_TAC)
THEN `!x. x IN STATES (NNF (g:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF g) ks e'[[[Q<--Y]]]` by RES_TAC
THEN `!x. x IN STATES (NNF (f:'prop mu)) (ks:('prop,'state) KS)  e[[[Q<--X]]] ==> x IN STATES (NNF f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN FULL_SIMP_TAC std_ss [], (* /\ *)
REWRITE_TAC [IMF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,UNION_DEF,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ASSUME_TAC (GEN ``Q:string`` (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``(e:string -> 'state -> bool) Q``,``(e':string -> 'state -> bool) Q``] EQ_IMP_SUBSET)))
THEN IMP_RES_TAC (BETA_RULE (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``\Q. SUBFORMULA (~RV Q) (NNF (f:'prop mu))``,``\Q. SUBFORMULA (~RV Q) (NNF (g:'prop mu))``,``\Q. ((e:string -> 'state -> bool) Q = (e':string -> 'state -> bool) Q)``,``\Q.((e:string -> 'state -> bool) Q SUBSET (e':string -> 'state -> bool) Q)``] GEN_COND_SPLIT_LEM)))
THEN PAT_ASSUM ``IMF f`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``IMF g`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``!Q'. (if SUBFORMULA (~RV Q') (NNF f) \/ SUBFORMULA (~RV Q') (NNF g) then e Q' = e' Q'
 else !x. x IN e Q' ==> x IN e' Q')`` (fn t=> ALL_TAC)
THEN PAT_ASSUM ``!Q. (e Q = e' Q) ==> !x. x IN e Q ==> x IN e' Q`` (fn t => ALL_TAC)
THEN `!x. x IN STATES (NNF (g:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF g) ks e'[[[Q<--Y]]]` by RES_TAC
THEN `!x. x IN STATES (NNF (f:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN ASSUM_LIST (fn t => PROVE_TAC [hd t, hd (tl t)]), (* \/ *)
FULL_SIMP_TAC std_ss [STATES_def,NNF_def,SUBSET_DEF,SET_SPEC,IMF_def], (* AP *)
SIMP_TAC std_ss [IMF_def,STATES_NNF_ID] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [STATES_def,wfKS_def,IN_UNIV,SET_SPEC]
THEN SIMP_TAC std_ss [SET_GSPEC,ETA_CONV `` (\(s:'state). e[[[Q'<--(X:'state -> bool)]]] Q s)``, ETA_CONV  ``(\(s:'state). e'[[[Q'<--(Y:'state->bool)]]] Q s)``]
THEN Cases_on `Q'=Q` THENL [
 FULL_SIMP_TAC std_ss [ENV_UPDATE_def],
 FULL_SIMP_TAC std_ss [ENV_UPDATE_def]
 THEN ASSUME_TAC STATES_MONO_LEM8
 THEN ASSUM_LIST PROVE_TAC], (* RV *)
REWRITE_TAC [IMF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ` !x. x IN STATES (NNF (f:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN POP_ASSUM (fn t => PROVE_TAC [t]), (* <> *)
REWRITE_TAC [IMF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ` !x. x IN STATES (NNF (f:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN POP_ASSUM (fn t => PROVE_TAC [t]), (* [] *)
SIMP_TAC std_ss [IMF_def,STATES_NNF_ID] THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [STATES_def,SUBSET_DEF,SET_SPEC,EXTENSION]
THEN MATCH_MP_TAC MU_FP_LEMMA
THEN Induct_on `n` THENL [
ASSUM_LIST (fn t => SIMP_TAC std_ss ([ENV_UPDATE_def,STATES_def,SUBSET_REFL]@t)),
SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--{}]]] n SUBSET FP f Q ks e'[[[Q'<--Y]]][[[Q<--{}]]] n``
THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks: ('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--{}]]] n``,``Y':'state->bool``)
THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--{}]]] n``,``X':'state->bool``)
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [STATES_MONO_LEM6]
THEN `( !Q''. (if SUBFORMULA (~RV Q'') (NNF (f:'prop mu)) then e[[[Q'<--X]]] Q'' = e'[[[Q'<--Y]]] Q'' else
      e[[[Q'<--X]]] Q'' SUBSET e'[[[Q'<--Y]]] Q''))` by (IMP_RES_TAC STATES_MONO_LEM7)
THEN PAT_ASSUM `` X SUBSET Y`` (fn t=> ALL_TAC)
THEN PAT_ASSUM `` !Q'. (if SUBFORMULA (~RV Q') (NNF f) then e Q' = e' Q' else e Q' SUBSET e' Q')`` (fn t => ALL_TAC)
THEN PAT_ASSUM `` ~SUBFORMULA (~RV Q') (NNF f)`` (fn t => ALL_TAC)
THEN FULL_SIMP_TAC std_ss []], (* mu *)
SIMP_TAC std_ss [IMF_def,STATES_NNF_ID] THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [STATES_def,SUBSET_DEF,SET_SPEC,EXTENSION]
THEN MATCH_MP_TAC NU_FP_LEMMA
THEN Induct_on `n` THENL [
ASSUM_LIST (fn t => SIMP_TAC std_ss ([ENV_UPDATE_def,STATES_def,SUBSET_REFL]@t)),
SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--ks.S]]] n SUBSET FP f Q ks e'[[[Q'<--Y]]][[[Q<--ks.S]]] n``
THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--ks.S]]] n``,``Y':'state->bool``)
THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks:('prop,'state) KS)  e[[[Q'<--X]]][[[Q<--ks.S]]] n``,``X':'state->bool``)
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [STATES_MONO_LEM11]
THEN `( !Q''. (if SUBFORMULA (~RV Q'') (NNF (f:'prop mu)) then e[[[Q'<--X]]] Q'' = e'[[[Q'<--Y]]] Q'' else
      e[[[Q'<--X]]] Q'' SUBSET e'[[[Q'<--Y]]] Q''))` by (IMP_RES_TAC STATES_MONO_LEM7)
THEN PAT_ASSUM `` X SUBSET Y`` (fn t=> ALL_TAC)
THEN PAT_ASSUM `` !Q'. (if SUBFORMULA (~RV Q') (NNF f) then e Q' = e' Q' else e Q' SUBSET e' Q')`` (fn t => ALL_TAC)
THEN PAT_ASSUM `` ~SUBFORMULA (~RV Q') (NNF f)`` (fn t => ALL_TAC)
THEN FULL_SIMP_TAC std_ss []], (* nu *)
RW_TAC std_ss [STATES_def,NNF_def,SUBSET_DEF,NOT_IN_EMPTY], (* ~T *)
RW_TAC std_ss [STATES_def,NNF_def,SUBSET_DEF,IN_UNIV], (* ~F *)
REWRITE_TAC [IMF_def,NNF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,UNION_DEF,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ASSUME_TAC (GEN ``Q:string`` (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``(e:string -> 'state -> bool) Q``,``(e':string -> 'state -> bool) Q``] EQ_IMP_SUBSET)))
THEN IMP_RES_TAC (BETA_RULE (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``\Q. SUBFORMULA (~RV Q) (NNF (f:'prop mu))``,``\Q. SUBFORMULA (~RV Q) (NNF (g:'prop mu))``,``\Q. ((e:string -> 'state -> bool) Q = (e':string -> 'state -> bool) Q)``,``\Q.((e:string -> 'state -> bool) Q SUBSET (e':string -> 'state -> bool) Q)``] GEN_COND_SPLIT_LEM)))
THEN PAT_ASSUM ``IMF f`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``IMF g`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``!Q'. (if SUBFORMULA (~RV Q') (NNF f) \/ SUBFORMULA (~RV Q') (NNF g) then e Q' = e' Q'
 else !x. x IN e Q' ==> x IN e' Q')`` (fn t=> ALL_TAC)
THEN PAT_ASSUM ``!Q. (e Q = e' Q) ==> !x. x IN e Q ==> x IN e' Q`` (fn t => ALL_TAC)
THEN `!x. x IN STATES (NNF ~(g:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF ~g) ks e'[[[Q<--Y]]]` by RES_TAC
THEN `!x. x IN STATES (NNF ~(f:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF ~f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN ASSUM_LIST (fn t => PROVE_TAC [hd t, hd (tl t)]), (* ~/\ *)
REWRITE_TAC [IMF_def,NNF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,INTER_DEF,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ASSUME_TAC (GEN ``Q:string`` (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``(e:string -> 'state -> bool) Q``,``(e':string -> 'state -> bool) Q``] EQ_IMP_SUBSET)))
THEN IMP_RES_TAC (BETA_RULE (ONCE_REWRITE_RULE [SUBSET_DEF] (ISPECL [``\Q. SUBFORMULA (~RV Q) (NNF (f:'prop mu))``,``\Q. SUBFORMULA (~RV Q) (NNF (g:'prop mu))``,``\Q. ((e:string -> 'state -> bool) Q = (e':string -> 'state -> bool) Q)``,``\Q.((e:string -> 'state -> bool) Q SUBSET (e':string -> 'state -> bool) Q)``] GEN_COND_SPLIT_LEM)))
THEN PAT_ASSUM ``IMF f`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``IMF g`` (fn t => ALL_TAC)
THEN PAT_ASSUM ``!Q'. (if SUBFORMULA (~RV Q') (NNF f) \/ SUBFORMULA (~RV Q') (NNF g) then e Q' = e' Q'
 else !x. x IN e Q' ==> x IN e' Q')`` (fn t=> ALL_TAC)
THEN PAT_ASSUM ``!Q. (e Q = e' Q) ==> !x. x IN e Q ==> x IN e' Q`` (fn t => ALL_TAC)
THEN `!x. x IN STATES (NNF ~(g:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF ~g) ks e'[[[Q<--Y]]]` by RES_TAC
THEN `!x. x IN STATES (NNF ~(f:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF ~f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN ASSUM_LIST (fn t => PROVE_TAC [hd t, hd (tl t)]),  (* ~\/ *)
FULL_SIMP_TAC std_ss [STATES_def,NNF_def,SUBSET_DEF,SET_SPEC,IMF_def], (* ~AP *)
SIMP_TAC std_ss [IMF_def,STATES_NNF_ID] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [STATES_def,wfKS_def,IN_UNIV,SET_SPEC,UNIV_DIFF_SUBSET]
THEN SIMP_TAC std_ss [SET_GSPEC,ETA_CONV `` (\(s:'state). e[[[Q'<--X]]] Q s)``, ETA_CONV  ``(\(s:'state). e'[[[Q'<--Y]]] Q s)``]
THEN FULL_SIMP_TAC std_ss [STATES_MONO_LEM9]
THEN FULL_SIMP_TAC std_ss [ENV_UPDATE_def]
THEN ONCE_REWRITE_TAC [SUBSET_DEST]
THEN DISJ2_TAC
THEN ASSUM_LIST (fn t=> PROVE_TAC (STATES_MONO_LEM9::t)), (* ~ RV *)
REWRITE_TAC [IMF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ` !x. x IN STATES (NNF ~(f:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF ~f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN POP_ASSUM (fn t => PROVE_TAC [t]), (* ~<> *)
REWRITE_TAC [IMF_def] THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss ([STATES_def,NNF_def,SUBSET_DEF,SET_SPEC,MU_SUB_def]@tsimps ``:'prop mu``)
THEN ` !x. x IN STATES (NNF ~(f:'prop mu)) (ks:('prop,'state) KS) e[[[Q<--X]]] ==> x IN STATES (NNF ~f) ks e'[[[Q<--Y]]]` by RES_TAC
THEN POP_ASSUM (fn t => PROVE_TAC [t]), (* ~[] *)
FULL_SIMP_TAC std_ss [STATES_def,NNF_def,SUBSET_DEF,SET_SPEC,IMF_def], (* ~~ *)
SIMP_TAC std_ss [IMF_def,STATES_NNF_ID] THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [STATES_def,SUBSET_DEF,SET_SPEC,EXTENSION]
THEN SIMP_TAC std_ss [DIFF_DEF,SET_SPEC]
THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV]
THEN SIMP_TAC std_ss [prove(``!P Q. ((!n. ~(P n)) ==> (!n. ~(Q n))) = ((?n. (Q n)) ==> (?n. P n))``,PROVE_TAC [])]
THEN MATCH_MP_TAC MU_NEG_FP_LEMMA
THEN FULL_SIMP_TAC std_ss [STATES_MONO_NEG_MU_LEM1]
THEN `!Q''. (if SUBFORMULA (~RV Q'') (NNF (RVNEG Q ~(f:'prop mu))) then e[[[Q'<--X]]] Q'' = e'[[[Q'<--Y]]] Q''
             else e[[[Q'<--X]]] Q'' SUBSET e'[[[Q'<--Y]]] Q'')` by IMP_RES_TAC STATES_MONO_LEM4
THEN Q.PAT_ASSUM `!Q'. (if SUBFORMULA (~RV Q') (NNF (RVNEG Q ~f)) then e Q' = e' Q' else e Q' SUBSET e' Q')` (fn t => ALL_TAC)
THEN Induct_on `n` THENL [
 ASSUM_LIST (fn t => SIMP_TAC std_ss ([ENV_UPDATE_def,STATES_def,SUBSET_REFL]@t)),
 SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
 THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--{}]]] n SUBSET FP f Q ks e[[[Q'<--X]]][[[Q<--{}]]] n``
 THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--{}]]] n``,``Y':'state->bool``)
 THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--{}]]] n``,``X':'state->bool``)
 THEN REPEAT STRIP_TAC
 THEN IMP_RES_TAC IMF_INV_NEG_RVNEG
 THEN IMP_RES_TAC  STATES_MONO_LEM3
 THEN POP_ASSUM (fn t => ALL_TAC)
 THEN IMP_RES_TAC UNIV_DIFF_SUBSET
 THEN POP_ASSUM (fn t => ALL_TAC)
 THEN POP_ASSUM (fn t => ALL_TAC)
 THEN `(STATES (RVNEG Q ~(f:'prop mu)) (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--UNIV DIFF X']]] SUBSET
            STATES (RVNEG Q ~f) ks e'[[[Q'<--Y]]][[[Q<--UNIV DIFF Y']]])` by (IMP_RES_TAC STATES_MONO_LEM5)
 THEN (SUBGOAL_THEN ``STATES (RVNEG Q (f:'prop mu)) (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--UNIV DIFF Y']]] SUBSET STATES (RVNEG Q f) ks e[[[Q'<--X]]][[[Q<--UNIV DIFF X']]]`` ASSUME_TAC )
 THEN (FULL_SIMP_TAC std_ss [STATES_def,RVNEG_def,UNIV_DIFF_SUBSET])
 THEN PAT_ASSUM ``(ks:('prop,'state) KS).S DIFF STATES (RVNEG Q (f:'prop mu)) ks e[[[Q'<--X]]][[[Q<--UNIV DIFF X']]] SUBSET ks.S DIFF STATES (RVNEG Q f) ks e'[[[Q'<--Y]]][[[Q<--UNIV DIFF Y']]]`` (fn t => ALL_TAC)
 THEN IMP_RES_TAC wfKS_UNIV
 THEN IMP_RES_TAC RV_NEG_NEG
 THEN FULL_SIMP_TAC std_ss []], (* ~mu *)
SIMP_TAC std_ss [IMF_def,STATES_NNF_ID] THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [STATES_def,SUBSET_DEF,SET_SPEC,EXTENSION]
THEN SIMP_TAC std_ss [DIFF_DEF,SET_SPEC]
THEN FULL_SIMP_TAC std_ss [wfKS_def,IN_UNIV]
THEN SIMP_TAC std_ss [prove(``!P Q. ((?n. ~(P n)) ==> (?n. ~(Q n))) = ((!n. (Q n)) ==> (!n. P n))``,PROVE_TAC [])]
THEN MATCH_MP_TAC NU_NEG_FP_LEMMA
THEN Induct_on `n` THENL [
 ASSUM_LIST (fn t => SIMP_TAC std_ss ([ENV_UPDATE_def,STATES_def,SUBSET_REFL]@t)),
 SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
 THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--UNIV]]] n SUBSET FP f Q ks e[[[Q'<--X]]][[[Q<--UNIV]]] n``
 THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks:('prop,'state) KS)  e'[[[Q'<--Y]]][[[Q<--UNIV]]] n``,``Y':'state->bool``)
 THEN SPEC_TAC (`` FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--UNIV]]] n``,``X':'state->bool``)
 THEN REPEAT STRIP_TAC
 THEN FULL_SIMP_TAC std_ss [STATES_MONO_NEG_NU_LEM1]
 THEN `!Q''. (if SUBFORMULA (~RV Q'') (NNF (RVNEG Q ~(f: 'prop mu))) then e[[[Q'<--X]]] Q'' = e'[[[Q'<--Y]]] Q''
   else e[[[Q'<--X]]] Q'' SUBSET e'[[[Q'<--Y]]] Q'')` by (IMP_RES_TAC STATES_MONO_LEM4)
 THEN PAT_ASSUM ``!Q'. (if SUBFORMULA (~RV Q') (NNF (RVNEG Q ~f)) then e Q' = e' Q' else e Q' SUBSET e' Q')`` (fn t => ALL_TAC)
 THEN IMP_RES_TAC IMF_INV_NEG_RVNEG
 THEN IMP_RES_TAC  STATES_MONO_LEM3
 THEN POP_ASSUM (fn t => ALL_TAC)
 THEN IMP_RES_TAC UNIV_DIFF_SUBSET
 THEN POP_ASSUM (fn t => ALL_TAC)
 THEN POP_ASSUM (fn t => ALL_TAC)
 THEN `(STATES (RVNEG Q ~(f:'prop mu)) (ks:('prop,'state) KS) e[[[Q'<--X]]][[[Q<--UNIV DIFF X']]] SUBSET
            STATES (RVNEG Q ~f) ks e'[[[Q'<--Y]]][[[Q<--UNIV DIFF Y']]])` by (IMP_RES_TAC STATES_MONO_LEM5)
 THEN (SUBGOAL_THEN ``STATES (RVNEG Q (f:'prop mu)) (ks:('prop,'state) KS) e'[[[Q'<--Y]]][[[Q<--UNIV DIFF Y']]] SUBSET STATES (RVNEG Q f) ks e[[[Q'<--X]]][[[Q<--UNIV DIFF X']]]`` ASSUME_TAC)
 THEN FULL_SIMP_TAC std_ss [STATES_def,RVNEG_def,UNIV_DIFF_SUBSET]
 THEN PAT_ASSUM ``ks.S DIFF STATES (RVNEG Q f) ks e[[[Q'<--X]]][[[Q<--UNIV DIFF X']]] SUBSET ks.S DIFF STATES (RVNEG Q f) ks e'[[[Q'<--Y]]][[[Q<--UNIV DIFF Y']]]`` (fn t => ALL_TAC)
 THEN IMP_RES_TAC wfKS_UNIV
 THEN IMP_RES_TAC RV_NEG_NEG
 THEN FULL_SIMP_TAC std_ss []]]) (* ~nu *)

val STATES_MONO = save_thm("STATES_MONO",SIMP_RULE std_ss [STATES_NNF_ID] STATES_MONO_LEMMA)

val ENV_VAR_LEGAL = save_thm("ENV_VAR_LEGAL",prove(``!(e:string -> 'state -> bool) Q' f. if (SUBFORMULA (~RV Q') (NNF (f:'prop mu))) then e Q' = e Q' else e Q' SUBSET e Q'``,SIMP_TAC std_ss [SUBSET_REFL]))

val STATES_MONO_EQ = save_thm("STATES_MONO_EQ",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q X Y.
      (wfKS ks /\ (IMF mu Q.. f) /\ (X SUBSET Y)) ==>
	    (STATES f ks e[[[Q<--X]]] SUBSET STATES f ks e[[[Q<--Y]]])``,SIMP_TAC std_ss [STATES_MONO,ENV_VAR_LEGAL]))

(* thms for proving existence of least fixed-points *)

val LFP_CHAIN = save_thm("LFP_CHAIN",prove(``!(f:'prop mu) ks e n Q. (wfKS ks /\ IMF (mu Q .. f)) ==>
			 (FP f Q ks e[[[Q<--{}]]] n SUBSET FP f Q ks e[[[Q<--{}]]] (SUC n))``,
REPEAT STRIP_TAC THEN Induct_on `n` THENL [
 SIMP_TAC std_ss [STATES_def,EMPTY_SUBSET,ENV_UPDATE_def],
 ONCE_REWRITE_TAC [STATES_def]
 THEN REWRITE_TAC [ENV_UPDATE]
 THEN FULL_SIMP_TAC std_ss [STATES_MONO,ENV_VAR_LEGAL]]))

val LFP_CHAIN_STABLE = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q. (wfKS ks /\ IMF (mu Q.. f)) ==>
                 ((FP f Q ks e[[[Q<--{}]]] n = FP f Q ks e[[[Q<--{}]]] (SUC n)) ==>
		  (!m. m>=n ==> (FP f Q ks e[[[Q<--{}]]] m = FP f Q ks e[[[Q<--{}]]] n)))``,
REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
THEN REPEAT STRIP_TAC THENL [
 PAT_ASSUM ``m=n`` (fn t => REWRITE_TAC [t]), (* m = n *)
 Induct_on `m` THENL [
  SIMP_TAC arith_ss [], (* 0 *)
  REWRITE_TAC [DECIDE ``(SUC m > n)=(m>=n)``]
  THEN REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
  THEN REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [], (* m=n *)
   PAT_ASSUM ``FP f Q ks e[[[Q<--{}]]] n = FP f Q ks e[[[Q<--{}]]] (SUC n)`` (fn t => REWRITE_TAC [t])
   THEN ONCE_REWRITE_TAC [STATES_def]
   THEN REWRITE_TAC [ENV_UPDATE]
   THEN ASSUM_LIST PROVE_TAC]]])

val LFP_CHAIN_UNION = prove(``!n' (f:'prop mu) Q ks e. (wfKS ks /\ IMF (mu Q.. f)) ==>
                 (BIGUNION {P | ?n. n <= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} = FP f Q ks e[[[Q<--{}]]] n')``,
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
 THEN SIMP_TAC std_ss [SET_GSPEC, ETA_CONV `` (\x. FP f Q ks e[[[Q<--{}]]] (SUC n') x)``]
 THEN PROVE_TAC [LFP_CHAIN,SUBSET_UNION_ABSORPTION]])

val LFP_FP_SUBSET = prove(``!n' (f:'prop mu) Q (ks:('prop,'state) KS) e.  (wfKS ks /\ IMF (mu Q.. f) /\ (FP f Q ks e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n'))) ==>
                  (BIGUNION {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} SUBSET FP f Q ks e[[[Q<--{}]]] n')``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPECL [``f:'prop mu``,``ks:('prop,'state) KS``,``e:string -> 'state -> bool``,``n':num``,``Q:string``] LFP_CHAIN_STABLE)
THEN UNDISCH_TAC `` wfKS (ks:('prop,'state) KS) /\ IMF (mu Q..f) ==> (FP f Q ks e[[[Q<--{}]]] n' =  FP f Q ks e[[[Q<--{}]]] (SUC n')) ==>
 !m. m >= n' ==> (FP f Q ks e[[[Q<--{}]]] m = FP f Q ks e[[[Q<--{}]]] n')``
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--{}]]]``,``P:num->'state->bool``)
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,SUBSET_DEF]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN ASSUM_LIST PROVE_TAC)  (* TODO: the SUBSET should really be an = *)

val MU_FP_STATES_LEM1 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n' Q. wfKS ks /\ IMF (mu Q..f) ==>
   (FP f Q ks e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')) ==>
     (FP f Q ks e[[[Q<--{}]]] n' UNION  BIGUNION {P | ?n. n >= n' /\ (P =FP f Q ks e[[[Q<--{}]]] n)} =
      FP f Q ks e[[[Q<--{}]]] n')``,
REPEAT GEN_TAC
THEN ASSUME_TAC (SPEC_ALL LFP_FP_SUBSET)
THEN UNDISCH_TAC ``wfKS (ks:('prop,'state) KS) /\ IMF (mu Q..(f:'prop mu)) /\ (FP f Q ks e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')) ==>
      BIGUNION {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} SUBSET FP f Q ks e[[[Q<--{}]]] n'``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--{}]]]``,``P:num -> 'state -> bool``)
THEN REPEAT STRIP_TAC
THEN ONCE_REWRITE_TAC [UNION_COMM]
THEN ASSUM_LIST (fn t => PROVE_TAC (SUBSET_UNION_ABSORPTION::t)))

val MU_FP_STATES_LEM2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n' Q. (wfKS ks /\ IMF (mu Q..f)) ==>
                 ((FP f Q ks e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')) ==>
                   (BIGUNION {P | ?n. n <= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} UNION
                     BIGUNION {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} =
                    FP f Q ks e[[[Q<--{}]]] n'))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (LFP_CHAIN_UNION::(tl t)))
THEN ASSUME_TAC (SPEC_ALL MU_FP_STATES_LEM1)
THEN UNDISCH_TAC `` wfKS (ks:('prop,'state) KS) /\ IMF (mu Q .. f) ==> (FP f Q ks e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')) ==>
 (FP f Q ks e[[[Q<--{}]]] n' UNION BIGUNION {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} =
  FP f Q ks e[[[Q<--{}]]] n')``
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--{}]]]``,``P:num -> 'state -> bool``)
THEN ASSUM_LIST PROVE_TAC)


val MU_FP_STATES = save_thm("MU_FP_STATES",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n' Q. (wfKS ks /\ IMF (mu Q ..f)) ==>
                 ((FP f Q ks e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')) ==>
                       (STATES (mu Q.. f) ks e = FP f Q ks e[[[Q<--{}]]] n'))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (MU_BIGUNION::(tl t)))
THEN ASSUME_TAC (SPEC_ALL MU_FP_STATES_LEM2)
THEN UNDISCH_TAC `` wfKS (ks:('prop,'state) KS) /\ IMF (mu Q.. f) ==> (FP f Q ks e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')) ==>
 (BIGUNION {P | ?n. n <= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} UNION
   BIGUNION {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--{}]]] n)} =
  FP f Q ks e[[[Q<--{}]]] n')``
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n' = FP f Q ks e[[[Q<--{}]]] (SUC n')``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--{}]]]``,``P:num -> 'state -> bool``)
THEN REWRITE_TAC [GSYM BIGUNION_SPLIT]
THEN ASSUM_LIST PROVE_TAC))

val LFP_STRICT_CHAIN = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q. (wfKS ks /\ IMF (mu Q.. f)) ==>
				(~(FP f Q ks e[[[Q<--{}]]] n = FP f Q ks e[[[Q<--{}]]] (SUC n))) ==>
				FP f Q ks e[[[Q<--{}]]] n PSUBSET FP f Q ks e[[[Q<--{}]]] (SUC n)``,
				PROVE_TAC [GSYM PSUBSET_DEF,LFP_CHAIN])

val LFP_STRICT_CHAIN2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (mu Q.. f)) ==>
				(!n. ~(FP f Q ks e[[[Q<--{}]]] n = FP f Q ks e[[[Q<--{}]]] (SUC n))) ==>
				!n. (FP f Q ks e[[[Q<--{}]]] n PSUBSET FP f Q ks e[[[Q<--{}]]] (SUC n))``,
				PROVE_TAC [GSYM PSUBSET_DEF,LFP_CHAIN])

val STATES_FINITE = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e. wfKS ks ==> FINITE ks.S ==> FINITE (STATES f ks e)``,
PROVE_TAC [wfKS_def,SUBSET_UNIV,SUBSET_FINITE])

val LFP_FP_FINITE = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e n. wfKS ks ==> FINITE (ks.S) ==> FINITE (FP f Q ks e[[[Q<--{}]]] n)``,
REPEAT GEN_TAC THEN Induct_on `n` THENL [
SIMP_TAC std_ss [STATES_def,ENV_EVAL,FINITE_EMPTY],
SIMP_TAC std_ss [STATES_FINITE,STATES_def]])

val LFP_FP_STRICT_CARD = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (mu Q .. f) /\ FINITE (ks.S)) ==>
				  (!n. ~(FP f Q ks e[[[Q<--{}]]] n = FP f Q ks e[[[Q<--{}]]] (SUC n))) ==>
				  (!n. CARD (FP f Q ks e[[[Q<--{}]]] n) < CARD (FP f Q ks e[[[Q<--{}]]] (SUC n)))``,
PROVE_TAC [LFP_FP_FINITE,PSUBSET_CARD_LT,LFP_STRICT_CHAIN2])


val GEN_LFP_IDEM_LEM1 =  GENL [``f:'prop mu``,``Q:string``,``ks:('prop,'state) KS``,``e:string -> 'state -> bool``] (SPEC ``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--{}]]]`` GEN_PCHAIN_CARD_NO_UB)

val LFP_STRICT_CHAIN2_IMP_CARD_GT_S = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e.
         (!n.
            CARD (FP f Q ks e[[[Q<--{}]]] n) <
            CARD (FP f Q ks e[[[Q<--{}]]] (SUC n))) ==> (?n.  CARD (FP f Q ks e[[[Q<--{}]]] n) > CARD ks.S)``,
REPEAT STRIP_TAC THEN IMP_RES_TAC GEN_LFP_IDEM_LEM1 THEN FULL_SIMP_TAC std_ss [])

val CARD_S_GTE = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e n. wfKS ks /\ FINITE ks.S ==> CARD (FP f Q ks e[[[Q<--{}]]] n) <= CARD ks.S``,
FULL_SIMP_TAC std_ss [LFP_FP_FINITE,SUBSET_CARD_LTE,wfKS_def,SUBSET_UNIV])

val GEN_LFP_IDEM_LEM2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (mu Q.. f) /\ FINITE ks.S) ==>
			    ?k. (FP f Q ks e[[[Q<--{}]]] k = FP f Q ks e[[[Q<--{}]]] (SUC k))``,
REPEAT STRIP_TAC THEN SPOSE_NOT_THEN ASSUME_TAC THEN IMP_RES_TAC LFP_FP_STRICT_CARD
THEN IMP_RES_TAC LFP_STRICT_CHAIN2_IMP_CARD_GT_S THEN IMP_RES_TAC CARD_S_GTE
THEN ASSUM_LIST (fn t => PROVE_TAC ((DECIDE ``!m n. ~(m>n /\ m<=n)``)::t))
)

val LFP_IDEM = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q. (wfKS ks /\ IMF (mu Q .. f)) ==>
		((FP f Q ks e[[[Q<--{}]]] n = FP f Q ks e[[[Q<--{}]]] (SUC n)) ==>
                       (STATES f ks e[[[Q<--(BIGUNION {P | ?i. (P = (FP f Q ks e[[[Q<--{}]]] i))})]]]
			= (BIGUNION {P | ?i. (P = (FP f Q ks e[[[Q<--{}]]] i))})))``,
		FULL_SIMP_TAC std_ss [CONV_RULE (STRIP_QUANT_CONV (FORK_CONV (ALL_CONV,SYM_CONV))) MU_BIGUNION]
		THEN REPEAT STRIP_TAC THEN IMP_RES_TAC MU_FP_STATES
		THEN PAT_ASSUM ``STATES (mu Q.. (f:'prop mu)) (ks:('prop,'state) KS) e = FP f Q ks e[[[Q<--{}]]] n`` (fn t => REWRITE_TAC [t])
		THEN REWRITE_TAC [SYM (prove (``STATES (f:'prop mu) (ks:('prop,'state) KS) e[[[Q<--{}]]][[[Q<--FP f Q ks e[[[Q<--{}]]] n]]]
					      = STATES f ks e[[[Q<--FP f Q ks e[[[Q<--{}]]] n]]]``, PROVE_TAC [ENV_UPDATE]))]
		THEN UNDISCH_TAC ``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n = FP f Q ks e[[[Q<--{}]]] (SUC n)``
		THEN SPEC_TAC (``e[[[Q<--{}]]]:string->'state->bool``,``e:string->'state->bool``)
		THEN ASSUM_LIST (fn t => PROVE_TAC (STATES_def::t)))

val GEN_LFP_IDEM =  save_thm("GEN_LFP_IDEM",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (mu Q .. f) /\ FINITE ks.S) ==>
			     (STATES f ks e[[[Q<--(BIGUNION {P | ?i. (P = (FP f Q ks e[[[Q<--{}]]] i))})]]]
			      = (BIGUNION {P | ?i. (P = (FP f Q ks e[[[Q<--{}]]] i))}))``,
REPEAT STRIP_TAC THEN IMP_RES_TAC GEN_LFP_IDEM_LEM2 THEN IMP_RES_TAC LFP_IDEM THEN FULL_SIMP_TAC std_ss []))

val GEN_LFP_FP_IDEM = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q n. (wfKS ks /\ IMF (mu Q .. f) /\ FINITE ks.S) ==>
 (FP f Q ks e[[[Q<--(BIGUNION {P | ?i. (P = (FP f Q ks e[[[Q<--{}]]] i))})]]] n
			      = (BIGUNION {P | ?i. (P = (FP f Q ks e[[[Q<--{}]]] i))}))``,
Induct_on `n` THENL [
SIMP_TAC std_ss [STATES_def,ENV_EVAL],
FULL_SIMP_TAC std_ss [ENV_UPDATE,STATES_def,GEN_LFP_IDEM]])

val SPEC_GEN_LFP_FP_IDEM =  SPECL [``f:'prop mu``,``ks:('prop,'state) KS``,``e:string->'state->bool``,``Q:string``,``n:num``] GEN_LFP_FP_IDEM

val LFP_CHAIN_TOP = prove(``!(f:'prop mu) Q ks e. (wfKS ks /\ IMF (mu Q.. f) /\ FINITE ks.S) ==>
 ?n. BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)} = FP f Q ks e[[[Q<--{}]]] n``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC GEN_LFP_IDEM_LEM2
THEN POP_ASSUM (fn t => ASSUME_TAC (Q.SPEC `e` t))
THEN RW_TAC std_ss []
THEN Q.EXISTS_TAC `k`
THEN REWRITE_TAC [Q.SPEC `k` (CONV_RULE SWAP_VARS_CONV BIGUNION_SPLIT)]
THEN ASSUM_LIST (fn t => METIS_TAC (LFP_CHAIN_UNION::MU_FP_STATES_LEM1::t))
)

val GEN_LFP_CHAIN = save_thm("GEN_LFP_CHAIN",prove(``!(f:'prop mu) ks e n Q X. (wfKS ks /\ IMF (mu Q .. f)  /\ X SUBSET STATES f ks e[[[Q<--X]]]) ==>
			 (FP f Q ks e[[[Q<--X]]] n SUBSET FP f Q ks e[[[Q<--X]]] (SUC n))``,
REPEAT STRIP_TAC THEN Induct_on `n` THENL [
FULL_SIMP_TAC std_ss [STATES_def,ENV_UPDATE,ENV_EVAL],
 ONCE_REWRITE_TAC [STATES_def]
 THEN REWRITE_TAC [ENV_UPDATE]
 THEN FULL_SIMP_TAC std_ss [STATES_MONO,ENV_VAR_LEGAL]]))

val GEN_LFP_CHAIN_STABLE = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q X. (wfKS ks /\ IMF (mu Q.. f)) ==>
                 ((FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)) ==>
		  (!m. m>=n ==> (FP f Q ks e[[[Q<--X]]] m = FP f Q ks e[[[Q<--X]]] n)))``,
REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
THEN REPEAT STRIP_TAC THENL [
 PAT_ASSUM ``m=n`` (fn t => REWRITE_TAC [t]), (* m = n *)
 Induct_on `m` THENL [
  SIMP_TAC arith_ss [], (* 0 *)
  REWRITE_TAC [DECIDE ``(SUC m > n)=(m>=n)``]
  THEN REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
  THEN REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [], (* m=n *)
   PAT_ASSUM ``FP f Q (ks:('prop,'state) KS) e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)`` (fn t => REWRITE_TAC [t])
   THEN ONCE_REWRITE_TAC [STATES_def]
   THEN REWRITE_TAC [ENV_UPDATE]
   THEN ASSUM_LIST PROVE_TAC]]])

val GEN_LFP_CHAIN_UNION = prove(``!n (f:'prop mu) Q (ks:('prop,'state) KS) e X. (wfKS ks /\ IMF (mu Q.. f) /\  X SUBSET STATES f ks e[[[Q<--X]]]) ==> (BIGUNION {P | ?n'. n' <= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} = FP f Q ks e[[[Q<--X]]] n)``,
REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
 REWRITE_TAC [DECIDE ``!n. n<=0 = (n=0)``]
 THEN REWRITE_TAC [BIGUNION]
 THEN SIMP_TAC std_ss [SET_SPEC]
 THEN SIMP_TAC std_ss [SET_SPEC,EXTENSION], (* 0 *)
 REWRITE_TAC [DECIDE ``!n n'. n'<=(SUC n) = (n'<=n \/ (n'=SUC n))``]
 THEN REWRITE_TAC [RIGHT_AND_OVER_OR]
 THEN SIMP_TAC std_ss [EXISTS_OR_THM]
 THEN SIMP_TAC arith_ss [GSYM (SIMP_RULE std_ss [IN_DEF] UNION_DEF)]
 THEN SIMP_TAC std_ss [BIGUNION_UNION]
 THEN FULL_SIMP_TAC std_ss [SET_GSPEC]
 THEN SIMP_TAC std_ss [BIGUNION,IN_DEF]
 THEN SIMP_TAC std_ss [SET_GSPEC, ETA_CONV `` (\x. FP (f:'prop mu) Q ks e[[[Q<--X]]] (SUC n') x)``]
 THEN PROVE_TAC [GEN_LFP_CHAIN,SUBSET_UNION_ABSORPTION,ENV_VAR_LEGAL]]
)

val GEN_LFP_FP_SUBSET = prove(``!n (f:'prop mu) Q (ks:('prop,'state) KS) e X.  (wfKS ks /\ IMF (mu Q.. f) /\ (FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n))) ==>
                  (BIGUNION {P | ?n'. n' >= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} = FP f Q ks e[[[Q<--X]]] n)``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC GEN_LFP_CHAIN_STABLE
THEN NTAC 2 (POP_ASSUM MP_TAC)
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--X]]]``,``P:num->'state->bool``)
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGUNION,SUBSET_DEF]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN ONCE_REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN CONV_TAC (LAND_CONV (pred_setLib.SET_SPEC_CONV))
THEN EQ_TAC THENL [
REPEAT STRIP_TAC
THEN PAT_ASSUM ``!m. t`` (fn t => ASSUME_TAC (Q.SPEC `n'` t))
THEN ASSUM_LIST PROVE_TAC,
REPEAT STRIP_TAC
THEN Q.EXISTS_TAC `P n`
THEN CONJ_TAC THEN ASM_REWRITE_TAC []
THEN Q.EXISTS_TAC `SUC n`
THEN SIMP_TAC arith_ss []])

val GEN_MU_FP_STATES_LEM1 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q X. wfKS ks /\ IMF (mu Q..f) ==>
   (FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)) ==>
     (FP f Q ks e[[[Q<--X]]] n UNION  BIGUNION {P | ?n'. n' >= n /\ (P =FP f Q ks e[[[Q<--X]]] n')} =
      FP f Q ks e[[[Q<--X]]] n)``,
REPEAT STRIP_TAC THEN IMP_RES_TAC  GEN_LFP_FP_SUBSET
THEN NTAC 2 (POP_ASSUM MP_TAC)
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--X]]]``,``P:num->'state->bool``)
THEN REPEAT STRIP_TAC
THEN ASM_REWRITE_TAC [UNION_IDEMPOT])

val GEN_MU_FP_STATES_LEM2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q X. (wfKS ks /\ IMF (mu Q..f) /\ X SUBSET STATES f ks e[[[Q<--X]]]) ==>
                 ((FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)) ==>
                   (BIGUNION {P | ?n'. n' <= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} UNION
                     BIGUNION {P | ?n'. n' >= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} = FP f Q ks e[[[Q<--X]]] n))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (GEN_LFP_CHAIN_UNION::(tl t)))
THEN IMP_RES_TAC  GEN_MU_FP_STATES_LEM1)

val GEN_LFP_SUBSET = prove(``!(f:'prop mu) ks e Q X. wfKS ks /\ IMF (mu Q ..f) /\ FINITE ks.S ==>
X SUBSET BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)} ==>
!n. FP f Q ks e[[[Q<--X]]] n SUBSET  BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)}``,
REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
ASM_REWRITE_TAC [STATES_def,ENV_EVAL,ENV_UPDATE], (* 0 *)
`STATES f ks e[[[Q<--FP f Q ks e[[[Q<--X]]] n]]] SUBSET STATES f ks e[[[Q<--BIGUNION {P | ?n. P = FP f Q ks e[[[Q<--{}]]] n}]]]` by FULL_SIMP_TAC std_ss [STATES_MONO,ENV_VAR_LEGAL]
THEN REWRITE_TAC [STATES_def,ENV_UPDATE]
THEN IMP_RES_TAC GEN_LFP_IDEM
THEN ASSUM_LIST METIS_TAC])

val GEN_LFP_UNION_SUBSET = prove(``!(f:'prop mu) ks e Q X. wfKS ks /\ IMF (mu Q ..f) /\ FINITE ks.S ==> X SUBSET BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)} ==>
BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--X]]] n)} SUBSET  BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)}``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC GEN_LFP_SUBSET
THEN ASSUM_LIST (fn t => METIS_TAC (LEFT_BIGUNION_SUBSET::t)))

val LFP_ITER_EQ = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e X .
  (wfKS ks /\ IMF (mu Q ..f) /\ FINITE ks.S) ==>
		X SUBSET BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)} ==>
		(BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)} =
		 BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--X]]] n)})``,
 REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM SUBSET_EQ] THEN CONJ_TAC THENL [
`!n. FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--{}]]] n SUBSET FP f Q ks e[[[Q<--X]]] n` by
    (Induct_on `n` THENL [SIMP_TAC std_ss [STATES_def,EMPTY_SUBSET,ENV_EVAL],
	    FULL_SIMP_TAC std_ss [STATES_def,STATES_MONO,ENV_VAR_LEGAL,ENV_UPDATE]])
THEN FULL_SIMP_TAC std_ss [BIGUNION_SUBSET_IMP],
IMP_RES_TAC GEN_LFP_UNION_SUBSET
])

val GEN_MU_FP_STATES = save_thm("GEN_MU_FP_STATES",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q X. wfKS ks /\ IMF (mu Q ..f) /\ FINITE ks.S /\
                  X SUBSET STATES f ks e[[[Q<--X]]] ==> X SUBSET BIGUNION {P | ?n. (P = FP f Q ks e[[[Q<--{}]]] n)}  ==>
                 ((FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)) ==>
                       (STATES (mu Q.. f) ks e = FP f Q ks e[[[Q<--X]]] n))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (MU_BIGUNION::(tl t)))
THEN IMP_RES_TAC GEN_MU_FP_STATES_LEM2
THEN IMP_RES_TAC LFP_ITER_EQ
THEN FULL_SIMP_TAC std_ss [GSYM BIGUNION_SPLIT]))

(* thms for proving existence of greatest fixed-points *)

val GFP_CHAIN = save_thm("GFP_CHAIN",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q. (wfKS ks /\ IMF (mu Q..f)) ==> (FP f Q ks e[[[Q<--ks.S]]] (SUC n) SUBSET FP f Q ks e[[[Q<--ks.S]]]  n)``,
SIMP_TAC std_ss [wfKS_def]
THEN REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
SIMP_TAC std_ss [STATES_def,ENV_UPDATE_def,SUBSET_DEF,IN_UNIV],
ONCE_REWRITE_TAC [STATES_def]
THEN REWRITE_TAC [ENV_UPDATE]
THEN ASSUM_LIST (fn t => PROVE_TAC (wfKS_def::STATES_MONO::ENV_VAR_LEGAL::t))]))

val GFP_CHAIN_STABLE = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q. (wfKS ks /\ IMF (mu Q ..f)) ==>
                 ((FP f Q ks e[[[Q<--ks.S]]] n = FP f Q ks e[[[Q<--ks.S]]] (SUC n)) ==>
		  (!m. m>=n ==> (FP f Q ks e[[[Q<--ks.S]]] m = FP f Q ks e[[[Q<--ks.S]]] n)))``,
REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
THEN REPEAT STRIP_TAC THENL [
 PAT_ASSUM ``m=n`` (fn t => REWRITE_TAC [t]), (* m = n *)
 Induct_on `m` THENL [
   SIMP_TAC arith_ss [], (* 0 *)
  REWRITE_TAC [DECIDE ``(SUC m > n)=(m>=n)``]
  THEN REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
  THEN REPEAT STRIP_TAC THENL [
  FULL_SIMP_TAC std_ss [], (* m=n *)
  PAT_ASSUM ``FP f Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n = FP f Q ks e[[[Q<--ks.S]]] (SUC n)`` (fn t => REWRITE_TAC [t])
  THEN ONCE_REWRITE_TAC [STATES_def]
  THEN REWRITE_TAC [ENV_UPDATE]
  THEN ASSUM_LIST PROVE_TAC]]])

val GFP_CHAIN_INTER = prove(``!n' (f:'prop mu) Q (ks:('prop,'state) KS) e. (wfKS ks /\ IMF (mu Q..f)) ==>
                 (BIGINTER {P | ?n. n <= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)} = FP f Q ks e[[[Q<--ks.S]]] n')``,
REPEAT STRIP_TAC
THEN Induct_on `n'` THENL [
REWRITE_TAC [DECIDE ``!n. n<=0 = (n=0)``]
THEN REWRITE_TAC [BIGINTER]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN SIMP_TAC std_ss [SET_SPEC,EXTENSION], (* 0 *)
REWRITE_TAC [DECIDE ``!n n'. n<=(SUC n') = (n<=n' \/ (n=SUC n'))``]
THEN REWRITE_TAC [DECIDE ``!a b c.((a\/b)/\c)=((a/\c)\/(b/\c))``]
THEN SIMP_TAC std_ss [EXISTS_OR_THM]
THEN SIMP_TAC std_ss [GSYM (SIMP_RULE std_ss [IN_DEF] UNION_DEF)]
THEN SIMP_TAC std_ss [setLemmasTheory.BIGINTER_INTER]
THEN FULL_SIMP_TAC std_ss [SET_GSPEC]
THEN SIMP_TAC std_ss [BIGINTER,IN_DEF]
THEN SIMP_TAC std_ss [SET_GSPEC, ETA_CONV `` (\x. FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] (SUC n') x)``]
THEN ASSUM_LIST (fn t => PROVE_TAC (GFP_CHAIN::INTER_COMM::SUBSET_INTER_ABSORPTION::t))])

val GFP_FP_SUBSET = prove(``!n' (f:'prop mu) Q (ks:('prop,'state) KS) e.  (wfKS ks /\ IMF (mu Q..f) /\ (FP f Q ks e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n'))) ==>
                  ( FP f Q ks e[[[Q<--ks.S]]] n' SUBSET BIGINTER {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)})``,
REPEAT STRIP_TAC
THEN ASSUME_TAC (SPECL [``f:'prop mu``,``ks:('prop,'state) KS``,``e:string -> 'state -> bool``,``n':num``,``Q:string``] GFP_CHAIN_STABLE)
THEN UNDISCH_TAC `` wfKS (ks:('prop,'state) KS) /\ IMF (mu Q..f) ==> (FP f Q ks e[[[Q<--ks.S]]] n' =  FP f Q ks e[[[Q<--ks.S]]] (SUC n')) ==>
 !m. m >= n' ==> (FP f Q ks e[[[Q<--ks.S]]] m = FP f Q ks e[[[Q<--ks.S]]] n')``
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]]``,``P:num->'state->bool``)
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGINTER,SUBSET_DEF]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN ASSUM_LIST PROVE_TAC) (* TODO: the SUBSET should really be an = *)

val  NU_FP_STATES_LEM1 = prove(``!(f:'prop mu)ks e n' Q. wfKS (ks:('prop,'state) KS) /\ IMF (mu Q..f) ==>
   (FP f Q ks e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')) ==>
     (FP f Q ks e[[[Q<--ks.S]]] n' INTER  BIGINTER {P | ?n. n >= n' /\ (P =FP f Q ks e[[[Q<--ks.S]]] n)} =
      FP f Q ks e[[[Q<--ks.S]]] n')``,
REPEAT GEN_TAC
THEN ASSUME_TAC (SPEC_ALL GFP_FP_SUBSET)
THEN UNDISCH_TAC ``wfKS (ks:('prop,'state) KS) /\ (IMF (mu Q..f)) /\ (FP f Q ks e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')) ==>
      FP f Q ks e[[[Q<--ks.S]]] n' SUBSET BIGINTER {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)}``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]]``,``P:num -> 'state -> bool``)
THEN REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => PROVE_TAC (SUBSET_INTER_ABSORPTION::t)))

val NU_FP_STATES_LEM2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n' Q. (wfKS ks /\ IMF (mu Q..f)) ==>
                 ((FP f Q ks e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')) ==>
                   (BIGINTER {P | ?n. n <= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)} INTER
                     BIGINTER {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)} =
                    FP f Q ks e[[[Q<--ks.S]]] n'))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (GFP_CHAIN_INTER::(tl t)))
THEN ASSUME_TAC (SPEC_ALL NU_FP_STATES_LEM1)
THEN UNDISCH_TAC `` wfKS (ks:('prop,'state) KS) /\ IMF(mu Q.. f) ==> (FP f Q ks e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')) ==>
 (FP f Q ks e[[[Q<--ks.S]]] n' INTER BIGINTER {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)} =
  FP f Q ks e[[[Q<--ks.S]]] n')``
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]]``,``P:num -> 'state -> bool``)
THEN ASSUM_LIST PROVE_TAC)


val NU_FP_STATES1 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n' Q. (wfKS ks /\ IMF (mu Q..f)) ==>
                 ((FP f Q ks e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')) ==>
                       (STATES (nu Q.. f) ks e = FP f Q ks e[[[Q<--ks.S]]] n'))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (NU_BIGINTER::(tl t)))
THEN ASSUME_TAC (SPEC_ALL NU_FP_STATES_LEM2)
THEN UNDISCH_TAC `` wfKS (ks:('prop,'state) KS) /\ IMF (mu Q..f) ==> (FP f Q ks e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')) ==>
 (BIGINTER {P | ?n. n <= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)} INTER
   BIGINTER {P | ?n. n >= n' /\ (P = FP f Q ks e[[[Q<--ks.S]]] n)} =
  FP f Q ks e[[[Q<--ks.S]]] n')``
THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n' = FP f Q ks e[[[Q<--ks.S]]] (SUC n')``
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]]``,``P:num -> 'state -> bool``)
THEN REWRITE_TAC [GSYM BIGINTER_SPLIT]
THEN ASSUM_LIST PROVE_TAC)

val NU_FP_STATES = save_thm("NU_FP_STATES",REWRITE_RULE [IMF_MU_IFF_IMF_NU] NU_FP_STATES1)

val GFP_STRICT_CHAIN = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q. (wfKS ks /\ IMF (nu Q.. f)) ==>
				(~(FP f Q ks e[[[Q<--ks.S]]] n = FP f Q ks e[[[Q<--ks.S]]] (SUC n))) ==>
				FP f Q ks e[[[Q<--ks.S]]] (SUC n) PSUBSET FP f Q ks e[[[Q<--ks.S]]] n``,
				PROVE_TAC [GSYM PSUBSET_DEF,GFP_CHAIN,GSYM IMF_MU_IFF_IMF_NU])

val GFP_STRICT_CHAIN2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (nu Q.. f)) ==>
				(!n. ~(FP f Q ks e[[[Q<--ks.S]]] n = FP f Q ks e[[[Q<--ks.S]]] (SUC n))) ==>
				!n. (FP f Q ks e[[[Q<--ks.S]]] (SUC n) PSUBSET FP f Q ks e[[[Q<--ks.S]]] n)``,
				PROVE_TAC [GSYM PSUBSET_DEF,GFP_CHAIN,GSYM IMF_MU_IFF_IMF_NU])

val GFP_FP_FINITE = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e n. wfKS ks ==> FINITE (ks.S) ==> FINITE (FP f Q ks e[[[Q<--ks.S]]] n)``,
REPEAT GEN_TAC THEN Induct_on `n` THENL [
SIMP_TAC std_ss [STATES_def,ENV_EVAL,FINITE_EMPTY],
SIMP_TAC std_ss [STATES_FINITE,STATES_def]])

val GFP_FP_STRICT_CARD = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (nu Q .. f) /\ FINITE (ks.S)) ==>
				  (!n. ~(FP f Q ks e[[[Q<--ks.S]]] n = FP f Q ks e[[[Q<--ks.S]]] (SUC n))) ==>
				  (!n. CARD (FP f Q ks e[[[Q<--ks.S]]] (SUC n)) < CARD (FP f Q ks e[[[Q<--ks.S]]] n))``,
PROVE_TAC [GFP_FP_FINITE,PSUBSET_CARD_LT,GFP_STRICT_CHAIN2])

val CARD_S_GTE2 = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e n. wfKS ks /\ FINITE ks.S ==> CARD (FP f Q ks e[[[Q<--ks.S]]] n) <= CARD ks.S``,
FULL_SIMP_TAC arith_ss [wfKS_def,SUBSET_UNIV,GFP_FP_FINITE,SUBSET_CARD_LTE])

val CARD_EMPTY_LTE = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e n. CARD {} <= CARD (FP f Q ks e[[[Q<--ks.S]]] n)``,
FULL_SIMP_TAC arith_ss [CARD_EMPTY])

val NONE_LT_ALL = prove(``~(?i. !j. i<j)``,
SIMP_TAC std_ss [] THEN Induct_on `i` THENL [
EXISTS_TAC ``0`` THEN ARITH_TAC,
EXISTS_TAC ``i:num`` THEN ARITH_TAC])

val SDCF1 = prove(``!P. (!n. (P (SUC n)) < (P n))==>(!m n. (P (m+n)) <= (P n) - m)``,
REPEAT STRIP_TAC
THEN Induct_on `m` THENL [
SIMP_TAC arith_ss [] (* 0 *),
REWRITE_TAC [DECIDE ``!m n. SUC m + n = SUC (m + n)``]
THEN (SUBGOAL_THEN ``P (SUC (m+n)) < P n -m`` ASSUME_TAC) THENL [
ASSUM_LIST (fn t => PROVE_TAC ((DECIDE ``!l m n. l < m ==> m <= n ==> l < n``)::t)),
IMP_RES_TAC (DECIDE ``(P (SUC (m + n)) < P n -m) ==> (P (SUC (m + n)) <= (P n - m) - 1)``)
THEN FULL_SIMP_TAC arith_ss [SYM (DECIDE ``P n - (m + 1) = (P n - m) -1``)]]])

val STRICT_DEC_CHAIN_FALSE = prove(``!P. ~(!n. (P (SUC n)) < (P n))``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC (CONV_RULE (SIMP_CONV arith_ss []) (SPEC ``(P 0) : num`` (GEN ``m:num`` (SPEC_ALL (CONV_RULE (SIMP_CONV arith_ss [])
	          (GEN_ALL ( SPEC ``0`` (GEN ``n:num`` (SPEC_ALL (CONV_RULE (STRIP_QUANT_CONV RIGHT_IMP_FORALL_CONV)
                   (CONV_RULE (STRIP_QUANT_CONV RIGHT_IMP_FORALL_CONV) SDCF1)))))))))))
THEN (SUBGOAL_THEN ``P (SUC (P 0)) < P (P 0)`` ASSUME_TAC) THENL [
FULL_SIMP_TAC std_ss [],
ASSUM_LIST (fn t => PROVE_TAC ((DECIDE ``!n. ~(n<0)``)::t))])

val GEN_GFP_IDEM_LEM2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (nu Q.. f) /\ FINITE ks.S) ==>
			    ?k. (FP f Q ks e[[[Q<--ks.S]]] k = FP f Q ks e[[[Q<--ks.S]]] (SUC k))``,
REPEAT STRIP_TAC THEN SPOSE_NOT_THEN ASSUME_TAC THEN IMP_RES_TAC GFP_FP_STRICT_CARD
THEN FULL_SIMP_TAC std_ss [STRICT_DEC_CHAIN_FALSE])

val GFP_IDEM = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q. (wfKS ks /\ IMF (nu Q .. f)) ==>
		((FP f Q ks e[[[Q<--ks.S]]] n = FP f Q ks e[[[Q<--ks.S]]] (SUC n)) ==>
                       (STATES f ks e[[[Q<--(BIGINTER {P | ?i. (P = (FP f Q ks e[[[Q<--ks.S]]] i))})]]]
			= (BIGINTER {P | ?i. (P = (FP f Q ks e[[[Q<--ks.S]]] i))})))``,
		FULL_SIMP_TAC std_ss [CONV_RULE (STRIP_QUANT_CONV (FORK_CONV (ALL_CONV,STRIP_QUANT_CONV SYM_CONV))) NU_BIGINTER]
		THEN REPEAT STRIP_TAC THEN IMP_RES_TAC NU_FP_STATES
		THEN PAT_ASSUM ``STATES (nu Q.. f) (ks:('prop,'state) KS) e = FP f Q ks e[[[Q<--ks.S]]] n`` (fn t => REWRITE_TAC [t])
		THEN REWRITE_TAC [SYM (prove (``STATES f (ks:('prop,'state) KS) e[[[Q<--ks.S]]][[[Q<--FP f Q ks e[[[Q<--ks.S]]] n]]]
					      = STATES f ks e[[[Q<--FP f Q ks e[[[Q<--ks.S]]] n]]]``, PROVE_TAC [ENV_UPDATE]))]
		THEN UNDISCH_TAC ``FP f Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n = FP f Q ks e[[[Q<--ks.S]]] (SUC n)``
		THEN SPEC_TAC (``e[[[Q<--(ks:('prop,'state) KS).S]]]:string->'state->bool``,``e:string->'state->bool``)
		THEN ASSUM_LIST (fn t => PROVE_TAC (STATES_def::t)))


val GEN_GFP_IDEM =  save_thm("GEN_GFP_IDEM",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q. (wfKS ks /\ IMF (nu Q .. f) /\ FINITE ks.S) ==>
			     (STATES f ks e[[[Q<--(BIGINTER {P | ?i. (P = (FP f Q ks e[[[Q<--ks.S]]] i))})]]]
			      = (BIGINTER {P | ?i. (P = (FP f Q ks e[[[Q<--ks.S]]] i))}))``,
REPEAT STRIP_TAC THEN IMP_RES_TAC GEN_GFP_IDEM_LEM2 THEN IMP_RES_TAC GFP_IDEM THEN FULL_SIMP_TAC std_ss []))


val GEN_GFP_FP_IDEM = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q n. (wfKS ks /\ IMF (nu Q .. f) /\ FINITE ks.S) ==>
 (FP f Q ks e[[[Q<--(BIGINTER {P | ?i. (P = (FP f Q ks e[[[Q<--ks.S]]] i))})]]] n
			      = (BIGINTER {P | ?i. (P = (FP f Q ks e[[[Q<--ks.S]]] i))}))``,
Induct_on `n` THENL [
SIMP_TAC std_ss [STATES_def,ENV_EVAL],
FULL_SIMP_TAC std_ss [ENV_UPDATE,STATES_def,GEN_GFP_IDEM]])

val SPEC_GEN_GFP_FP_IDEM =  SPECL [``f:'prop mu``,``ks:('prop,'state) KS``,``e:string->'state->bool``,``Q:string``,``n':num``] GEN_GFP_FP_IDEM

val GEN_GFP_CHAIN = save_thm("GEN_GFP_CHAIN",prove(``!(f:'prop mu) ks e n Q X. (wfKS ks /\ IMF (nu Q .. f)  /\ STATES f ks e[[[Q<--X]]] SUBSET X) ==>
			 (FP f Q ks e[[[Q<--X]]] (SUC n) SUBSET FP f Q ks e[[[Q<--X]]] n)``,
REPEAT STRIP_TAC THEN Induct_on `n` THENL [
FULL_SIMP_TAC std_ss [STATES_def,ENV_UPDATE,ENV_EVAL],
 ONCE_REWRITE_TAC [STATES_def]
 THEN REWRITE_TAC [ENV_UPDATE]
 THEN FULL_SIMP_TAC std_ss [GSYM IMF_MU_IFF_IMF_NU,STATES_MONO,ENV_VAR_LEGAL]]))

val GEN_GFP_CHAIN_STABLE = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q gs. (wfKS ks /\ IMF (nu Q.. f)) ==>
                 ((FP f Q ks e[[[Q<--gs]]] n = FP f Q ks e[[[Q<--gs]]] (SUC n)) ==>
		  (!m. m>=n ==> (FP f Q ks e[[[Q<--gs]]] m = FP f Q ks e[[[Q<--gs]]] n)))``,
REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
THEN REPEAT STRIP_TAC THENL [
 PAT_ASSUM ``m=n`` (fn t => REWRITE_TAC [t]), (* m = n *)
 Induct_on `m` THENL [
  SIMP_TAC arith_ss [], (* 0 *)
  REWRITE_TAC [DECIDE ``(SUC m > n)=(m>=n)``]
  THEN REWRITE_TAC [DECIDE ``(m>=n) = ((m=n) \/ (m>n))``]
  THEN REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [], (* m=n *)
   PAT_ASSUM ``FP f Q (ks:('prop,'state) KS) e[[[Q<--gs]]] n = FP f Q ks e[[[Q<--gs]]] (SUC n)`` (fn t => REWRITE_TAC [t])
   THEN ONCE_REWRITE_TAC [STATES_def]
   THEN REWRITE_TAC [ENV_UPDATE]
   THEN ASSUM_LIST PROVE_TAC]]])

val GEN_GFP_CHAIN_INTER = prove(``!n (f:'prop mu) Q (ks:('prop,'state) KS) e X. (wfKS ks /\ IMF (nu Q.. f) /\ STATES f ks e[[[Q<--X]]] SUBSET X) ==> (BIGINTER {P | ?n'. n' <= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} = FP f Q ks e[[[Q<--X]]] n)``,
REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
 REWRITE_TAC [DECIDE ``!n. n<=0 = (n=0)``]
 THEN REWRITE_TAC [BIGINTER]
 THEN SIMP_TAC std_ss [SET_SPEC]
 THEN SIMP_TAC std_ss [SET_SPEC,EXTENSION], (* 0 *)
 REWRITE_TAC [DECIDE ``!n n'. n'<=(SUC n) = (n'<=n \/ (n'=SUC n))``]
 THEN REWRITE_TAC [RIGHT_AND_OVER_OR]
 THEN SIMP_TAC std_ss [EXISTS_OR_THM]
 THEN SIMP_TAC arith_ss [GSYM (SIMP_RULE std_ss [IN_DEF] UNION_DEF)]
 THEN SIMP_TAC std_ss [setLemmasTheory.BIGINTER_INTER]
 THEN FULL_SIMP_TAC std_ss [SET_GSPEC]
 THEN SIMP_TAC std_ss [BIGINTER,IN_DEF]
 THEN SIMP_TAC std_ss [SET_GSPEC, ETA_CONV `` (\x. FP (f:'prop mu) Q ks e[[[Q<--X]]] (SUC n) x)``]
 THEN PROVE_TAC [GEN_GFP_CHAIN,INTER_COMM,SUBSET_INTER_ABSORPTION,ENV_VAR_LEGAL]]
)


val GEN_GFP_FP_SUBSET = prove(``!n (f:'prop mu) Q (ks:('prop,'state) KS) e X.  (wfKS ks /\ IMF (nu Q.. f) /\ (FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n))) ==>
                  (BIGINTER {P | ?n'. n' >= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} = FP f Q ks e[[[Q<--X]]] n)``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC GEN_GFP_CHAIN_STABLE
THEN NTAC 2 (POP_ASSUM MP_TAC)
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--X]]]``,``P:num->'state->bool``)
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [BIGINTER,SUBSET_DEF]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN ONCE_REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN CONV_TAC (LAND_CONV (pred_setLib.SET_SPEC_CONV))
THEN EQ_TAC THENL [
REPEAT STRIP_TAC
THEN POP_ASSUM (fn t => POP_ASSUM (fn t' => ASSUME_TAC (Q.SPEC `n'` t') THEN ASSUME_TAC t))
THEN POP_ASSUM (fn t => ASSUME_TAC (CONV_RULE ((QUANT_CONV LEFT_IMP_EXISTS_CONV) THENC SWAP_VARS_CONV) t))
THEN POP_ASSUM (fn t => ASSUME_TAC (Q.SPECL [`n`,`P (n:num)`] t))
THEN FULL_SIMP_TAC arith_ss [],
REPEAT STRIP_TAC
THEN PAT_ASSUM ``!x.t`` (fn t => ASSUME_TAC (Q.SPEC `n'` t))
THEN ASSUM_LIST PROVE_TAC])


val GEN_NU_FP_STATES_LEM1 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q X. wfKS ks /\ IMF (nu Q..f) ==>
   (FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)) ==>
     (FP f Q ks e[[[Q<--X]]] n INTER  BIGINTER {P | ?n'. n' >= n /\ (P =FP f Q ks e[[[Q<--X]]] n')} =
      FP f Q ks e[[[Q<--X]]] n)``,
REPEAT STRIP_TAC THEN IMP_RES_TAC  GEN_GFP_FP_SUBSET
THEN NTAC 2 (POP_ASSUM MP_TAC)
THEN SPEC_TAC (``FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--X]]]``,``P:num->'state->bool``)
THEN REPEAT STRIP_TAC
THEN ASM_REWRITE_TAC [INTER_IDEMPOT])

val GEN_NU_FP_STATES_LEM2 = prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q X. (wfKS ks /\ IMF (nu Q..f) /\ STATES f ks e[[[Q<--X]]] SUBSET X) ==>
                 ((FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)) ==>
                   (BIGINTER {P | ?n'. n' <= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} INTER
                     BIGINTER {P | ?n'. n' >= n /\ (P = FP f Q ks e[[[Q<--X]]] n')} = FP f Q ks e[[[Q<--X]]] n))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (GEN_GFP_CHAIN_INTER::(tl t)))
THEN IMP_RES_TAC  GEN_NU_FP_STATES_LEM1)

val GEN_GFP_SUBSET =  prove(``!(f:'prop mu) ks e Q X. wfKS ks /\ IMF (nu Q ..f) /\ FINITE ks.S ==>
 BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} SUBSET X ==>
!n. BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} SUBSET FP f Q ks e[[[Q<--X]]] n``,
REPEAT STRIP_TAC
THEN Induct_on `n` THENL [
ASM_REWRITE_TAC [STATES_def,ENV_EVAL,ENV_UPDATE], (* 0 *)
`STATES f ks e[[[Q<--BIGINTER {P | ?n. P = FP f Q ks e[[[Q<--ks.S]]] n}]]] SUBSET STATES f ks e[[[Q<--FP f Q ks e[[[Q<--X]]] n]]]` by FULL_SIMP_TAC std_ss [GSYM IMF_MU_IFF_IMF_NU,STATES_MONO,ENV_VAR_LEGAL]
THEN REWRITE_TAC [STATES_def,ENV_UPDATE]
THEN IMP_RES_TAC GEN_GFP_IDEM
THEN ASSUM_LIST METIS_TAC])

val GEN_GFP_INTER_SUBSET =  prove(``!(f:'prop mu) ks e Q X. wfKS ks /\ IMF (nu Q ..f) /\ FINITE ks.S ==> BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} SUBSET X ==>
BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} SUBSET BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--X]]] n)}``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC GEN_GFP_SUBSET
THEN ASSUM_LIST (fn t => METIS_TAC (LEFT_BIGINTER_SUBSET::t)))

val GFP_ITER_EQ = prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e X .
  (wfKS ks /\ IMF (nu Q ..f) /\ FINITE ks.S) ==>
		BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} SUBSET X ==>
		(BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} =
		 BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--X]]] n)})``,
 REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM SUBSET_EQ] THEN CONJ_TAC THENL [
IMP_RES_TAC GEN_GFP_INTER_SUBSET,
`!n. FP f Q ks e[[[Q<--X]]] n SUBSET FP (f:'prop mu) Q (ks:('prop,'state) KS) e[[[Q<--ks.S]]] n` by
    (Induct_on `n` THENL [FULL_SIMP_TAC std_ss [STATES_def,EMPTY_SUBSET,ENV_EVAL,wfKS_def,SUBSET_UNIV],
	    FULL_SIMP_TAC std_ss [GSYM IMF_MU_IFF_IMF_NU,STATES_def,STATES_MONO,ENV_VAR_LEGAL,ENV_UPDATE]])
THEN FULL_SIMP_TAC std_ss [BIGINTER_SUBSET_IMP]
])

val GEN_NU_FP_STATES = save_thm("GEN_NU_FP_STATES",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e n Q X. wfKS ks /\ IMF (nu Q ..f) /\ FINITE ks.S /\
                  STATES f ks e[[[Q<--X]]] SUBSET X ==> BIGINTER {P | ?n. (P = FP f Q ks e[[[Q<--ks.S]]] n)} SUBSET X  ==>
                 ((FP f Q ks e[[[Q<--X]]] n = FP f Q ks e[[[Q<--X]]] (SUC n)) ==>
                       (STATES (nu Q.. f) ks e = FP f Q ks e[[[Q<--X]]] n))``,
REPEAT STRIP_TAC
THEN ASSUM_LIST (fn t => SIMP_TAC std_ss (NU_BIGINTER::(tl t)))
THEN IMP_RES_TAC GEN_NU_FP_STATES_LEM2
THEN IMP_RES_TAC GFP_ITER_EQ
THEN FULL_SIMP_TAC std_ss [GSYM BIGINTER_SPLIT]))

(* thms used by checker when initialising fix-point computations *)

val MS_FP = save_thm("MS_FP",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q s X n. MU_SAT f ks e[[[Q<--FP f Q ks e[[[Q<--X]]] n]]] s = FP f Q ks e[[[Q<--X]]] (SUC n) s``,
SIMP_TAC std_ss [MU_SAT_def,STATES_def,IN_DEF,ENV_UPDATE]))

val MS_FP_INIT = save_thm("MS_FP_INIT",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q s X n. wfKS ks ==> (MU_SAT (RV Q) ks e[[[Q<--FP f Q ks e[[[Q<--X]]] n]]] s = FP f Q ks e[[[Q<--X]]] n s)``,
RW_TAC std_ss [MU_SAT_def,STATES_def,IN_DEF,ENV_UPDATE,ENV_EVAL,UNIV_DEF,wfKS_def] THEN SIMP_TAC std_ss [SET_GSPEC]))

val GEN_MS_FP_INIT = save_thm("GEN_MS_FP_INIT",prove(``!(ks:('prop,'state) KS) e Q s X. wfKS ks ==> (MU_SAT (RV Q) ks e[[[Q<--X]]] s = X s)``,
RW_TAC std_ss [MU_SAT_def,STATES_def,IN_DEF,ENV_UPDATE,ENV_EVAL,UNIV_DEF,wfKS_def] THEN SIMP_TAC std_ss [SET_GSPEC]))

val LFP_INIT = save_thm("LFP_INIT",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q s. wfKS ks ==> (FP f Q  ks e[[[Q<--{}]]] 0 s = F)``,
SIMP_TAC std_ss [EMPTY_DEF,GSYM IN_DEF,STATES_def,ENV_UPDATE_def]))

val GFP_INIT = save_thm("GFP_INIT",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q s. wfKS ks ==> (FP f Q  ks e[[[Q<--ks.S]]] 0 s = T)``,
SIMP_TAC std_ss [wfKS_def,UNIV_DEF,GSYM IN_DEF,STATES_def,ENV_UPDATE_def]))

val GEN_FP_INIT = save_thm("GEN_FP_INIT",prove(``!(f:'prop mu) (ks:('prop,'state) KS) e Q X s. wfKS ks ==> (FP f Q  ks e[[[Q<--X]]] 0 s = X s)``,
SIMP_TAC std_ss [EMPTY_DEF,GSYM IN_DEF,STATES_def,ENV_UPDATE_def]))

(* thm used by checker to go from one round of the iteration to the next *)

val SAT_RV_ENV_SUBST = save_thm("SAT_RV_ENV_SUBST",prove(``!(f:'prop mu) Q (ks:('prop,'state) KS) e n s. wfKS ks ==> (MU_SAT (RV Q) ks e[[[Q<--FP f Q ks e (SUC n)]]] s = MU_SAT f ks e[[[Q<--FP f Q ks e n]]] s)``,
SIMP_TAC std_ss [wfKS_def,MU_SAT_def,STATES_def]
THEN SIMP_TAC std_ss [SET_SPEC,IN_UNIV]
THEN SIMP_TAC std_ss [ENV_UPDATE_def]
THEN SIMP_TAC std_ss [IN_DEF]))

(* trivial fol thms used by checker; pre-proved for speed *)

val fol1 = save_thm("fol1",prove(``!p q x y. ((p ==> x) /\ (q ==> y)) ==> ((p /\ q) ==> (x /\ y))``,PROVE_TAC []))

val fol2 = save_thm("fol2",prove(``!p x y. (p ==> (x /\ y)) ==> (p ==> (x \/ y))``,PROVE_TAC []))

val fol3 = save_thm("fol3",prove(``!p x y z. ((x /\ y) ==> z) ==>((p ==> (x/\y))==>(p==>z))``,PROVE_TAC []))

val fol4 = save_thm("fol4",prove(``!p x y z. ((x \/ y) ==> z) ==>((p ==> (x\/y))==>(p==>z))``,PROVE_TAC []))

val fol5 = save_thm("fol5",prove(``!p x y. (x ==> y) ==> ((p==>x)==>(p==>y))``,PROVE_TAC []))

(* ---------------AP substitution used by abstraction engine--------------------*)

fun ap_subst_fp_TAC gfp (asl:term list,w) =
let val (w1l,w1r) = (rand o hd o snd o strip_comb ## rand o hd o snd o strip_comb)(dest_eq w)
    val fp_thm = if gfp then MU_SAT_GFP else MU_SAT_LFP
    val dest_b = if gfp then dest_forall else dest_exists
    val (fa,w2) = strip_forall (concl  (INST_TYPE [alpha |-> ``:'state``,beta|->``:'prop``] fp_thm))
    val w2l = rhs(concl(ISPECL [``s':'state``,``(ks:('prop,'state) KS)``,``e:string -> 'state -> bool``,``s:string``,w1l]
			   (mk_thm([],list_mk_forall (fa,snd(dest_imp w2))))))
    val w2r = rhs(concl(ISPECL [``s':'state``,``(ks:('prop,'state) KS)``,``e:string -> 'state -> bool``,``s:string``,w1r]
			   (mk_thm([],list_mk_forall (fa,snd(dest_imp w2))))))
    val gl = list_mk_forall([``n:num``,``e:string -> 'state -> bool``,``s':'state``],mk_eq(snd(dest_b(w2l)),snd(dest_b(w2r))))
in
    (FULL_SIMP_TAC std_ss [fp_thm]
    THEN SUBGOAL_THEN gl ASSUME_TAC
    THENL
    [
     REWRITE_TAC [GSYM EXTENSION]
     THEN Induct_on `n` THENL
     [
      SIMP_TAC std_ss [STATES_def,ENV_UPDATE_def],
      SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
      THEN REWRITE_TAC [EXTENSION]
      THEN REWRITE_TAC [GSYM MU_SAT_def]
      THEN ASSUM_LIST PROVE_TAC
      ],
     ASSUM_LIST PROVE_TAC
     ]) (asl,w)
end

val AP_SUBST_LEM = prove(``!(f:'prop mu) g ap (ks:('prop,'state) KS).
			    wfKS ks ==> (IS_PROP g) ==> (!e s. MU_SAT (AP ap) ks e s = MU_SAT g ks e s)
			    ==> (!e s. MU_SAT f ks e s = MU_SAT (AP_SUBST g ap f) ks e s)``,
Induct_on `g`
THEN Induct_on `f`
THEN RW_TAC std_ss [IS_PROP_def,AP_SUBST_def,MU_SAT_NEG,MU_SAT_CONJ,MU_SAT_DISJ,MU_SAT_DMD,MU_SAT_BOX,MU_SAT_RV]
THEN FULL_SIMP_TAC std_ss [IS_PROP_def,AP_SUBST_def,MU_SAT_NEG,MU_SAT_CONJ,MU_SAT_DISJ,MU_SAT_DMD,MU_SAT_BOX,MU_SAT_RV]
THEN RES_TAC
THEN (TRY (PROVE_TAC []))
THEN FIRST_PROVE [NTAC 6 (POP_ASSUM (K ALL_TAC)) THEN ap_subst_fp_TAC true,
		  NTAC 6 (POP_ASSUM (K ALL_TAC)) THEN ap_subst_fp_TAC false,
		  ap_subst_fp_TAC true,
		  ap_subst_fp_TAC false])

val lm1 = prove(``!(g:'prop mu) (ks:('prop,'state) KS) e e'. wfKS ks ==> (IS_PROP g) ==>
	 (!s. MU_SAT g ks e s = MU_SAT g ks e' s)``,
Induct_on `g` THEN RW_TAC std_ss [SET_SPEC,IS_PROP_def]
THENL[
 FULL_SIMP_TAC std_ss [SET_SPEC,IS_PROP_def,MU_SAT_def,STATES_def,wfKS_def,IN_UNIV,NOT_IN_EMPTY,SET_SPEC],
FULL_SIMP_TAC std_ss [SET_SPEC,IS_PROP_def,MU_SAT_def,STATES_def,wfKS_def,IN_UNIV,NOT_IN_EMPTY,SET_SPEC],
metisLib.METIS_TAC [MU_SAT_NEG],
metisLib.METIS_TAC [MU_SAT_CONJ],
metisLib.METIS_TAC [MU_SAT_DISJ],
metisLib.METIS_TAC [MU_SAT_AP]])

val lm2 = prove(``!(ap:'prop). IS_PROP (AP ap)``,REWRITE_TAC [IS_PROP_def])

val lm3 = prove(``!(g:'prop mu) ap (ks:('prop,'state) KS) e.
			    wfKS ks ==> (IS_PROP g) ==>
				((!e s. MU_SAT (AP ap) ks e s = MU_SAT g ks e s)
			    = (!s. MU_SAT (AP ap) ks e s = MU_SAT g ks e s))``,
REPEAT STRIP_TAC THEN EQ_TAC THENL [
metisLib.METIS_TAC [],
ASSUME_TAC lm2
THEN metisLib.METIS_TAC [lm1]
])

(* subst of ap's by propositional formulas with the same semantics preserves overall semantics *)
(* i.e. the principle of subst of equals for equals, for mu ap's *)
val AP_SUBST = save_thm("AP_SUBST",prove(``!(f:'prop mu) g ap (ks:('prop,'state) KS) e (s:'state).
			    wfKS ks ==> (IS_PROP g) ==> (!s. MU_SAT (AP ap) ks e s = MU_SAT g ks e s)
			    ==> (MU_SAT f ks e s = MU_SAT (AP_SUBST g ap f) ks e s)``,
metisLib.METIS_TAC [AP_SUBST_LEM,lm3]))

val lm4 = prove(``!(f:'prop mu) g ap (ks:('prop,'state) KS)  e (s:'state).
			    wfKS ks ==> (IS_PROP g) ==> (!s. MU_SAT (AP ap) ks e s = MU_SAT g ks e s)
			    ==> ((s IN ks.S0 ==> MU_SAT f ks e s) = (s IN ks.S0 ==> MU_SAT (AP_SUBST g ap f) ks e s))``,
metisLib.METIS_TAC [AP_SUBST])

val AP_SUBST_MODEL = save_thm("AP_SUBST_MODEL",prove(``!(f:'prop mu) g ap (ks:('prop,'state) KS)   e (s:'state).
			    wfKS ks ==> (IS_PROP g) ==> (!s. MU_SAT (AP ap) ks e s = MU_SAT g ks e s)
			    ==> (MU_MODEL_SAT f ks e = MU_MODEL_SAT (AP_SUBST g ap f) ks e)``,
metisLib.METIS_TAC [lm4,MU_MODEL_SAT_def]))

(*----------- bisimilarity preserves mu properties (used to eliminate data independent vars of any type) ---------------*)

val MU_BISIM_STATES = save_thm("MU_BISIM_STATES",prove(``!f M1 M2 e1 e2 s1 s2 BS.
		    wfKS M1 ==>
		    wfKS M2 ==>
		    (!p s1 s2. AP p SUBF f ==> (M1.L s1 p = M2.L s2 p)) ==>
		    BISIM M1 M2 BS ==>
		    (!(Q:string) s1 s2. BS(s1,s2) ==> (s1 IN e1 Q = s2 IN e2 Q)) ==>
		    BS(s1,s2) ==>
		    (MU_SAT f M1 e1 s1 = MU_SAT f M2 e2 s2)``,
Induct_on `f` THENL [
SIMP_TAC std_ss [MU_SAT_T],(* T *)
SIMP_TAC std_ss [MU_SAT_F],(* F *)
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MU_SAT_NEG,SUB_AP_NEG] THEN RES_TAC,(* ~ *)
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MU_SAT_CONJ,SUB_AP_CONJ,DISJ_IMP_THM,FORALL_AND_THM]
THEN RES_TAC
THEN metisLib.METIS_TAC [],(* /\ *)
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MU_SAT_DISJ,SUB_AP_DISJ,DISJ_IMP_THM,FORALL_AND_THM]
THEN RES_TAC
THEN metisLib.METIS_TAC [],(* \/ *)
RW_TAC std_ss [MU_SAT_RV,IN_DEF], (* RV *)
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MU_SAT_AP,SUBF_REFL], (* AP *)
REPEAT STRIP_TAC
THEN Q.PAT_ASSUM `!t s1 s2. P SUBF P' ==>Q` (fn t => ASSUME_TAC (REWRITE_RULE [SUB_AP_DMD] t))
THEN FULL_SIMP_TAC std_ss [MU_SAT_DMD]
THEN Q.PAT_ASSUM `BS t` (fn t => RES_TAC THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
					 THEN POP_ASSUM (fn t' => NTAC 2 (POP_ASSUM (K ALL_TAC))
								  THEN POP_ASSUM (fn t'' => NTAC 3 (POP_ASSUM (K ALL_TAC))
                                                                       THEN ASSUME_TAC t'' THEN ASSUME_TAC t'))
					 THEN ASSUME_TAC t)
THEN FULL_SIMP_TAC std_ss [BISIM_def]
THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THENL [
  Q.PAT_ASSUM `!a b. P ==> (Q=Q')` (fn t => ASSUME_TAC (Q.SPECL [`s2'`,`q`] t))
  THEN Q.EXISTS_TAC `s2'`
  THEN metisLib.METIS_TAC [],
  Q.PAT_ASSUM `!a b. P ==> (Q=Q')` (fn t => ASSUME_TAC (Q.SPECL [`q`,`s1'`] t))
  THEN Q.EXISTS_TAC `s1'`
  THEN metisLib.METIS_TAC []
 ], (* <<>>*)
REPEAT STRIP_TAC
THEN Q.PAT_ASSUM `!t s1 s2. P SUBF P' ==>Q` (fn t => ASSUME_TAC (REWRITE_RULE [SUB_AP_BOX] t))
THEN FULL_SIMP_TAC std_ss [MU_SAT_BOX]
THEN Q.PAT_ASSUM `BS t` (fn t => RES_TAC THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
					 THEN POP_ASSUM (fn t' => NTAC 2 (POP_ASSUM (K ALL_TAC))
								  THEN POP_ASSUM (fn t'' => NTAC 3 (POP_ASSUM (K ALL_TAC))
                                                                       THEN ASSUME_TAC t'' THEN ASSUME_TAC t'))
					 THEN ASSUME_TAC t)
THEN FULL_SIMP_TAC std_ss [BISIM_def]
THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN  metisLib.METIS_TAC [], (* [[]] *)
REPEAT STRIP_TAC
THEN POP_ASSUM MP_TAC
THEN MAP_EVERY Q.SPEC_TAC [(`s2`,`s2`),(`s1`,`s1`)]
THEN FULL_SIMP_TAC std_ss [MU_SAT_LFP]
THEN Q.SUBGOAL_THEN `!n s1 s2. BS (s1,s2) ==> (s1 IN FP f s M1 e1[[[s<--{}]]] n = s2 IN FP f s M2 e2[[[s<--{}]]] n)`  ASSUME_TAC
 THENL [
  Induct_on `n` THENL [
     SIMP_TAC std_ss [STATES_def,ENV_EVAL,NOT_IN_EMPTY], (* 0 *)
     REPEAT STRIP_TAC THEN SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
     THEN Q.PAT_ASSUM `!t s1 s2. P SUBF P' ==>Q` (fn t => ASSUME_TAC (REWRITE_RULE [SUB_AP_MU] t))
     THEN Q.PAT_ASSUM `!M1 M2 e1 e2. P` (fn t => ASSUME_TAC (Q.SPECL [`M1`,`M2`,
								       `e1[[[s<--FP f s M1 e1[[[s<--{}]]] n]]]`,
								       `e2[[[s<--FP f s M2 e2[[[s<--{}]]] n]]]`] t))
     THEN RES_TAC
     THEN NTAC 8 (POP_ASSUM (K ALL_TAC))
     THEN POP_ASSUM (fn t => NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN ASSUME_TAC t)
     THEN POP_ASSUM_LIST (fn l => MAP_EVERY ASSUME_TAC (List.take(l,4)))
     THEN Q.SUBGOAL_THEN `(!Q s1 s2.
		BS (s1,s2) ==>(s1 IN e1[[[s<--FP f s M1 e1[[[s<--{}]]] n]]] Q = s2 IN e2[[[s<--FP f s M2 e2[[[s<--{}]]] n]]] Q))`
              ASSUME_TAC
     THENL [
      POP_ASSUM_LIST (fn l => MAP_EVERY ASSUME_TAC (List.take(l,2)))
      THEN REPEAT STRIP_TAC
      THEN Cases_on `Q=s` THENL [
       FULL_SIMP_TAC std_ss [ENV_EVAL],
       FULL_SIMP_TAC std_ss [ENV_UPDATE_INV]
      ],
      RES_TAC THEN metisLib.METIS_TAC [MU_SAT_def,IN_DEF]
     ]
   ],
  metisLib.METIS_TAC []
 ], (* mu *)
REPEAT STRIP_TAC
THEN POP_ASSUM MP_TAC
THEN MAP_EVERY Q.SPEC_TAC [(`s2`,`s2`),(`s1`,`s1`)]
THEN FULL_SIMP_TAC std_ss [MU_SAT_GFP]
THEN Q.SUBGOAL_THEN `!n s1 s2. BS (s1,s2) ==> (s1 IN FP f s M1 e1[[[s<--M1.S]]] n = s2 IN FP f s M2 e2[[[s<--M2.S]]] n)`  ASSUME_TAC
 THENL [
  Induct_on `n` THENL [
     FULL_SIMP_TAC std_ss [STATES_def,ENV_EVAL,IN_UNIV,wfKS_def], (* 0 *)
     REPEAT STRIP_TAC THEN SIMP_TAC std_ss [STATES_def,ENV_UPDATE]
     THEN Q.PAT_ASSUM `!t s1 s2. P SUBF P' ==>Q` (fn t => ASSUME_TAC (REWRITE_RULE [SUB_AP_NU] t))
     THEN Q.PAT_ASSUM `!M1 M2 e1 e2. P` (fn t => ASSUME_TAC (Q.SPECL [`M1`,`M2`,
								       `e1[[[s<--FP f s M1 e1[[[s<--M1.S]]] n]]]`,
								       `e2[[[s<--FP f s M2 e2[[[s<--M2.S]]] n]]]`] t))
     THEN RES_TAC
     THEN NTAC 8 (POP_ASSUM (K ALL_TAC))
     THEN POP_ASSUM (fn t => NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN ASSUME_TAC t)
     THEN POP_ASSUM_LIST (fn l => MAP_EVERY ASSUME_TAC (List.take(l,4)))
     THEN Q.SUBGOAL_THEN `(!Q s1 s2.
		BS (s1,s2) ==>(s1 IN e1[[[s<--FP f s M1 e1[[[s<--M1.S]]] n]]] Q = s2 IN e2[[[s<--FP f s M2 e2[[[s<--M2.S]]] n]]] Q))`
              ASSUME_TAC
     THENL [
      POP_ASSUM_LIST (fn l => MAP_EVERY ASSUME_TAC (List.take(l,2)))
      THEN REPEAT STRIP_TAC
      THEN Cases_on `Q=s` THENL [
       FULL_SIMP_TAC std_ss [ENV_EVAL],
       FULL_SIMP_TAC std_ss [ENV_UPDATE_INV]

      ],
      RES_TAC THEN metisLib.METIS_TAC [MU_SAT_def,IN_DEF]
     ]
   ],
  metisLib.METIS_TAC []
 ] (* nu *)
]))

val MU_BISIM = save_thm("MU_BISIM",prove(``!f M1 M2 e1 e2 BS.
			wfKS M1 ==>
			wfKS M2 ==>
			(!p s1 s2. AP p SUBF f ==> (M1.L s1 p = M2.L s2 p)) ==>
			(!s1 s2. BS(s1,s2) ==> (s1 IN M1.S0 = s2 IN M2.S0)) ==>
			BISIM M1 M2 BS ==>
			(!(Q:string) s1 s2. BS(s1,s2) ==> (s1 IN e1 Q = s2 IN e2 Q)) ==>
			(!s1. ?s2. BS(s1,s2)) ==>
			(!s2. ?s1. BS(s1,s2)) ==>
			(MU_MODEL_SAT f M1 e1 = MU_MODEL_SAT f M2 e2)``,
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [MU_MODEL_SAT_def]
THEN REPEAT STRIP_TAC
THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
 Q.PAT_ASSUM `!s2. ?s1. BS(s1,s2)` (fn t => ASSUME_TAC t THEN ASSUME_TAC(Q.SPEC `s` t))
 THEN FULL_SIMP_TAC std_ss []
 THEN  Q.PAT_ASSUM `!s1 s2. BS (s1,s2) ==> (s1 IN M1.S0 = s2 IN M2.S0)` (fn t => IMP_RES_TAC (Q.SPECL [`s1`,`s`] t))
 THEN  Q.PAT_ASSUM `!s. s IN M1.S0 ==> MU_SAT f M1 e1 s` (fn t => ASSUME_TAC (Q.SPEC `s1` t))
 THEN IMP_RES_TAC MU_BISIM_STATES
 THEN NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM (fn t => NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN ASSUME_TAC t)
 THEN FULL_SIMP_TAC std_ss [],
 Q.PAT_ASSUM `!s1. ?s2. BS(s1,s2)` (fn t => Q.PAT_ASSUM `!s1. ?s2. BS(s1,s2)` (fn t => ASSUME_TAC t THEN ASSUME_TAC(Q.SPEC `s` t)))
 THEN FULL_SIMP_TAC std_ss []
 THEN  Q.PAT_ASSUM `!s1 s2. BS (s1,s2) ==> (s1 IN M1.S0 = s2 IN M2.S0)` (fn t => IMP_RES_TAC (Q.SPECL [`s`,`s2`] t))
 THEN  Q.PAT_ASSUM `!s. s IN M2.S0 ==> MU_SAT f M2 e1 s` (fn t => ASSUME_TAC (Q.SPEC `s2` t))
 THEN IMP_RES_TAC MU_BISIM_STATES
 THEN NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM (fn t => NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN ASSUME_TAC t)
 THEN FULL_SIMP_TAC std_ss []
]))

val _ = export_theory()







