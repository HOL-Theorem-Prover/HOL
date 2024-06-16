(*
app load
["pairTheory", "pairLib", "pairTools", "pairSyntax", "pred_setTheory", "pred_setLib",
 "stringLib", "listTheory", "rich_listTheory", "simpLib", "stringTheory", "sumTheory",
 "ksTheory", "numLib", "setLemmasTheory", "muSyntaxTheory", "muTheory", "res_quanLib",
 "envTheory", "ctlTheory", "metisLib", "res_quanLib"];
*)

open HolKernel Parse boolLib bossLib

val _ = new_theory "ctl2mu";

open pairTheory;
open pairLib;
open pairTools;
open pairSyntax;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open rich_listTheory;
open simpLib;
open stringTheory;
open sumTheory;
open ksTheory;
open numLib;
open setLemmasTheory;
open muSyntaxTheory
open muTheory;
open res_quanLib
open envTheory
open ctlTheory
open metisLib
open res_quanLib

val _ = numLib.temp_prefer_num();

fun tsimps ty =
    let val {convs,rewrs} = TypeBase.simpls_of ty in rewrs end;

val BEXP2MU_def = Define `
(BEXP2MU (B_TRUE: 'prop bexp) = (TR:'prop mu)) /\
(BEXP2MU (B_PROP (b:'prop)) = (AP (b:'prop))) /\
(BEXP2MU (B_NOT be) = ~(BEXP2MU be)) /\
(BEXP2MU (B_AND(be1,be2)) = (BEXP2MU be1) /\ (BEXP2MU be2))`;

val CTL2MU_def = Define `
        (CTL2MU (C_BOOL b) = BEXP2MU b) /\
        (CTL2MU (C_NOT f)  = ~(CTL2MU f)) /\
        (CTL2MU (C_AND(f,g))  = (CTL2MU f) /\ (CTL2MU g )) /\
        (CTL2MU (C_EX f)  = <<".">> (CTL2MU f)) /\
        (CTL2MU (C_EG f)  = nu "Q" .. ((CTL2MU f ) /\ <<".">> (RV "Q"))) /\
        (CTL2MU (C_EU(f,g))  = mu "Q" .. ((CTL2MU g) \/ ((CTL2MU f) /\ <<".">> (RV "Q"))))`;

val ctl2muks_def = Define `ctl2muks (M : ('prop,'state) kripke_structure) =
    <| S  := M.S;
       S0 := M.S0;
       T  := (\q. M.R);
       ap := M.P;
       L  := M.L |>`;

val REST_RESTN = save_thm("REST_RESTN",prove(``!p. REST p = RESTN p (1:num)``,
Induct_on `p` THEN REWRITE_TAC [REST_def,RESTN_def,DECIDE ``1 = SUC 0``]));

val ELEM_REST = save_thm("ELEM_REST",prove(``!(p:'state path) (n:num). ELEM (REST p) n = ELEM p (n+1)``,
Induct_on `p` THEN Induct_on `n` THENL [
REWRITE_TAC [ELEM_def,RESTN_def,REST_def,DECIDE ``1 = SUC 0``, DECIDE ``0+1=SUC 0``], (* finite, 0 *)
FULL_SIMP_TAC std_ss [ELEM_def,RESTN_def,REST_def,DECIDE ``SUC n + 1 = SUC (SUC n)``,DECIDE ``n+1 = SUC n``], (* finite, SUC n *)
REWRITE_TAC [ELEM_def,RESTN_def,REST_def,DECIDE ``1 = SUC 0``, DECIDE ``0+1=SUC 0``], (* infinite, 0 *)
FULL_SIMP_TAC std_ss [ELEM_def,RESTN_def,REST_def,DECIDE ``SUC n + 1 = SUC (SUC n)``,DECIDE ``n+1 = SUC n``] (* infinite, SUC n *)
]));

val PATH_REST = save_thm("PATH_REST",prove(``!(p:'state path) (M: ('prop,'state) kripke_structure) (s:'state). PATH M p s ==> PATH M (REST p) (ELEM p 1)``,
Induct_on `p` THENL [
 SIMP_TAC std_ss [PATH_def,IS_INFINITE_def],
 REWRITE_TAC [PATH_def]
 THEN REWRITE_TAC [REST_INFINITE,IS_INFINITE_def]
 THEN REPEAT STRIP_TAC THENL [
  SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def],
  FULL_SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def]
  THEN POP_ASSUM (fn t => ASSUME_TAC (SPEC ``(n:num)+1`` t))
  THEN FULL_SIMP_TAC arith_ss []]]));

val EG_LEMMA = prove(``!(M :('prop,'state) kripke_structure) (f:'prop ctl) (s:'state). C_SEM M (C_EG f) s = C_SEM M (C_AND(f,C_EX (C_EG f))) s``,
REPEAT GEN_TAC THEN EQ_TAC THENL [
REWRITE_TAC [C_SEM_def,IN_DEF]
THEN BETA_TAC
THEN REPEAT STRIP_TAC THENL [
 FULL_SIMP_TAC resq_ss [PATH_def,IN_DEF]
 THEN Induct_on `p` THENL [
  SIMP_TAC std_ss [IS_INFINITE_def],
  SIMP_TAC std_ss [PLENGTH_def,xnum_to_def,IS_INFINITE_def]
  THEN SIMP_TAC arith_ss [] THEN GEN_TAC THEN PROVE_TAC []], (* ==>, f case *)
 EXISTS_TAC ``p:'state path``
 THEN REPEAT STRIP_TAC THENL [
  ASM_REWRITE_TAC [],
  EXISTS_TAC ``REST (p:'state path)``
  THEN REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [PATH_def]
   THEN REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC std_ss [IS_INFINITE_REST],
    FULL_SIMP_TAC std_ss [ELEM_REST],
    SIMP_TAC std_ss [ELEM_REST,DECIDE ``SUC n + 1 = n + 2``,DECIDE ``SUC n + 1 + 1 = n + 3``]
    THEN ASSUM_LIST (fn t => PROVE_TAC ((DECIDE ``((n:num)+2)+1 = n + 3``)::t))], (* |- PATH M (REST p) (ELEM p 1) *)
   REWRITE_TAC [ELEM_REST]
   THEN Induct_on `p` THENL [
    REWRITE_TAC [PATH_def,IS_INFINITE_def], (* finite *)
    REWRITE_TAC [PATH_def,IS_INFINITE_def]
    THEN REWRITE_TAC [REST_INFINITE,PLENGTH_def]
    THEN SIMP_TAC resq_ss [IN_DEF,xnum_to_def]
    THEN SIMP_TAC arith_ss []]]]], (* ==> *)
REWRITE_TAC [C_SEM_def,IN_DEF]
THEN BETA_TAC
THEN REPEAT STRIP_TAC
THEN Induct_on `p` THEN Induct_on `p'`
THEN REWRITE_TAC [PATH_def,IS_INFINITE_def]
THEN REPEAT STRIP_TAC
THEN EXISTS_TAC ``INFINITE (\n. if (n=0) then s else ((f':num->'state) (n-1)))``
THEN SIMP_TAC std_ss [IS_INFINITE_def]
THEN FULL_SIMP_TAC resq_ss [IN_DEF,xnum_to_def,PLENGTH_def]
THEN SIMP_TAC arith_ss []
THEN REPEAT STRIP_TAC THENL [
 REWRITE_TAC [ELEM_def,RESTN_INFINITE]
 THEN SIMP_TAC arith_ss []
 THEN SIMP_TAC std_ss [HEAD_def], (* p0=s case *)
 Induct_on `n` THENL [
  SIMP_TAC std_ss [ELEM_def,RESTN_INFINITE,HEAD_def]
  THEN Q.PAT_ASSUM `ELEM (INFINITE f') 0 = ELEM (INFINITE f'') 1`
                                               (fn t => ONCE_REWRITE_TAC [SIMP_RULE std_ss [ELEM_def,RESTN_INFINITE,HEAD_def] t])
  THEN Q.PAT_ASSUM `ELEM (INFINITE f'') 0 = s`  (fn t => ONCE_REWRITE_TAC [SIMP_RULE std_ss [ELEM_def,RESTN_INFINITE,HEAD_def] (SYM t)])
  THEN Q.PAT_ASSUM `!n. M.R (ELEM (INFINITE f'') n,ELEM (INFINITE f'') (n + 1))`
   (fn t => ONCE_REWRITE_TAC [SIMP_RULE std_ss [ELEM_def,RESTN_INFINITE,HEAD_def] (SPEC ``0:num`` t)]), (* 0 *)
  SIMP_TAC std_ss [ELEM_def,RESTN_INFINITE,HEAD_def]
  THEN SIMP_TAC arith_ss []
  THEN ONCE_REWRITE_TAC [DECIDE ``SUC n = n + 1``]
  THEN Q.PAT_ASSUM `!n. M.R (ELEM (INFINITE f') n,ELEM (INFINITE f') (n + 1))`
   (fn t=> ONCE_REWRITE_TAC [SIMP_RULE arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def] (SPEC ``n:num`` t)])], (* SUC n, !n. R(p_n,p_(n+1) *)
  Induct_on `j` THENL [
   SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def]
   THEN ASM_REWRITE_TAC [], (* 0 *)
   ONCE_REWRITE_TAC [DECIDE ``SUC j = j + 1``]
   THEN SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def]
   THEN FULL_SIMP_TAC arith_ss []
   THEN Q.PAT_ASSUM `!j'. C_SEM M f (ELEM (INFINITE f') j')`
    (fn t => REWRITE_TAC [SIMP_RULE arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def] (SPEC ``j:num`` t)])]]]);

val Nf2 = Define `(Nf2 (R:'state # 'state -> bool) (s:'state) (0:num) = s) /\ (Nf2 R s (SUC n) = (@r. R(Nf2 R s n,r)))`;

val unc = Define `unc R = \x y. R(x,y)`; (*FIXME: replace this with CURRY_DEF*)
val unc_thm = save_thm("unc_thm",prove(``!P x y. P(x,y) = (unc P) x y``,PROVE_TAC [unc]));

val EU_LEMMA = prove(``!(M :('prop,'state) kripke_structure) (f:'prop ctl) (g:'prop ctl) (s:'state). TOTAL M.R ==>
                        (C_SEM M (C_EU(f,g)) s = C_SEM M (C_NOT(C_AND(C_NOT g,C_NOT(C_AND(f,C_EX (C_EU(f,g))))))) s)``,
REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL [
REWRITE_TAC [C_SEM_def,PATH_def,IN_DEF]
THEN BETA_TAC
THEN SIMP_TAC std_ss []
THEN STRIP_TAC
THEN Induct_on `p` THEN FULL_SIMP_TAC std_ss [IS_INFINITE_def]
THEN SIMP_TAC resq_ss [IN_DEF,xnum_to_def,PLENGTH_def]
THEN SIMP_TAC arith_ss []
THEN REPEAT STRIP_TAC
THEN Cases_on `C_SEM M g s`
THEN RW_TAC std_ss [] THENL [ (* 2 *)
IMP_RES_TAC ( prove(``C_SEM M g (ELEM (INFINITE f') k) /\ ~C_SEM M g (ELEM (INFINITE f') 0) ==> ~(k=0)``,PROVE_TAC []))
THEN PAT_ASSUM ``!(j:num). (P:bool) ==> (Q:bool)`` (fn t => (ASSUME_TAC (SPEC ``0:num`` t)))
THEN FULL_SIMP_TAC arith_ss [],
EXISTS_TAC ``(INFINITE (f':num->'state))``
THEN FULL_SIMP_TAC std_ss [IS_INFINITE_def]
THEN EXISTS_TAC ``REST (INFINITE (f':num -> 'state))``
THEN FULL_SIMP_TAC std_ss [REST_INFINITE,IS_INFINITE_def,ELEM_REST]
THEN FULL_SIMP_TAC arith_ss [PLENGTH_def,xnum_to_def]
THEN EXISTS_TAC ``(k-1):num``
THEN IMP_RES_TAC ( prove(``C_SEM M g (ELEM (INFINITE f') k) /\ ~C_SEM M g (ELEM (INFINITE f') 0) ==> ~(k=0)``,PROVE_TAC []))
THEN FULL_SIMP_TAC arith_ss []], (* ==> *)
REWRITE_TAC [C_SEM_def,PATH_def,IN_DEF]
THEN BETA_TAC
THEN SIMP_TAC std_ss []
THEN STRIP_TAC THENL [ (* 2 *)
EXISTS_TAC ``INFINITE (Nf2  (M :('prop,'state) kripke_structure).R (s :'state))``
THEN SIMP_TAC std_ss [Nf2,IS_INFINITE_def,ELEM_def,RESTN_INFINITE,HEAD_def]
THEN FULL_SIMP_TAC arith_ss [TOTAL_def]
THEN CONJ_TAC THENL [
 ONCE_REWRITE_TAC [DECIDE ``n+1=SUC n``]
 THEN Induct_on `n` THENL [
  SIMP_TAC arith_ss [Nf2,ELEM_def,RESTN_def,REST_def,HEAD_def,listTheory.HD,listTheory.TL,
                     PLENGTH_def,GT_xnum_num_def,listTheory.LENGTH]
  THEN PAT_ASSUM ``!(s:'state). ?(s':'state). M.R (s,s')`` (fn t => ASSUME_TAC (SPEC ``s:'state`` t))
  THEN FULL_SIMP_TAC std_ss [unc_thm]
  THEN REWRITE_TAC [SELECT_THM]
  THEN ASSUM_LIST PROVE_TAC, (* 0 *)
  FULL_SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def,TOTAL_def,Nf2]
  THEN PAT_ASSUM ``!(s:'state). ?(s':'state). M.R (s,s')``
  (fn t => ASSUME_TAC (SPEC ``@(r:'state). (M :('prop,'state) kripke_structure).R (Nf2 M.R s n,r)`` t))
  THEN FULL_SIMP_TAC std_ss [unc_thm]
  THEN REWRITE_TAC [SELECT_THM]
  THEN ASSUM_LIST PROVE_TAC], (* SUC *)
 SIMP_TAC resq_ss [IN_DEF,PLENGTH_def]
 THEN SIMP_TAC arith_ss [xnum_to_def]
 THEN EXISTS_TAC ``0:num``
 THEN FULL_SIMP_TAC arith_ss [Nf2]], (* g *)
 EXISTS_TAC ``INFINITE (\n. if (n=0) then s else ELEM (p':'state path) (n-1))``
 THEN FULL_SIMP_TAC resq_ss []
 THEN SIMP_TAC std_ss [IS_INFINITE_def,IN_DEF,xnum_to_def,PLENGTH_def]
 THEN SIMP_TAC arith_ss []
 THEN REPEAT CONJ_TAC THENL [ (* 3 *)
  SIMP_TAC std_ss [ELEM_def,RESTN_INFINITE,HEAD_def], (* p_0 = s *)
  Induct_on `n` THENL [
   SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def]
   THEN REWRITE_TAC [RESTN_def]
   THEN Induct_on `p'` THEN REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC std_ss [IS_INFINITE_def], (* finite *)
    REWRITE_TAC [HEAD_def]
    THEN PAT_ASSUM ``ELEM (INFINITE (f':num -> 'state)) 0 = ELEM (p:'state path) 1`` (fn t =>
                                REWRITE_TAC [(CONV_RULE (LHS_CONV (SIMP_CONV std_ss [ELEM_def,RESTN_INFINITE,HEAD_def]))) t])
    THEN PAT_ASSUM ``ELEM (p:'state path) 0 = s`` (fn t => REWRITE_TAC [SYM t])
    THEN ONCE_REWRITE_TAC [DECIDE ``(1:num) = 0 + 1``]
    THEN PAT_ASSUM ``!n. (M :('prop,'state) kripke_structure).R (ELEM p n,ELEM p (n + 1))``
    (fn t => REWRITE_TAC [SPEC ``0:num`` t])], (* infinite,0 *)
    ONCE_REWRITE_TAC [ELEM_def]
    THEN ONCE_REWRITE_TAC [RESTN_INFINITE]
    THEN ONCE_REWRITE_TAC [HEAD_def]
    THEN SIMP_TAC arith_ss []
    THEN ONCE_REWRITE_TAC [DECIDE ``SUC n = n + 1``]
    THEN PAT_ASSUM ``!n. (M :('prop,'state) kripke_structure).R (ELEM p' n,ELEM p' (n + 1))``
    (fn t => REWRITE_TAC [SPEC ``n:num`` t])], (* SUC, R(p_n,p_(n+1)) *)
  EXISTS_TAC ``SUC k``
  THEN ONCE_REWRITE_TAC [ELEM_def]
  THEN ONCE_REWRITE_TAC [RESTN_INFINITE]
  THEN ONCE_REWRITE_TAC [HEAD_def]
  THEN SIMP_TAC arith_ss []
  THEN ASM_REWRITE_TAC []
  THEN GEN_TAC
  THEN Cases_on `j=0` THENL [
   FULL_SIMP_TAC std_ss [],
   FULL_SIMP_TAC std_ss []
   THEN Induct_on `j` THENL [
    SIMP_TAC std_ss [], (* 0 *)
    REWRITE_TAC [DECIDE ``!j. ~(SUC j = 0)``]
    THEN REWRITE_TAC [DECIDE ``!j k. SUC j < SUC k = j < k``,DECIDE ``!j. SUC j - 1 = j``]
    THEN ASSUM_LIST PROVE_TAC]]]]]); (* SUC, j!=0, conj_3, strip_2, <== *)

val fol1 = prove(``!x y x' y' z z'. (((x=y)==>z) /\ ((x'=y')==>z')) ==> (((x=y)/\(x'=y'))==>(z/\z'))``,PROVE_TAC []);
val fol2 = prove(``!x y x' y'. (x = y) /\ (x' = y') ==> (x/\x' = y /\ y')``,PROVE_TAC []);
val fol4 = prove(``!x y z. ((x==>y)/\(x==>z))==>(x==>(y/\z))``,PROVE_TAC []);
val fol5 = prove(``!a b c. (a = c) ==> (a /\ b = c /\ b)``,PROVE_TAC []);

val IMF_CTL_LEM8a1 = prove(
  ``!f Q Q'. ~(Q IN FV f) = ~(Q IN (FV (RVNEG Q' f)))``,
  Induct_on `f` THEN
  SIMP_TAC std_ss ([FV_def,UNION_DEF,DELETE_DEF,DIFF_DEF,SET_SPEC,IN_SING,
                    RVNEG_def]@ tsimps ``:'a mu``)
  THENL [ (* 8 *)
    FULL_SIMP_TAC std_ss [],
    PROVE_TAC[],
    PROVE_TAC[],
    REPEAT GEN_TAC THEN CASE_TAC THENL [ (* 2 *)
      EQ_TAC THEN SIMP_TAC std_ss [FV_def,IN_SING],
      EQ_TAC THEN SIMP_TAC std_ss [FV_def,IN_SING]
    ],
    PROVE_TAC[],
    PROVE_TAC[],
    REPEAT GEN_TAC THEN CASE_TAC THENL [ (* 2 *)
     FULL_SIMP_TAC std_ss [FV_def,DELETE_DEF,IN_SING,DIFF_DEF,SET_SPEC],
     FULL_SIMP_TAC std_ss [FV_def,DELETE_DEF,IN_SING,DIFF_DEF,SET_SPEC]
     THEN MATCH_MP_TAC fol5
     THEN ASSUM_LIST PROVE_TAC
     ],
    REPEAT GEN_TAC THEN CASE_TAC THENL [ (* 2 *)
     FULL_SIMP_TAC std_ss [FV_def,DELETE_DEF,IN_SING,DIFF_DEF,SET_SPEC],
     FULL_SIMP_TAC std_ss [FV_def,DELETE_DEF,IN_SING,DIFF_DEF,SET_SPEC]
     THEN MATCH_MP_TAC fol5
     THEN ASSUM_LIST PROVE_TAC
   ]
  ]);

val IMF_CTL_LEM8a = prove(
  ``!f Q. ~(Q IN FV f) ==> IMF f ==> ~SUBFORMULA (~RV Q) (NNF f)``,
  recInduct NNF_IND_def THEN
  SIMP_TAC std_ss ([MU_SUB_def,IMF_def,FV_def,NNF_def,UNION_DEF,SET_SPEC,
                    DELETE_DEF,DIFF_DEF,RVNEG_def,IN_SING] @
                   tsimps ``:'a mu``) THEN
  REPEAT CONJ_TAC THENL [ (* 3 *)
    NTAC 6 STRIP_TAC THENL [(* 2 *)
     FULL_SIMP_TAC std_ss [],
     FULL_SIMP_TAC std_ss []
    ],
    NTAC 6 STRIP_TAC THENL [(* 2 *)
     FULL_SIMP_TAC std_ss [],
     FULL_SIMP_TAC std_ss []
    ],
    NTAC 6 STRIP_TAC THENL [(* 2 *)
     FULL_SIMP_TAC std_ss [IMF_INV_RVNEG]
     THEN ASSUM_LIST (fn t => PROVE_TAC (IMF_CTL_LEM8a1::t)),
     PROVE_TAC [STATES_MONO_LEM3,RVNEG_def]
    ]
  ]);

val FV_BEXP2MU =  save_thm("FV_BEXP2MU",prove(``!b. FV (BEXP2MU b) = {}``,
recInduct (theorem "BEXP2MU_ind")
THEN FULL_SIMP_TAC std_ss [BEXP2MU_def,STATES_def,FV_def]
THEN PROVE_TAC [EMPTY_UNION]));

val FV_CTL2MU = save_thm("FV_CTL2MU",prove(``!(f: 'prop ctl). FV (CTL2MU f) = {}``,
recInduct (theorem "CTL2MU_ind")
THEN FULL_SIMP_TAC std_ss [FV_BEXP2MU,CTL2MU_def,STATES_def,FV_def]
THEN REPEAT STRIP_TAC THENL [
PROVE_TAC [EMPTY_UNION],
SIMP_TAC std_ss [UNION_DEF,DELETE_DEF,DIFF_DEF,SET_SPEC,NOT_IN_EMPTY]
THEN SIMP_TAC std_ss [EMPTY_DEF,SET_GSPEC],
SIMP_TAC std_ss [UNION_DEF,DELETE_DEF,DIFF_DEF,SET_SPEC,NOT_IN_EMPTY]
THEN SIMP_TAC std_ss [EMPTY_DEF,SET_GSPEC]
]
));

val IMF_CTL_LEM =save_thm("IMF_CTL_LEM",prove(``!f Q. IMF (CTL2MU f) ==> ~SUBFORMULA (~RV Q) (NNF (CTL2MU f))``,
GEN_TAC THEN SIMP_TAC std_ss [IMF_CTL_LEM8a,FV_CTL2MU,NOT_IN_EMPTY]));

val IMF_CTL = save_thm("IMF_CTL",prove(``!f. IMF  (CTL2MU f)``,
recInduct (theorem "CTL2MU_ind") THEN REPEAT CONJ_TAC THENL [
 REWRITE_TAC [CTL2MU_def]
 THEN recInduct (theorem "BEXP2MU_ind")
 THEN FULL_SIMP_TAC std_ss ([IMF_def,BEXP2MU_def,NNF_def,MU_SUB_def,RVNEG_def]@(tsimps ``:'a mu``)), (* C_BOOL *)
 SIMP_TAC std_ss [CTL2MU_def,IMF_def], (* C_NOT *)
 SIMP_TAC std_ss [CTL2MU_def,IMF_def], (* C_AND *)
 SIMP_TAC std_ss [CTL2MU_def,IMF_def], (* C_EX *)
 SIMP_TAC std_ss ([CTL2MU_def,IMF_def,NNF_def,MU_SUB_def,RVNEG_def,IMF_CTL_LEM]@(tsimps ``:'a mu``)), (* C_EG *)
 SIMP_TAC std_ss ([CTL2MU_def,IMF_def,NNF_def,MU_SUB_def,RVNEG_def,IMF_CTL_LEM]@(tsimps ``:'a mu``))  (* C_EU *)
]));

val Nf = Define `(Nf (R:'state # 'state -> bool) (s:'state) (q:'state) (0:num) = s) /\ (Nf R s q (SUC n) = if (n=0) then q else (@r. R(Nf R s q n,r)))`;

val STATES_FV_ENV_INV_SPEC = save_thm("STATES_FV_ENV_INV_SPEC",prove(``!(f: 'prop ctl) (M: ('prop,'state) kripke_structure) X.
                                      (STATES (CTL2MU f) (ctl2muks M)  EMPTY_ENV[[["Q"<--X]]]
                                       = STATES (CTL2MU f) (ctl2muks M) EMPTY_ENV)``,
recInduct (theorem "CTL2MU_ind") THEN SIMP_TAC std_ss [FV_CTL2MU,NOT_IN_EMPTY] THEN REPEAT CONJ_TAC THENL [
recInduct (theorem "BEXP2MU_ind")
THEN FULL_SIMP_TAC std_ss [STATES_def,BEXP2MU_def,CTL2MU_def],
FULL_SIMP_TAC std_ss [STATES_def,CTL2MU_def], (* ~ *)
FULL_SIMP_TAC std_ss [STATES_def,CTL2MU_def], (* /\ *)
FULL_SIMP_TAC std_ss [STATES_def,CTL2MU_def], (* EX *)
FULL_SIMP_TAC std_ss [STATES_def,CTL2MU_def]
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [EXTENSION,SET_SPEC]
THEN SIMP_TAC std_ss [ENV_UPDATE],
FULL_SIMP_TAC std_ss [STATES_def,CTL2MU_def]
THEN REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [EXTENSION,SET_SPEC]
THEN SIMP_TAC std_ss [ENV_UPDATE]]));

val Nf3 = Define `(Nf3 (R:'state # 'state -> bool) (x:'state) (q:'state) (0:num) = x)
          /\ (Nf3 R x q (SUC n) = if (n=0) then q else (@r. R(Nf3 R x q n,r)))`;

val CTL2MU_AND_LEM = prove(``!(M: ('prop,'state) kripke_structure) f1 f2 . C_SEM M (C_AND(f1,f2)) = C_SEM M f1 INTER C_SEM M f2``,
REPEAT GEN_TAC
THEN REWRITE_TAC [FUN_EQ_THM]
THEN REWRITE_TAC [INTER_DEF]
THEN SIMP_TAC std_ss [SET_GSPEC]
THEN SIMP_TAC std_ss [IN_DEF]
THEN REWRITE_TAC [C_SEM_def]);

val CTL2MU_OR_LEM = prove(``!(M: ('prop,'state) kripke_structure) f1 f2 . C_SEM M (C_NOT(C_AND(C_NOT f1,C_NOT f2))) = C_SEM M f1 UNION C_SEM M f2``,
REPEAT GEN_TAC
THEN REWRITE_TAC [FUN_EQ_THM]
THEN REWRITE_TAC [UNION_DEF]
THEN SIMP_TAC std_ss [SET_GSPEC]
THEN SIMP_TAC std_ss [IN_DEF]
THEN SIMP_TAC std_ss [C_SEM_def]);

val CTL2MU_EG_LEM = prove(``!(M: ('prop,'state) kripke_structure) (f:'prop ctl). TOTAL M.R /\ wfKS (ctl2muks M) ==>
                          (STATES <<".">> (RV "Q") (ctl2muks M) EMPTY_ENV[[["Q"<--C_SEM M (C_EG f)]]] = C_SEM M (C_EX (C_EG f)))``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [EXTENSION]
THEN GEN_TAC
THEN REWRITE_TAC [STATES_def]
THEN FULL_SIMP_TAC std_ss [SET_SPEC,wfKS_def,IN_UNIV]
THEN REWRITE_TAC [IN_DEF]
THEN SIMP_TAC std_ss [ENV_EVAL]
THEN SIMP_TAC std_ss [C_SEM_def,IN_DEF]
THEN SIMP_TAC std_ss [KS_TRANSITION_def,ctl2muks_def,KS_accfupds,combinTheory.K_DEF] THEN (CONV_TAC (DEPTH_CONV BETA_CONV))
THEN EQ_TAC THENL [
 STRIP_TAC
 THEN EXISTS_TAC ``INFINITE (Nf3 (M: ('prop,'state) kripke_structure).R x q)``
 THEN CONJ_TAC THENL [
  FULL_SIMP_TAC std_ss [PATH_def,TOTAL_def]
  THEN REPEAT CONJ_TAC THENL [ (* 3 *)
   REWRITE_TAC [IS_INFINITE_def],
   SIMP_TAC std_ss [ELEM_def,RESTN_INFINITE,HEAD_def,Nf3],
   ONCE_REWRITE_TAC [DECIDE ``n+1=SUC n``]
   THEN Induct_on `n` THENL [
    SIMP_TAC arith_ss [Nf3,ELEM_def,RESTN_INFINITE,HEAD_def]
    THEN REWRITE_TAC [Nf3,DECIDE ``1=SUC 0``]
    THEN ASM_REWRITE_TAC [], (* 0 *)
    FULL_SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def,TOTAL_def,Nf3]
    THEN PAT_ASSUM ``!(s:'state). ?(s':'state). M.R (s,s')``
    (fn t => ASSUME_TAC (SPEC ``(if n = 0 then q else @(r:'state). (M: ('prop,'state) kripke_structure).R (Nf3 M.R x q n,r))`` t))
    THEN FULL_SIMP_TAC std_ss [unc_thm]
    THEN REWRITE_TAC [SELECT_THM]
    THEN ASSUM_LIST PROVE_TAC]], (* conj_3 *)
  EXISTS_TAC ``p: 'state path``
  THEN (CONV_TAC (LAND_CONV (SIMP_CONV std_ss [ELEM_def,RESTN_INFINITE,HEAD_def])))
  THEN REWRITE_TAC [Nf3,DECIDE ``1=SUC 0``]
  THEN ASM_REWRITE_TAC []], (* ==> *)
  STRIP_TAC
  THEN EXISTS_TAC ``ELEM (p:'state path) 1``
  THEN CONJ_TAC THENL [
   FULL_SIMP_TAC std_ss [PATH_def]
   THEN PAT_ASSUM ``ELEM (p:'state path) 0 = x`` (fn t => ONCE_REWRITE_TAC [SYM t])
   THEN PAT_ASSUM `` !n. (M: ('prop,'state) kripke_structure).R (ELEM p n,ELEM p (n + 1))`` (fn t => ASSUME_TAC (SPEC ``0:num`` t))
   THEN FULL_SIMP_TAC arith_ss [],
   EXISTS_TAC ``p' : 'state path``
   THEN ASM_REWRITE_TAC []]]); (* <== *)

val CTL2MU_EU_LEM = prove(``!(M: ('prop,'state) kripke_structure) (f:'prop ctl) (g:'prop ctl). TOTAL M.R /\ wfKS (ctl2muks M) ==>
                       (STATES <<".">> (RV "Q") (ctl2muks M) EMPTY_ENV[[["Q"<--C_SEM M (C_EU(f,g))]]] = C_SEM M (C_EX (C_EU(f,g))))``,
REPEAT STRIP_TAC
THEN SIMP_TAC std_ss [EXTENSION]
THEN GEN_TAC
THEN REWRITE_TAC [STATES_def]
THEN FULL_SIMP_TAC std_ss [SET_SPEC,wfKS_def,IN_UNIV]
THEN REWRITE_TAC [IN_DEF]
THEN SIMP_TAC std_ss [ENV_EVAL]
THEN SIMP_TAC std_ss [C_SEM_def,IN_DEF]
THEN SIMP_TAC std_ss [KS_TRANSITION_def,ctl2muks_def,KS_accfupds,combinTheory.K_DEF] THEN (CONV_TAC (DEPTH_CONV BETA_CONV))
THEN EQ_TAC THENL [
 STRIP_TAC
 THEN EXISTS_TAC ``INFINITE (Nf3 (M: ('prop,'state) kripke_structure).R x q)``
 THEN CONJ_TAC THENL [
  FULL_SIMP_TAC std_ss [PATH_def,TOTAL_def]
  THEN REPEAT CONJ_TAC THENL [ (* 3 *)
   REWRITE_TAC [IS_INFINITE_def],
   SIMP_TAC std_ss [ELEM_def,RESTN_INFINITE,HEAD_def,Nf3],
   ONCE_REWRITE_TAC [DECIDE ``n+1=SUC n``]
   THEN Induct_on `n` THENL [
    SIMP_TAC arith_ss [Nf3,ELEM_def,RESTN_INFINITE,HEAD_def]
    THEN REWRITE_TAC [Nf3,DECIDE ``1=SUC 0``]
    THEN ASM_REWRITE_TAC [], (* 0 *)
    FULL_SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def,TOTAL_def,Nf3]
    THEN PAT_ASSUM ``!(s:'state). ?(s':'state). M.R (s,s')``
    (fn t => ASSUME_TAC (SPEC ``(if n = 0 then q else @(r:'state). (M: ('prop,'state) kripke_structure).R (Nf3 M.R x q n,r))`` t))
    THEN FULL_SIMP_TAC std_ss [unc_thm]
    THEN REWRITE_TAC [SELECT_THM]
    THEN ASSUM_LIST PROVE_TAC]], (* conj_3 *)
  EXISTS_TAC ``p: 'state path``
  THEN (CONV_TAC (LAND_CONV (SIMP_CONV std_ss [ELEM_def,RESTN_INFINITE,HEAD_def])))
  THEN REWRITE_TAC [Nf3,DECIDE ``1=SUC 0``]
  THEN ASM_REWRITE_TAC []], (* ==> *)
  STRIP_TAC
  THEN EXISTS_TAC ``ELEM (p:'state path) 1``
  THEN CONJ_TAC THENL [
   FULL_SIMP_TAC std_ss [PATH_def]
   THEN PAT_ASSUM ``ELEM (p:'state path) 0 = x`` (fn t => ONCE_REWRITE_TAC [SYM t])
   THEN PAT_ASSUM `` !n. (M: ('prop,'state) kripke_structure).R (ELEM p n,ELEM p (n + 1))`` (fn t => ASSUME_TAC (SPEC ``0:num`` t))
   THEN FULL_SIMP_TAC arith_ss [],
   EXISTS_TAC ``p' : 'state path``
   THEN ASM_REWRITE_TAC []]]); (* <== *)

val GFP_def = Define `
(GFP (M: ('prop,'state) kripke_structure) (f: 'prop ctl) (0:num) = (UNIV:'state -> bool)) /\
(GFP M f (SUC n) = C_SEM M f INTER {s | ?s'. M.R(s,s') /\ s' IN GFP M f n})`;

val CTL_GFP_EQ_CTL2MU_GFP = prove(``!(f: 'prop ctl) (s:'state) (M: ('prop,'state) kripke_structure).
          ((C_SEM M f = MU_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV) /\ wfKS (ctl2muks M) )
          ==> (BIGINTER {P | ?i. P = GFP M f i}
               = BIGINTER {P | ?i. P = FP ((CTL2MU f) /\ <<".">> (RV "Q")) "Q" (ctl2muks M) EMPTY_ENV[[["Q"<--(ctl2muks M).S]]] i})``,
REPEAT STRIP_TAC
THEN MATCH_MP_TAC BIGINTER_LEMMA1
THEN Induct_on `n` THENL [
 FULL_SIMP_TAC std_ss [GFP_def,STATES_def,ENV_EVAL,wfKS_def,ctl2muks_def], (* 0 *)
 REWRITE_TAC [GFP_def]
 THEN ONCE_REWRITE_TAC [STATES_def] THEN ONCE_REWRITE_TAC [STATES_def]
 THEN REWRITE_TAC [ STATES_FV_ENV_INV_SPEC,ENV_UPDATE]
 THEN ONCE_REWRITE_TAC [STATES_def] THEN ONCE_REWRITE_TAC [STATES_def]
 THEN FULL_SIMP_TAC std_ss [KS_TRANSITION_def,ctl2muks_def,wfKS_def]
 THEN FULL_SIMP_TAC std_ss [KS_accfupds,KS_accessors,KS_fn_updates]
 THEN FULL_SIMP_TAC std_ss [ENV_EVAL,IN_UNIV]
 THEN REWRITE_TAC [SET_SPEC]
 THEN SIMP_TAC std_ss [INTER_DEF,SET_SPEC]
 THEN ONCE_REWRITE_TAC [EXTENSION]
 THEN SIMP_TAC std_ss [SET_SPEC]
 THEN SIMP_TAC std_ss [IN_DEF,MU_SAT_def]]);

val CTL_GFP_CLOSURE = prove(``!(f: 'prop ctl) (s:'state) (M: ('prop,'state) kripke_structure).
          ((C_SEM M f = MU_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV) /\ wfKS (ctl2muks M) /\  FINITE (ctl2muks M).S
           /\ (!(f: 'prop ctl). IMF (CTL2MU f)))
         ==> (s IN BIGINTER {P | ?i. P = GFP M f i}
              = (C_SEM M f s /\ ?s'. M.R(s,s') /\ s' IN BIGINTER {P | ?i. P = GFP M f i}))``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC  CTL_GFP_EQ_CTL2MU_GFP
THEN POP_ASSUM (fn t => REWRITE_TAC [t])
THEN POP_ASSUM (fn t => ASSUME_TAC (REWRITE_RULE [CTL2MU_def] (SPEC ``C_EG (f:'prop ctl)`` t)))
THEN IMP_RES_TAC GEN_GFP_IDEM
THEN POP_ASSUM (fn t => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [SYM (SPEC ``EMPTY_ENV:string -> 'state -> bool`` t)])))
THEN ONCE_REWRITE_TAC [STATES_def]
THEN REWRITE_TAC [ STATES_FV_ENV_INV_SPEC,ENV_UPDATE]
THEN SIMP_TAC std_ss [INTER_DEF,SET_SPEC]
THEN ONCE_REWRITE_TAC [STATES_def] THEN ONCE_REWRITE_TAC [STATES_def]
THEN FULL_SIMP_TAC std_ss [KS_TRANSITION_def,ctl2muks_def,wfKS_def]
THEN FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates]
THEN FULL_SIMP_TAC std_ss [ENV_EVAL,IN_UNIV]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN SIMP_TAC std_ss [MU_SAT_def,IN_DEF]);

val Nf4_def = Define `(Nf4 (R:'state # 'state -> bool) (P:'state -> bool) (0:num) = (ARB:'state))
          /\ (Nf4 R P (SUC n) =  @r. R(Nf4 R P n,r) /\ P r)`;


val P1_def = Define `P1 P R s = R(ARB,s) /\ P s`;
val P2_def = Define `P2 P R n s = R(Nf4 R P n,s) /\ P s`;
val P3_def = Define `P3 P R n s = R((@r. P2 P R n r),s) /\ P s`;

val GFP_CLOSURE_IMP_EG_LEM2 = prove(``!(P:'state ->bool) Q (R:'state # 'state -> bool). (!s. P s = Q s /\ ?s'. R(s,s') /\ P s')
==> (?f. !n. P (f n) ==> Q(f n) /\ R(f n,f (SUC n)) /\ P (f (SUC n)))``,
REPEAT STRIP_TAC
THEN EXISTS_TAC ``Nf4 (R:'state # 'state -> bool) (P:'state ->bool)``
THEN Induct_on `n` THENL [
STRIP_TAC
THEN CONJ_TAC THENL [
 ASSUM_LIST PROVE_TAC,
 UNDISCH_TAC ``(P :'state -> bool) (Nf4 (R :'state # 'state -> bool) (P:'state -> bool) (0 :num))``
 THEN SIMP_TAC std_ss [Nf4_def]
 THEN STRIP_TAC
 THEN REWRITE_TAC [GSYM P1_def]
 THEN REWRITE_TAC [SELECT_THM]
 THEN REWRITE_TAC [P1_def]
 THEN ASSUM_LIST PROVE_TAC], (* conj, 0 *)
 REWRITE_TAC [Nf4_def]
 THEN STRIP_TAC
 THEN CONJ_TAC THENL [
  ASSUM_LIST PROVE_TAC,
  REWRITE_TAC [GSYM P2_def]
  THEN REWRITE_TAC [GSYM P3_def]
  THEN REWRITE_TAC [SELECT_THM]
  THEN REWRITE_TAC [P2_def,P3_def]
  THEN ASSUM_LIST PROVE_TAC]]); (* conj, SUC *)

val Nf5_def = Define `(Nf5 (R:'state # 'state -> bool) (P:'state -> bool) (s:'state) (0:num) = s)
          /\ (Nf5 R P s (SUC n) =  @r. R(Nf5 R P s n,r) /\ P r)`;

val P4_def = Define `P4 R P s s' = R(s,s') /\ P s'`;
val P5_def = Define `P5 R P s n s' = R(Nf5 R P s n,s') /\ P s'`;
val P6_def = Define `P6 R P s n s' = R((@r. P5 R P s n r),s') /\ P s'`;

val GFP_CLOSURE_IMP_EG_LEM1a = prove(``!(P:'state ->bool) Q (R:'state # 'state -> bool) s. (!s. P s = Q s /\ ?s'. R(s,s') /\ P s') /\ P s
==> (!n. P (Nf5 R P s n) ==> Q(Nf5 R P s n) /\ R(Nf5 R P s n,Nf5 R P s (SUC n)) /\ P (Nf5 R P s (SUC n)))``,
REPEAT GEN_TAC THEN STRIP_TAC
THEN Induct_on `n` THENL [
STRIP_TAC
THEN CONJ_TAC THENL [
 ASSUM_LIST PROVE_TAC,
 UNDISCH_TAC ``(P :'state -> bool) (Nf5 (R :'state # 'state -> bool) (P:'state -> bool) (s:'state) (0 :num))``
 THEN SIMP_TAC std_ss [Nf5_def]
 THEN STRIP_TAC
 THEN REWRITE_TAC [GSYM P4_def]
 THEN REWRITE_TAC [SELECT_THM]
 THEN REWRITE_TAC [P4_def]
 THEN ASSUM_LIST PROVE_TAC], (* conj, 0 *)
 REWRITE_TAC [Nf5_def]
 THEN STRIP_TAC
 THEN CONJ_TAC THENL [
  ASSUM_LIST PROVE_TAC,
  REWRITE_TAC [GSYM P5_def]
  THEN REWRITE_TAC [GSYM P6_def]
  THEN REWRITE_TAC [SELECT_THM]
  THEN REWRITE_TAC [P5_def,P6_def]
  THEN ASSUM_LIST PROVE_TAC]]); (* conj, SUC *)

val GFP_CLOSURE_IMP_EG_LEM1 = prove(``!(P:'state ->bool) Q (R:'state # 'state -> bool) s. (!s. P s = Q s /\ ?s'.R(s,s') /\ P s') /\ P s
    ==> ?(f:num->'state). (f(0) = s) /\ !n. R(f n,f (SUC n)) /\ P(f n)``,
REPEAT STRIP_TAC
THEN EXISTS_TAC ``Nf5 (R:'state # 'state -> bool) (P:'state ->bool) s``
THEN CONJ_TAC THENL [
 REWRITE_TAC [Nf5_def],
 Induct_on `n` THENL [
  REWRITE_TAC [Nf5_def]
  THEN CONJ_TAC THENL [
  MATCH_MP_TAC (DECIDE ``((R:'state # 'state -> bool) (s,@r. R (s,r) /\ (P:'state ->bool) r) /\ P(@r. R (s,r) /\ P r))
                       ==> (R (s,@r. R (s,r) /\ P r))``)
  THEN REWRITE_TAC [GSYM P4_def]
  THEN REWRITE_TAC [SELECT_THM]
  THEN REWRITE_TAC [P4_def]
  THEN ASSUM_LIST PROVE_TAC,
  POP_ASSUM (fn t => REWRITE_TAC [t])], (* conj, 0 *)
  CONJ_TAC THENL [
  REWRITE_TAC [Nf5_def]
  THEN REWRITE_TAC [GSYM P5_def]
  THEN MATCH_MP_TAC (DECIDE ``((R:'state # 'state -> bool) ((@r. P5 R (P:'state ->bool) s n r),@r. R ((@r. P5 R P s n r),r) /\ P r)
                               /\ P (@r. R ((@r. P5 R P s n r),r) /\ P r))
                     ==> (R((@r. P5 R P s n r),@r. R ((@r. P5 R P s n r),r) /\ P r))``)
  THEN REWRITE_TAC [GSYM P6_def]
  THEN REWRITE_TAC [SELECT_THM]
  THEN REWRITE_TAC [P5_def,P6_def]
  THEN REWRITE_TAC [GSYM (List.last(CONJUNCTS Nf5_def))]
  THEN POP_ASSUM (fn t => `P (Nf5 (R:'state # 'state -> bool) (P:'state ->bool) s (SUC n))`
                           by PROVE_TAC [List.last(CONJUNCTS t),GFP_CLOSURE_IMP_EG_LEM1a])
  THEN ASSUM_LIST PROVE_TAC,
  IMP_RES_TAC GFP_CLOSURE_IMP_EG_LEM1a
  THEN ASSUM_LIST PROVE_TAC] (* conj *)] (* SUC *)] (* conj *));

val GFP_CLOSURE_IMP_EG_LEM3 = prove(``!(P:'state ->bool) Q (R:'state # 'state -> bool) s. (!s. P s = Q s /\ ?s'.R(s,s') /\ P s') /\ P s
  ==> ?(f:num->'state).  (f(0) = s) /\ !n. R(f n,f (SUC n)) /\ Q(f n)``,
REPEAT STRIP_TAC
THEN IMP_RES_TAC GFP_CLOSURE_IMP_EG_LEM1
THEN ASSUM_LIST (fn t => PROVE_TAC ( GFP_CLOSURE_IMP_EG_LEM2::t)));

val GFP_CLOSURE_IMP_EG_LEM = prove (``!(f: 'prop ctl) (s:'state) (M: ('prop,'state) kripke_structure).
((C_SEM M f = MU_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV) /\ wfKS (ctl2muks M) /\  FINITE (ctl2muks M).S
           /\ (!(f: 'prop ctl). IMF (CTL2MU f))) /\
(s IN BIGINTER {P | ?i. P = GFP M f i}) ==> ?p. PATH M p s /\ !n::0 to PLENGTH p. C_SEM M f (ELEM p n)``,
REPEAT STRIP_TAC
THEN `!(s :'state). s IN BIGINTER {(P :'state -> bool) | ?(i :num). P = GFP M f i}
              = C_SEM M f s /\ ?(s' :'state). M.R (s,s') /\ s' IN BIGINTER {P | ?(i :num). P = GFP M f i}`
     by (POP_ASSUM (fn t => ALL_TAC) THEN IMP_RES_TAC CTL_GFP_CLOSURE)
THEN POP_ASSUM (fn t => ASSUME_TAC (SIMP_RULE std_ss [IN_DEF] t))
THEN `!(s :'state). BIGINTER {P | ?i. P = GFP M f i} s ==>
            ?f'. (f' 0 = s) /\ !n. M.R (f' n,f' (SUC n)) /\ C_SEM M f (f' n)` by IMP_RES_TAC GFP_CLOSURE_IMP_EG_LEM3
THEN PAT_ASSUM ``(s :'state) IN BIGINTER {P | ?i. P = GFP M f i}`` (fn t => POP_ASSUM (fn t' =>
                                                                             ASSUME_TAC (MATCH_MP t' (SIMP_RULE std_ss [IN_DEF] t))))
THEN POP_ASSUM (fn t => POP_ASSUM_LIST (fn t => ALL_TAC) THEN ASSUME_TAC t)
THEN FULL_SIMP_TAC std_ss []
THEN EXISTS_TAC ``INFINITE (f':num->'state)``
THEN POP_ASSUM (fn t => ASSUME_TAC ((CONV_RULE unwindLib.FORALL_CONJ_CONV) t))
THEN FULL_SIMP_TAC resq_ss [PATH_def,PLENGTH_def,xnum_to_def,IN_DEF]
THEN FULL_SIMP_TAC  arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def,IS_INFINITE_def,DECIDE ``SUC n = n + 1``]);

val CTL_GFP_SUBSET_EG = prove(``!(f: 'prop ctl) (M: ('prop,'state) kripke_structure).
((C_SEM M f = MU_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV) /\ wfKS (ctl2muks M) /\  FINITE (ctl2muks M).S
           /\ (!(f: 'prop ctl). IMF (CTL2MU f)))
==> BIGINTER {P | ?i. P = GFP M f i} SUBSET C_SEM M (C_EG f)``,
REPEAT STRIP_TAC THEN REWRITE_TAC [SUBSET_DEF]
THEN GEN_TAC THEN SPEC_TAC (``x:'state``,``s:'state``) THEN GEN_TAC
THEN SIMP_TAC std_ss [IN_DEF,C_SEM_def]
THEN IMP_RES_TAC GFP_CLOSURE_IMP_EG_LEM
THEN FULL_SIMP_TAC std_ss [IN_DEF]);

val CTL_LFP = Define `
(LFP (M: ('prop,'state) kripke_structure) (f: 'prop ctl) (g:'prop ctl) (0:num) = ({}:'state -> bool)) /\
(LFP M f g (SUC n) = C_SEM M g UNION (C_SEM M f INTER {s | ?s'. M.R(s,s') /\ s' IN LFP M f g n}))`;

val CTL_LFP_EQ_CTL2MU_LFP = prove(``!(f: 'prop ctl) (g: 'prop ctl) (s:'state) (M: ('prop,'state) kripke_structure).
          ((C_SEM M f = MU_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV)
           /\ (C_SEM M g = MU_SAT (CTL2MU g) (ctl2muks M) EMPTY_ENV) /\ (wfKS (ctl2muks M)))
          ==> (BIGUNION {P | ?i. P = LFP M f g i}
               = BIGUNION {P | ?i. P = FP ((CTL2MU g) \/ ((CTL2MU f) /\ <<".">> (RV "Q"))) "Q" (ctl2muks M) EMPTY_ENV[[["Q"<--{}]]] i})``,
REPEAT STRIP_TAC
THEN MATCH_MP_TAC BIGUNION_LEMMA1
THEN Induct_on `n` THENL [
 FULL_SIMP_TAC std_ss [CTL_LFP,STATES_def,ENV_EVAL,ctl2muks_def], (* 0 *)
 REWRITE_TAC [CTL_LFP]
 THEN ONCE_REWRITE_TAC [STATES_def] THEN ONCE_REWRITE_TAC [STATES_def] THEN ONCE_REWRITE_TAC [STATES_def]
 THEN REWRITE_TAC [ STATES_FV_ENV_INV_SPEC,ENV_UPDATE]
 THEN ONCE_REWRITE_TAC [STATES_def] THEN ONCE_REWRITE_TAC [STATES_def]
 THEN FULL_SIMP_TAC std_ss [KS_TRANSITION_def,wfKS_def]
 THEN FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates]
 THEN FULL_SIMP_TAC std_ss [ENV_EVAL,IN_UNIV]
 THEN REWRITE_TAC [SET_SPEC]
 THEN SIMP_TAC std_ss [UNION_DEF,INTER_DEF,SET_SPEC]
 THEN ONCE_REWRITE_TAC [EXTENSION]
 THEN SIMP_TAC std_ss [SET_SPEC]
 THEN SIMP_TAC std_ss [IN_DEF,MU_SAT_def]]);

val FIN_PFX_def  = Define `
(FIN_PFX l 0 = []) /\
(FIN_PFX l (SUC n) = (HD l)::(FIN_PFX (TL l) n))`;

val INF_PFX_def = Define `
(INF_PFX f 0 = []) /\
(INF_PFX f (SUC n) = SNOC (f n) (INF_PFX f n))`;

val PREFIX_def = Define `
(PREFIX (FINITE l) n = FIN_PFX l n) /\
(PREFIX (INFINITE f) n = INF_PFX f n)`;

val INF_PREFIX_LENGTH = save_thm("INF_PREFIX_LENGTH",prove(``!f k. LENGTH (PREFIX (INFINITE f) k) = k``,
REWRITE_TAC [PREFIX_def]
THEN Induct_on `k` THENL [
REWRITE_TAC [INF_PFX_def,LENGTH,SNOC],
REWRITE_TAC [INF_PFX_def]
THEN FULL_SIMP_TAC arith_ss [LENGTH,SNOC,LENGTH_SNOC]]));

val IDX_BIGUNION = save_thm("IDX_BIGUNION",prove(``!P s. s IN BIGUNION {p | ?i. p = P i} = ?i. s IN P i``,
SIMP_TAC std_ss [BIGUNION,SET_SPEC] THEN PROVE_TAC []));

val CTL_LFP_LEM = prove(``!(f: 'prop ctl) (g: 'prop ctl) (s:'state) (M: ('prop,'state) kripke_structure).
C_SEM M (C_EU(f,g)) s ==> s IN BIGUNION {P | ?(i:num). P = LFP M f g i}``,
CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (REWRITE_CONV [C_SEM_def,IN_DEF]))) THEN BETA_TAC THEN REPEAT STRIP_TAC
THEN Induct_on `p` THENL [
 SIMP_TAC std_ss [PATH_def,IS_INFINITE_def],
 GEN_TAC
 THEN CONV_TAC (RAND_CONV (RATOR_CONV (SIMP_CONV resq_ss [IN_DEF,PLENGTH_def,xnum_to_def])))
 THEN SIMP_TAC arith_ss []
 THEN SPEC_TAC (``INFINITE (f':num->'state)``,``p:'state path``)
 THEN REPEAT STRIP_TAC
 THEN UNDISCH_TAC ``!(j :num). j < (k :num) ==> C_SEM (M :('prop,'state) kripke_structure) (f :'prop ctl) (ELEM (p :'state path) j)``
 THEN UNDISCH_TAC `` C_SEM (M :('prop,'state) kripke_structure) (g :'prop ctl)  (ELEM (p :'state path) (k :num))``
 THEN UNDISCH_TAC ``PATH (M :('prop,'state) kripke_structure) (p :'state path) (s :'state)``
 THEN SPEC_TAC (``s:'state``,``s:'state``)
 THEN Induct_on `LENGTH (PREFIX (p:'state path) (k:num))` THENL [
  REPEAT STRIP_TAC
  THEN REWRITE_TAC [IDX_BIGUNION]
  THEN EXISTS_TAC ``SUC 0``
  THEN FULL_SIMP_TAC std_ss [PATH_def,UNION_DEF,CTL_LFP,SET_SPEC]
  THEN DISJ1_TAC
  THEN Induct_on `p` THENL [
    FULL_SIMP_TAC std_ss [PATH_def,IS_INFINITE_def],
    FULL_SIMP_TAC std_ss [INF_PREFIX_LENGTH]]
  THEN ASSUM_LIST (fn t => PROVE_TAC (IN_DEF::t)), (* basis case *)
  REPEAT STRIP_TAC
  THEN PAT_ASSUM ``!p k. t`` (fn t => ASSUME_TAC ( SPECL [``REST (p: 'state path)``,``(k:num)-1``] t ))
  THEN Cases_on `k=0` THENL [
   REPEAT STRIP_TAC
   THEN REWRITE_TAC [IDX_BIGUNION]
   THEN EXISTS_TAC ``SUC 0``
   THEN FULL_SIMP_TAC std_ss [PATH_def,UNION_DEF,CTL_LFP,SET_SPEC]
   THEN DISJ1_TAC
   THEN Induct_on `p` THENL [
     FULL_SIMP_TAC std_ss [PATH_def,IS_INFINITE_def],
     FULL_SIMP_TAC std_ss [INF_PREFIX_LENGTH]]
   THEN ASSUM_LIST (fn t => PROVE_TAC (IN_DEF::t)), (* k = 0 *)
   Induct_on `p` THENL [
    SIMP_TAC std_ss [PATH_def,IS_INFINITE_def],
    SIMP_TAC std_ss [INF_PREFIX_LENGTH,REST_INFINITE]
    THEN REWRITE_TAC [GSYM REST_INFINITE]
    THEN GEN_TAC
    THEN SPEC_TAC (``INFINITE (f':num->'state)``,``p:'state path``)
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC (SIMP_RULE std_ss [] (ARITH_CONV ``~(k=0) /\ (SUC v = k) ==> (v = k - 1)``))
    THEN RES_TAC
    THEN PAT_ASSUM ``((v:num)=k-1)==>t`` (fn t => ALL_TAC)
    THEN PAT_ASSUM ``(v:num)= k - 1`` (fn t => PAT_ASSUM ``SUC v = k`` (fn t => ALL_TAC))
    THEN POP_ASSUM (fn t => ASSUME_TAC (SPEC ``ELEM (p:'state path) 1`` t))
    THEN FULL_SIMP_TAC std_ss [ELEM_REST]
    THEN IMP_RES_TAC PATH_REST
    THEN RES_TAC
    THEN PAT_ASSUM ``PATH x y z ==> t`` (fn t => ALL_TAC)
    THEN PAT_ASSUM ``PATH M (REST (p:'state path)) (ELEM p 1)`` (fn t => ALL_TAC)
    THEN FULL_SIMP_TAC std_ss [DECIDE ``~((k:num)=0) = (k-1+1=k)``]
    THEN PAT_ASSUM ``(k:num) - 1 + 1 = k`` (fn t => FULL_SIMP_TAC std_ss [t] THEN ASSUME_TAC t)
    THEN FULL_SIMP_TAC std_ss [SYM (DECIDE ``~((k:num)=0) = (k-1+1=k)``)]
    THEN RES_TAC
    THEN PAT_ASSUM ``C_SEM x y z ==> t`` (fn t => ALL_TAC)
    THEN SUBGOAL_THEN ``(!j. j < (k:num) - 1
                ==> C_SEM (M: ('prop,'state) kripke_structure)  f (ELEM (p:'state path) (j + 1)))`` ASSUME_TAC THENL [
     GEN_TAC
     THEN IMP_RES_TAC (DECIDE ``~((k:num)=0) ==> (j<k-1 = j+1<k)``)
     THEN POP_ASSUM (fn _ => POP_ASSUM (fn _ => POP_ASSUM (fn t => REWRITE_TAC [t])))
     THEN ASM_REWRITE_TAC [], (* subgoal *)
     RES_TAC
     THEN PAT_ASSUM ``x ==> y`` (fn t => ALL_TAC)
     THEN PAT_ASSUM ``!(j:num). j < (k:num) - 1 ==> C_SEM M f (ELEM (p:'state path) (j + 1))`` (fn t => ALL_TAC)
     THEN FULL_SIMP_TAC std_ss [PATH_def]
     THEN PAT_ASSUM ``!(j:num). j < (k:num)==> C_SEM M f (ELEM (p:'state path) j)``
                                           (fn t => ASSUME_TAC (SPEC ``0:num`` t) THEN ASSUME_TAC t)
     THEN PAT_ASSUM ``ELEM (p:'state path) 0 = s`` (fn t => PAT_ASSUM `` 0 < (k:num)  ==> C_SEM M f (ELEM p 0)`` (fn t' =>
                                        ASSUME_TAC (REWRITE_RULE [t] t') THEN ASSUME_TAC t))
     THEN FULL_SIMP_TAC std_ss [DECIDE ``~((k:num)=0) = 0 < k``]
     THEN RES_TAC
     THEN FULL_SIMP_TAC std_ss [SYM (DECIDE ``~((k:num)=0) = 0 < k``)]
     THEN PAT_ASSUM ``T`` (fn _ => POP_ASSUM (fn _ => ALL_TAC))
     THEN FULL_SIMP_TAC std_ss [IDX_BIGUNION]
     THEN EXISTS_TAC ``SUC i``
     THEN FULL_SIMP_TAC std_ss [PATH_def,UNION_DEF,CTL_LFP,SET_SPEC,INTER_DEF]
     THEN DISJ2_TAC
     THEN CONJ_TAC THENL [
      FULL_SIMP_TAC std_ss [IN_DEF],
      EXISTS_TAC ``ELEM (p:'state path) 1``
      THEN PAT_ASSUM ``ELEM (p:'state path) 0 = s`` (fn t => REWRITE_TAC [SYM t])
      THEN ASM_REWRITE_TAC []
      THEN ONCE_REWRITE_TAC [DECIDE ``(1:num) = 0+1``]
      THEN ASSUM_LIST PROVE_TAC]]]]]]);

val CTL2MU_LEM = prove(``!(f: 'prop ctl) (M: ('prop,'state) kripke_structure).
                      ((!(f: 'prop ctl). IMF (CTL2MU f)) /\ TOTAL M.R /\ wfKS (ctl2muks M) /\ FINITE (ctl2muks M).S) ==>
                      (C_SEM M f = MU_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV)``,
REWRITE_TAC [FUN_EQ_THM]
THEN CONV_TAC (STRIP_QUANT_CONV (RIGHT_IMP_FORALL_CONV))
THEN CONV_TAC (QUANT_CONV SWAP_VARS_CONV)
THEN CONV_TAC SWAP_VARS_CONV
THEN ONCE_REWRITE_TAC [GEN_ALPHA_CONV ``s:'state`` `` !(x :'state) (f :'prop ctl) (M :('prop,'state) kripke_structure).
      (!(f :'prop ctl). IMF (CTL2MU f)) /\  (TOTAL :('state # 'state -> bool) -> bool) M.R /\ wfKS (ctl2muks M) /\ FINITE (ctl2muks M).S
      ==> (C_SEM M f x = MU_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV x)``]
THEN CONV_TAC SWAP_VARS_CONV
THEN recInduct (theorem "CTL2MU_ind") THEN REPEAT CONJ_TAC THENL [
SIMP_TAC std_ss [MU_SAT_def,STATES_def,CTL2MU_def,BEXP2MU_def,C_SEM_def,B_SEM_def]
THEN recInduct (theorem "BEXP2MU_ind") THEN REPEAT CONJ_TAC THENL [
FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates,B_SEM_def,BEXP2MU_def,STATES_def,wfKS_def,IN_UNIV,SET_SPEC],
FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates]
THEN FULL_SIMP_TAC std_ss [B_SEM_def,BEXP2MU_def,STATES_def,ctl2muks_def,wfKS_def]
THEN FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates]
THEN FULL_SIMP_TAC std_ss [SET_SPEC]
THEN PROVE_TAC [IN_UNIV],
FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates,B_SEM_def,BEXP2MU_def,STATES_def,wfKS_def,IN_UNIV,DIFF_DEF,SET_SPEC],
FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates,B_SEM_def,BEXP2MU_def,STATES_def,wfKS_def,IN_UNIV,INTER_DEF,SET_SPEC]], (* C_BOOL *)
FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates,B_SEM_def,BEXP2MU_def,STATES_def,wfKS_def,IN_UNIV,DIFF_DEF,
                      SET_SPEC,MU_SAT_def,STATES_def,CTL2MU_def,C_SEM_def,B_SEM_def], (* C_NOT *)
FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates,B_SEM_def,BEXP2MU_def,STATES_def,wfKS_def,IN_UNIV,INTER_DEF,
                      SET_SPEC,MU_SAT_def,STATES_def,CTL2MU_def,C_SEM_def,B_SEM_def], (* C_AND *)
FULL_SIMP_TAC std_ss [MU_SAT_def,STATES_def,CTL2MU_def,BEXP2MU_def,C_SEM_def,B_SEM_def]
THEN CONV_TAC (STRIP_QUANT_CONV (RAND_CONV (STRIP_QUANT_CONV (RAND_CONV (LHS_CONV(STRIP_QUANT_CONV (RAND_CONV(RATOR_CONV (REWRITE_CONV [IN_DEF])))))))))
THEN BETA_TAC
THEN REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [wfKS_def,KS_TRANSITION_def]
THEN FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates]
THEN FULL_SIMP_TAC std_ss [SET_SPEC,IN_UNIV]
THEN FULL_SIMP_TAC std_ss [PATH_def]
THEN EQ_TAC THENL [
 CONV_TAC LEFT_IMP_EXISTS_CONV
 THEN GEN_TAC THEN
 CONV_TAC RIGHT_IMP_EXISTS_CONV
 THEN EXISTS_TAC ``ELEM (p:'state path) ((0:num)+1)``
 THEN REPEAT STRIP_TAC THENL [
  PAT_ASSUM ``ELEM (p:'state path) 0 = s`` (fn t => ONCE_REWRITE_TAC [SYM t])
  THEN PAT_ASSUM ``!n. (M: ('prop,'state) kripke_structure).R (ELEM (p:'state path) n,ELEM p (n + 1))``
  (fn t => ASSUME_TAC (SPEC ``0:num`` t))
  THEN FULL_SIMP_TAC arith_ss [],
  FULL_SIMP_TAC std_ss []], (* ==> *)
 CONV_TAC LEFT_IMP_EXISTS_CONV
 THEN GEN_TAC THEN
 CONV_TAC RIGHT_IMP_EXISTS_CONV
 THEN EXISTS_TAC ``INFINITE (Nf (M: ('prop,'state) kripke_structure).R s q)``
 THEN REPEAT STRIP_TAC THENL [
 REWRITE_TAC [IS_INFINITE_def], (* INFINITE p *)
 SIMP_TAC std_ss [ELEM_def,RESTN_def,REST_def,HEAD_def,listTheory.HD,Nf], (* ELEM p 0 = s *)
 ONCE_REWRITE_TAC [DECIDE ``n+1=SUC n``]
 THEN Induct_on `n` THENL [
  SIMP_TAC arith_ss [Nf,ELEM_def,RESTN_def,REST_def,HEAD_def,listTheory.HD,listTheory.TL,
                     PLENGTH_def,GT_xnum_num_def,listTheory.LENGTH]
  THEN REWRITE_TAC [Nf,DECIDE ``1=SUC 0``]
  THEN ASM_REWRITE_TAC [], (* 0 *)
  FULL_SIMP_TAC arith_ss [ELEM_def,RESTN_INFINITE,HEAD_def,TOTAL_def,Nf]
  THEN PAT_ASSUM ``!s. ?s'. (M: ('prop,'state) kripke_structure).R (s,s')``
  (fn t => ASSUME_TAC (SPEC ``(if n = 0 then q else @r. (M: ('prop,'state) kripke_structure).R (Nf M.R s q n,r))`` t))
  THEN FULL_SIMP_TAC std_ss [unc_thm]
  THEN REWRITE_TAC [SELECT_THM]
  THEN ASSUM_LIST PROVE_TAC], (* SUC n *)
 REWRITE_TAC [ELEM_def] THEN ONCE_REWRITE_TAC [DECIDE ``1 = SUC 0``]
 THEN REWRITE_TAC [Nf,ELEM_def,RESTN_def,REST_def,HEAD_def,listTheory.HD,listTheory.TL,DECIDE ``1 = SUC 0``]
 THEN SIMP_TAC arith_ss [] THEN REWRITE_TAC [DECIDE ``1=SUC 0``] THEN REWRITE_TAC [Nf]
 THEN ASM_REWRITE_TAC []]], (* <== *) (* C_EX *)
REPEAT STRIP_TAC
THEN EQ_TAC THENL [
 FULL_SIMP_TAC std_ss [MU_SAT_def,STATES_def,CTL2MU_def,BEXP2MU_def,SET_SPEC,IN_UNIV]
 THEN CONV_TAC RIGHT_IMP_FORALL_CONV
 THEN SPEC_TAC (``s:'state``,``s:'state``)
 THEN CONV_TAC (SWAP_VARS_CONV)
 THEN CONV_TAC (STRIP_QUANT_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM (prove(``!x P. x IN P = P x``,PROVE_TAC [IN_DEF]))])))
 THEN REWRITE_TAC [GSYM SUBSET_DEF]
 THEN Induct_on `n` THENL [
  FULL_SIMP_TAC std_ss [ctl2muks_def,KS_accfupds,KS_accessors,KS_fn_updates,STATES_def,ENV_EVAL,SUBSET_UNIV,wfKS_def,ctl2muks_def,SET_SPEC,IN_UNIV], (* 0 *)
  PAT_ASSUM ``!(f:'prop ctl). IMF (CTL2MU f)`` (fn t => ASSUME_TAC (REWRITE_RULE [CTL2MU_def] (SPEC ``C_EG (f:'prop ctl)`` t)))
  THEN IMP_RES_TAC (REWRITE_RULE [IMF_MU_IFF_IMF_NU] STATES_MONO_EQ)
  THEN POP_ASSUM (fn t => ASSUME_TAC (ISPEC ``EMPTY_ENV:string -> 'state -> bool`` t))
  THEN ONCE_REWRITE_TAC [STATES_def]
  THEN REWRITE_TAC [ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC ((CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [STATES_def]))) t))
  THEN IMP_RES_TAC CTL2MU_EG_LEM
  THEN POP_ASSUM (fn t=> FULL_SIMP_TAC std_ss [SPEC ``f: 'prop ctl`` t])
  THEN FULL_SIMP_TAC std_ss [STATES_FV_ENV_INV_SPEC]
  THEN RES_TAC
  THEN POP_ASSUM (fn t => ALL_TAC)
  THEN POP_ASSUM (fn t => ALL_TAC)
  THEN POP_ASSUM (fn t => ASSUME_TAC (REWRITE_RULE [GSYM FUN_EQ_THM] (SIMP_RULE std_ss [IN_DEF] t)))
  THEN POP_ASSUM (fn t => FULL_SIMP_TAC std_ss [SYM t])
  THEN FULL_SIMP_TAC std_ss [GSYM CTL2MU_AND_LEM,
                             REWRITE_RULE [GSYM FUN_EQ_THM]
                                          (GENL [``(M: ('prop,'state) kripke_structure)``,``f:'prop ctl``] EG_LEMMA)]], (* SUC,==>*)
  RES_TAC
  THEN POP_ASSUM (fn t => ALL_TAC)
  THEN POP_ASSUM (fn t => ALL_TAC)
  THEN POP_ASSUM (fn t => ASSUME_TAC (REWRITE_RULE [GSYM FUN_EQ_THM] (SIMP_RULE std_ss [IN_DEF] t)))
  THEN REWRITE_TAC [MU_SAT_def]
  THEN REWRITE_TAC [CTL2MU_def]
  THEN IMP_RES_TAC NU_BIGINTER
  THEN POP_ASSUM (fn t => REWRITE_TAC [t])
  THEN IMP_RES_TAC CTL_GFP_EQ_CTL2MU_GFP
  THEN POP_ASSUM (fn t => REWRITE_TAC [SYM t])
  THEN IMP_RES_TAC CTL_GFP_SUBSET_EG
  THEN POP_ASSUM (fn t => ASSUME_TAC (SIMP_RULE std_ss [SUBSET_DEF,IN_DEF] t))
  THEN FULL_SIMP_TAC std_ss [IN_DEF]], (* <==,EG *)
REPEAT STRIP_TAC
THEN EQ_TAC THENL [
 FULL_SIMP_TAC std_ss [MU_SAT_def,MU_BIGUNION,CTL2MU_def,BEXP2MU_def,SET_SPEC,IN_UNIV]
 THEN RES_TAC
 THEN PAT_ASSUM ``!s. t ==> t'`` (fn t => ALL_TAC)
 THEN PAT_ASSUM ``!s. t ==> t'`` (fn t => ALL_TAC)
 THEN PAT_ASSUM ``!s. t ==> t'`` (fn t => ALL_TAC)
 THEN PAT_ASSUM ``!s. t ==> t'`` (fn t => ALL_TAC)
 THEN PAT_ASSUM ``!s. C_SEM M g s = s IN STATES (CTL2MU g) (ctl2muks M) EMPTY_ENV``
                   (fn t=> ASSUME_TAC (SIMP_RULE std_ss [GSYM MU_SAT_def] t))
 THEN POP_ASSUM (fn t=> ASSUME_TAC (REWRITE_RULE [GSYM FUN_EQ_THM] t))
 THEN PAT_ASSUM ``!s. C_SEM M f s = s IN STATES (CTL2MU f) (ctl2muks M) EMPTY_ENV``
                   (fn t=> ASSUME_TAC (SIMP_RULE std_ss [GSYM MU_SAT_def] t))
 THEN POP_ASSUM (fn t=> ASSUME_TAC (REWRITE_RULE [GSYM FUN_EQ_THM] t))
 THEN `BIGUNION {P | ?i. P = LFP M f g i}
                   = BIGUNION {P  | ?i. P = FP (CTL2MU g \/ CTL2MU f /\ <<".">> (RV "Q")) "Q" (ctl2muks M) EMPTY_ENV[[["Q"<--{}]]] i}`
       by IMP_RES_TAC CTL_LFP_EQ_CTL2MU_LFP
 THEN POP_ASSUM (fn t => REWRITE_TAC [SYM t])
 THEN REWRITE_TAC [CTL_LFP_LEM], (* ==> *)
 FULL_SIMP_TAC std_ss [MU_SAT_def,STATES_def,CTL2MU_def,BEXP2MU_def,SET_SPEC,IN_UNIV]
 THEN CONV_TAC LEFT_IMP_EXISTS_CONV
 THEN SPEC_TAC (``s:'state``,``s:'state``)
 THEN CONV_TAC (SWAP_VARS_CONV)
 THEN CONV_TAC (STRIP_QUANT_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM (prove(``!x P. x IN P = P x``,PROVE_TAC [IN_DEF]))])))
 THEN REWRITE_TAC [GSYM SUBSET_DEF]
 THEN Induct_on `n` THENL [
  REWRITE_TAC [STATES_def,ENV_EVAL,EMPTY_SUBSET], (* 0 *)
  PAT_ASSUM ``!(f:'prop ctl). IMF (CTL2MU f)`` (fn t => ASSUME_TAC (REWRITE_RULE [CTL2MU_def] (SPEC ``C_EU(f:'prop ctl,g:'prop ctl)`` t)))
  THEN IMP_RES_TAC STATES_MONO_EQ
  THEN POP_ASSUM (fn t => ASSUME_TAC (SPEC ``EMPTY_ENV:string -> 'state -> bool`` t))
  THEN ONCE_REWRITE_TAC [STATES_def]
  THEN REWRITE_TAC [ENV_UPDATE]
  THEN POP_ASSUM (fn t => ASSUME_TAC ((CONV_RULE(RAND_CONV ((ONCE_REWRITE_CONV [STATES_def]) THENC (ONCE_REWRITE_CONV [STATES_def])))) t))
  THEN IMP_RES_TAC CTL2MU_EU_LEM
  THEN POP_ASSUM (fn t=> FULL_SIMP_TAC std_ss [SPECL [``f: 'prop ctl``,``g: 'prop ctl``] t])
  THEN FULL_SIMP_TAC std_ss [STATES_FV_ENV_INV_SPEC]
  THEN RES_TAC
  THEN POP_ASSUM (fn t => ALL_TAC)
  THEN POP_ASSUM (fn t => ALL_TAC)
  THEN PAT_ASSUM ``!s. C_SEM M g s ==> s IN STATES (CTL2MU g) (ctl2muks M) EMPTY_ENV`` (fn t => ALL_TAC)
  THEN PAT_ASSUM ``!s. s IN STATES (CTL2MU g) (ctl2muks M) EMPTY_ENV ==> C_SEM M g s`` (fn t => ALL_TAC)
  THEN PAT_ASSUM ``!s. C_SEM M f s = s IN STATES (CTL2MU f) (ctl2muks M) EMPTY_ENV``
                                       (fn t => ASSUME_TAC (REWRITE_RULE [GSYM FUN_EQ_THM] (SIMP_RULE std_ss [IN_DEF] t)))
  THEN PAT_ASSUM ``!s. C_SEM M g s = s IN STATES (CTL2MU g) (ctl2muks M) EMPTY_ENV``
                                       (fn t => ASSUME_TAC (REWRITE_RULE [GSYM FUN_EQ_THM] (SIMP_RULE std_ss [IN_DEF] t)))
  THEN POP_ASSUM (fn t => POP_ASSUM (fn t' => FULL_SIMP_TAC std_ss [SYM t,SYM t']))
  THEN FULL_SIMP_TAC std_ss [GSYM CTL2MU_AND_LEM,GSYM CTL2MU_OR_LEM,
                             (CONV_RULE (RAND_CONV(REWRITE_CONV [GSYM FUN_EQ_THM])))
                                 ((CONV_RULE FORALL_IMP_CONV)
                                      (ISPECL [``(M: ('prop,'state) kripke_structure)``,``f:'prop ctl``,``g:'prop ctl``]
                                                                     EU_LEMMA))]]]]);

val CTL2MU = save_thm("CTL2MU",SIMP_RULE std_ss [IMF_CTL] CTL2MU_LEM);

val CTL2MU_MODEL = save_thm("CTL2MU_MODEL",prove(``!(f: 'prop ctl) (M: ('prop,'state) kripke_structure).
                      (TOTAL M.R /\ wfKS (ctl2muks M) /\ FINITE (ctl2muks M).S) ==>
                      (CTL_MODEL_SAT M f = MU_MODEL_SAT (CTL2MU f) (ctl2muks M) EMPTY_ENV)``,
REPEAT STRIP_TAC THEN REWRITE_TAC [MU_MODEL_SAT_def,CTL_MODEL_SAT_def]
THEN CONV_TAC (RHS_CONV (QUANT_CONV (LAND_CONV (REWRITE_CONV[ctl2muks_def]))))
THEN REWRITE_TAC [combinTheory.K_THM,KS_accfupds]
THEN METIS_TAC [CTL2MU]))


val _ = export_theory();
