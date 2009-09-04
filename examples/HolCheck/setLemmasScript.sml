open HolKernel Parse boolLib bossLib

val _ = new_theory("setLemmas");

open pred_setLib pred_setTheory numLib metisLib pairTheory stringTheory stringLib

infix &&; infix 8 by;

val SET_SPEC = save_thm("SET_SPEC",prove(``!P x. x IN { y | P y} = P x``, RW_TAC std_ss [SET_SPEC_CONV `` x IN { y | P y}``]));

val DIFF_OVER_INTER = save_thm("DIFF_OVER_INTER",prove(``!s t u. s SUBSET u /\ t SUBSET u ==> (u DIFF (s INTER t) = (u DIFF s) UNION (u DIFF t))``, RW_TAC std_ss [SUBSET_DEF,IN_DIFF,IN_INTER,IN_UNION,DIFF_DEF,EXTENSION,SET_SPEC] THEN PROVE_TAC []));


val DIFF_OVER_UNION = save_thm("DIFF_OVER_UNION",prove(``!s t u. s SUBSET u /\ t SUBSET u ==> (u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t))``, RW_TAC std_ss [SUBSET_DEF,IN_DIFF,IN_INTER,IN_UNION,DIFF_DEF,EXTENSION,SET_SPEC] THEN PROVE_TAC []));

val DIFF_OVER_BIGUNION = save_thm("DIFF_OVER_BIGUNION",prove (``!P. (UNIV DIFF (BIGUNION {s | ?(n:num). s = (P n)})) = (BIGINTER {s | ?(n:num). (s = (UNIV DIFF (P n)))})``,RW_TAC std_ss [prove(``!P. BIGINTER {s | ?(n:num). s = UNIV DIFF P n} = {x | !(n:num). x IN UNIV DIFF P n}``,
			   RW_TAC std_ss [BIGINTER,EXTENSION,SET_SPEC] THEN RW_TAC std_ss [IN_DEF] THEN PROVE_TAC []),
                  prove(``!P. UNIV DIFF BIGUNION {s | ?n. s = P n} = {x | !n. x IN UNIV DIFF P n}``,
			   RW_TAC std_ss [BIGINTER,IN_UNIV,DIFF_DEF,EXTENSION,SET_SPEC,BIGUNION]
			   THEN RW_TAC std_ss [IN_DEF] THEN PROVE_TAC [])]));


val DIFF_OVER_BIGINTER = save_thm("DIFF_OVER_BIGINTER",prove(``!P. (UNIV DIFF (BIGINTER {s | ?n. s = (P n)})) = (BIGUNION {s | ?n. (s = (UNIV DIFF (P n)))})``,
RW_TAC std_ss [prove(``!P. BIGUNION {s | ?n. s = UNIV DIFF P n} = {x | ?n. x IN UNIV DIFF P n}``,
			   RW_TAC std_ss [BIGUNION,EXTENSION,SET_SPEC] THEN RW_TAC std_ss [IN_DEF] THEN PROVE_TAC []),
                  prove(``!P. UNIV DIFF BIGINTER {s | ?n. s = P n} = {x | ?n. x IN UNIV DIFF P n}``,
			   RW_TAC std_ss [BIGINTER,IN_UNIV,DIFF_DEF,EXTENSION,SET_SPEC,BIGUNION]
			   THEN RW_TAC std_ss [IN_DEF] THEN PROVE_TAC [])]));

val SET_GSPEC = save_thm("SET_GSPEC",prove(``!P x. { x | P x} = \x. P x``,
RW_TAC std_ss [EXTENSION,SET_SPEC,SPECIFICATION]));

val UNIV_DIFF_EQ = save_thm("UNIV_DIFF_EQ",prove (``!s t. (UNIV DIFF s = UNIV DIFF t) = (s = t)``,RW_TAC std_ss [IN_UNIV,DIFF_DEF,EXTENSION,SET_SPEC]));

val BIGINTER_LEMMA1 = save_thm("BIGINTER_LEMMA1",
prove (``!P Q. (!n. P n = Q n) ==> (BIGINTER {s | ?n. s = P n} = BIGINTER {s | ?n. s = Q n})``,
RW_TAC std_ss [BIGINTER,SET_SPEC,EXTENSION]));

val BIGUNION_LEMMA1 =  save_thm("BIGUNION_LEMMA1",prove(``!P Q. (!n. P n = Q n) ==> (BIGUNION {s | ?n. s = P n} = BIGUNION {s | ?n. s = Q n})``,
RW_TAC std_ss [BIGUNION,SET_SPEC,EXTENSION]));

val UNIV_DIFF_SUBSET = save_thm("UNIV_DIFF_SUBSET",prove (``!s t. (UNIV DIFF s SUBSET UNIV DIFF t) = (t SUBSET s)``,
FULL_SIMP_TAC std_ss [DIFF_DEF,SUBSET_DEF,SET_SPEC,IN_UNIV]
THEN PROVE_TAC []));

val SUBSET_DEST = save_thm("SUBSET_DEST",prove(``!s t. s SUBSET t = s SUBSET t \/ (s=t)``,PROVE_TAC [SUBSET_DEF]));

val EQ_IMP_SUBSET = save_thm("EQ_IMP_SUBSET",prove(``!P Q. (P = Q) ==> (P SUBSET Q)``,PROVE_TAC [SUBSET_DEF]));

val bus1 = save_thm("bus1",prove(``!(Q :num -> 'state -> bool) (n' :num).
      {(P :'state -> bool) | ?(n :num). P = Q n} =
      {P | ?(n :num). ~(n > n') /\ (P = Q n) \/ (n > n' \/ (n = n')) /\ (P = Q n)}``,
ONCE_REWRITE_TAC [EXTENSION]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN PROVE_TAC []));

val bus2 = save_thm("bus2",prove(``!P Q. (P = Q) ==> (BIGUNION P = BIGUNION Q)``,PROVE_TAC []));

val BIGUNION_PSPLIT = save_thm("BIGUNION_PSPLIT",prove(``!Q n'. BIGUNION {P | ?n.  ~(n=0) /\  (P = Q n)} =
      BIGUNION {P | ?n.  ~(n=0) /\ n <= n' /\ (P = Q n)} UNION BIGUNION {P | ?n. n > n' /\ (P = Q n)}``,
SIMP_TAC std_ss [GSYM BIGUNION_UNION,UNION_DEF,SET_SPEC,GSYM EXISTS_OR_THM]
THEN REPEAT GEN_TAC THEN MATCH_MP_TAC bus2
THEN ONCE_REWRITE_TAC [EXTENSION]
THEN CONV_TAC (QUANT_CONV (FORK_CONV (pred_setLib.SET_SPEC_CONV,pred_setLib.SET_SPEC_CONV)))
THEN GEN_TAC
THEN NTAC 2 (ONCE_REWRITE_TAC [RIGHT_OR_OVER_AND])
THEN REWRITE_TAC [DECIDE ``!n n'. n > n' = ~(n<=n')``]
THEN EQ_TAC THEN REPEAT STRIP_TAC THEN Q.EXISTS_TAC `n` THEN FULL_SIMP_TAC arith_ss []));

val BIGUNION_PSPLIT2 = save_thm("BIGUNION_PSPLIT2",prove(``!Q n'. BIGUNION {P | ?n.  (P = Q n)} =
      BIGUNION {P | ?n.  n <= n' /\ (P = Q n)} UNION BIGUNION {P | ?n. n > n' /\ (P = Q n)}``,
SIMP_TAC std_ss [GSYM BIGUNION_UNION,UNION_DEF,SET_SPEC,GSYM EXISTS_OR_THM]
THEN REPEAT GEN_TAC THEN MATCH_MP_TAC bus2
THEN ONCE_REWRITE_TAC [EXTENSION]
THEN CONV_TAC (QUANT_CONV (FORK_CONV (pred_setLib.SET_SPEC_CONV,pred_setLib.SET_SPEC_CONV)))
THEN GEN_TAC
THEN NTAC 2 (ONCE_REWRITE_TAC [RIGHT_OR_OVER_AND])
THEN REWRITE_TAC [DECIDE ``!n n'. n > n' = ~(n<=n')``]
THEN EQ_TAC THEN REPEAT STRIP_TAC THEN Q.EXISTS_TAC `n` THEN FULL_SIMP_TAC arith_ss []));

val BIGUNION_SPLIT = save_thm("BIGUNION_SPLIT",prove(``!Q n'. BIGUNION {P | ?n. (P = Q n)} =
      BIGUNION {P | ?n. n <= n' /\ (P = Q n)} UNION BIGUNION {P | ?n. n >= n' /\ (P = Q n)}``,
SIMP_TAC std_ss [GSYM BIGUNION_UNION,UNION_DEF,SET_SPEC,GSYM EXISTS_OR_THM, DECIDE ``!n n'. n<=n' = ~(n>n')``, DECIDE ``!n n'. n>=n' = (n>n') \/ (n=n')``]
THEN FULL_SIMP_TAC std_ss [bus1,bus2]));

val BIGUNION_SPLIT_EXISTS = save_thm("BIGUNION_SPLIT_EXISTS",prove(``?n'. !Q. BIGUNION {P | ?n. (P = Q n)} =
      BIGUNION {P | ?n. n <= n' /\ (P = Q n)} UNION BIGUNION {P | ?n. n >= n' /\ (P = Q n)}``,METIS_TAC [BIGUNION_SPLIT]))

val SUBSET_DEST2 = save_thm("SUBSET_DEST2",prove(``!s t. s SUBSET t = s PSUBSET t \/ (s=t)``,SIMP_TAC std_ss [SUBSET_DEF,PSUBSET_DEF,IN_DEF] THEN PROVE_TAC []));

val PSUBSET_CARD_LT = save_thm("PSUBSET_CARD_LT",prove(``!s t. FINITE s /\ FINITE t ==> (s PSUBSET t ==> CARD s < CARD t)``,PROVE_TAC [CARD_PSUBSET]));

val SUBSET_CARD_LTE = save_thm("SUBSET_CARD_LTE",prove(``!s t. FINITE s /\ FINITE t ==> (s SUBSET t ==> CARD s <= CARD t)``,PROVE_TAC [CARD_SUBSET]));

val GEN_PCHAIN_CARD_NO_UB = save_thm("GEN_PCHAIN_CARD_NO_UB",prove(``!(P:num -> 'state -> bool). (!n. CARD (P n) < (CARD (P (SUC n)))) ==> !m. ?n. (CARD (P n) > m)``,
REPEAT STRIP_TAC THEN Induct_on `m` THENL [
EXISTS_TAC ``1``
THEN `CARD ((P:num -> 'state -> bool) 0) >= 0` by ARITH_TAC
THEN `CARD ((P:num -> 'state -> bool) 0) < CARD (P 1)` by ASSUM_LIST (fn t => PROVE_TAC ((DECIDE ``SUC 0 = 1``)::t))
THEN FULL_SIMP_TAC arith_ss [], (* 0 *)
(SUBGOAL_THEN ``?n. CARD ((P:num -> 'state -> bool) (n:num)) >= (SUC m)`` ASSUME_TAC) THENL [
FULL_SIMP_TAC std_ss [DECIDE ``!n m. n>m = n>=(SUC m)``] THEN ASSUM_LIST PROVE_TAC,
(SUBGOAL_THEN ``(?n. CARD ((P:num -> 'state -> bool) (n:num))>(SUC m)) \/ (?n. CARD (P (n:num))=(SUC m))`` ASSUME_TAC) THENL [
(CONV_TAC OR_EXISTS_CONV) THEN ASSUM_LIST (fn t => PROVE_TAC ((DECIDE ``!m n. m>=n = (m>n \/ (m=n))``)::t)),
UNDISCH_TAC ``(?(n :num). CARD ((P :num -> 'state -> bool) n) > SUC (m :num)) \/ ?(n :num). CARD (P n) = SUC m``
THEN REPEAT STRIP_TAC THENL [ASSUM_LIST PROVE_TAC,
(SUBGOAL_THEN ``CARD ((P:num -> 'state -> bool) (SUC n)) > (SUC m)`` ASSUME_TAC) THENL [ASSUM_LIST (fn t => PROVE_TAC ((DECIDE ``!m n. m>n = n<m``)::t)),
EXISTS_TAC ``SUC n`` THEN ASM_REWRITE_TAC []]]]]
]));

val BIGUNION_LEM2 = save_thm("BIGUNION_LEM2",prove(``!P Q. (!n. P n SUBSET Q n) ==> BIGUNION {p | ?n. (p = P n)} SUBSET BIGUNION {p | ?n. (p = Q n)}``,
SIMP_TAC std_ss [BIGUNION,SET_SPEC,SUBSET_DEF] THEN PROVE_TAC []));

val SUBSET_EQ = save_thm("SUBSET_EQ",prove(``!s t. s SUBSET t /\ t SUBSET s = (s=t)``,
REPEAT STRIP_TAC THEN EQ_TAC THENL [
SIMP_TAC std_ss [SUBSET_ANTISYM],
SIMP_TAC std_ss [SUBSET_DEF,IN_DEF]]));

val BIGUNION_SUBSET_IMP = save_thm("BIGUNION_SUBSET_IMP",prove(``!P Q. (!n. P n SUBSET Q n) ==> BIGUNION {P' | ?n. P' = P n} SUBSET BIGUNION {Q' | ?n. Q' = Q n}``,
REPEAT STRIP_TAC THEN SIMP_TAC std_ss [BIGUNION] THEN SIMP_TAC std_ss [SUBSET_DEF,SET_SPEC] THEN FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN ASSUM_LIST PROVE_TAC));

val LEFT_BIGUNION_SUBSET = save_thm("LEFT_BIGUNION_SUBSET",prove(``!X P. (!n. P n SUBSET X) ==> BIGUNION {Q | ?n. Q = P n} SUBSET X``,
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [BIGUNION,SUBSET_DEF,SET_SPEC]
THEN REPEAT STRIP_TAC
THEN ASSUM_LIST PROVE_TAC))

val BIGINTER_SUBSET_IMP = save_thm("BIGINTER_SUBSET_IMP",prove(``!P Q. (!n. P n SUBSET Q n) ==> BIGINTER {P' | ?n. P' = P n} SUBSET BIGINTER {Q' | ?n. Q' = Q n}``,
REPEAT STRIP_TAC THEN SIMP_TAC std_ss [BIGINTER] THEN SIMP_TAC std_ss [SUBSET_DEF,SET_SPEC] THEN FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN ASSUM_LIST PROVE_TAC));

val LEFT_BIGINTER_SUBSET = save_thm("LEFT_BIGINTER_SUBSET",prove(``!X P. (!n. X SUBSET P n) ==> X SUBSET BIGINTER {Q | ?n. Q = P n}``,
REPEAT STRIP_TAC
THEN FULL_SIMP_TAC std_ss [BIGINTER,SUBSET_DEF,SET_SPEC]
THEN REPEAT STRIP_TAC
THEN ASSUM_LIST PROVE_TAC))

val BIGINTER_SPLIT = save_thm("BIGINTER_SPLIT",prove(``!Q n'. BIGINTER {P | ?n. P = Q n} =
      BIGINTER {P | ?n. n <= n' /\ (P = Q n)} INTER BIGINTER {P | ?n. n >= n' /\ (P = Q n)}``,
SIMP_TAC std_ss [BIGINTER,INTER_DEF,SET_SPEC,GSYM FORALL_AND_THM, DECIDE ``!n n'. n<=n' = ~(n>n')``, DECIDE ``!n n'. n>=n' = (n>n') \/ (n=n')``]
THEN ONCE_REWRITE_TAC [EXTENSION]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN PROVE_TAC []));

val BIGINTER_INTER =  save_thm("BIGINTER_INTER",prove(``!s1 s2. BIGINTER (s1 UNION s2) = (BIGINTER s1) INTER (BIGINTER s2)``,
SIMP_TAC std_ss [BIGINTER,UNION_DEF,INTER_DEF,SET_SPEC]
THEN ONCE_REWRITE_TAC [EXTENSION]
THEN SIMP_TAC std_ss [SET_SPEC]
THEN SIMP_TAC std_ss [GSYM FORALL_AND_THM]
THEN PROVE_TAC []));

val BIGINTER_SUBSET = save_thm("BIGINTER_SUBSET",prove(``!P Q. (!n. P n SUBSET Q n) ==> BIGINTER {P' | ?n. P' = P n} SUBSET BIGINTER {Q' | ?n. Q' = Q n}``,
REPEAT STRIP_TAC THEN SIMP_TAC std_ss [BIGINTER] THEN SIMP_TAC std_ss [SUBSET_DEF,SET_SPEC] THEN FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN ASSUM_LIST PROVE_TAC));

val BOOL_UNIV_FINITE = save_thm("BOOL_UNIV_FINITE",prove(``FINITE (UNIV:bool->bool)``,
SUBGOAL_THEN ``?f b. !e. e IN (UNIV:bool->bool) = ?n. n<b /\ (e = f n)``  ASSUME_TAC
THENL [
EXISTS_TAC ``\n. if (n=0) then T else F``
THEN EXISTS_TAC ``2``
THEN GEN_TAC THEN EQ_TAC THENL [
BETA_TAC THEN Cases_on `e` THENL [
SIMP_TAC std_ss [UNIV_DEF,IN_DEF],
SIMP_TAC std_ss [UNIV_DEF,IN_DEF]
THEN EXISTS_TAC ``1``
THEN SIMP_TAC arith_ss []],
SIMP_TAC std_ss [IN_UNIV]],
FULL_SIMP_TAC std_ss [GSYM FINITE_WEAK_ENUMERATE]]));

val UNIV_CROSS_UNIV = save_thm("UNIV_CROSS_UNIV",prove(``(UNIV:bool -> bool) CROSS (UNIV:'state->bool) = (UNIV:(bool # 'state)->bool)``,
SIMP_TAC std_ss [UNIV_DEF,CROSS_DEF,FST,SND,IN_DEF,SET_GSPEC]));

val IN_APPLY = save_thm("IN_APPLY",prove(``!P x. x IN P = P x``,SIMP_TAC std_ss [IN_DEF] THEN BETA_TAC));

val IMPLODE_EXPLODE_BIJ = prove(``BIJ (IMPLODE o EXPLODE) UNIV UNIV``,
SIMP_TAC std_ss [BIJ_DEF,INJ_DEF,SURJ_DEF,IN_UNIV,IMPLODE_ONTO,EXPLODE_ONTO,IMPLODE_11,EXPLODE_11,INJ_COMPOSE,SURJ_COMPOSE]THEN METIS_TAC [IMPLODE_EXPLODE])

val PRIME_def = Define `PRIME s = STRCAT s "'"`;

val PRIME_11 = prove(``!x y. (PRIME x = PRIME y) ==> (x=y)``,
Induct_on `x` THEN Induct_on `y` THEN REWRITE_TAC [PRIME_def] THEN METIS_TAC [STRCAT_11])

val PRIME_NOT_ONTO = prove(``?y. !x. ~(PRIME x = y)``,
Q.EXISTS_TAC `""`
THEN Induct_on `x` THENL [
 REWRITE_TAC [PRIME_def] THEN EVAL_TAC,
 GEN_TAC THEN REWRITE_TAC [PRIME_def] THEN EVAL_TAC
])

val INF_STRING_UNIV = save_thm("INF_STRING_UNIV",prove(``INFINITE (UNIV:string->bool)``,
REWRITE_TAC [INFINITE_UNIV]
THEN Q.EXISTS_TAC `PRIME`
THEN METIS_TAC [PRIME_11,PRIME_NOT_ONTO]))

val NOT_IN_FIN_STRING_SET = save_thm("NOT_IN_FIN_STRING_SET",prove(``!s. FINITE s ==> ?(x:string). ~(x IN s)``,
 REPEAT STRIP_TAC
 THEN ASSUME_TAC INF_STRING_UNIV
 THEN IMP_RES_TAC INFINITE_DIFF_FINITE
 THEN FULL_SIMP_TAC std_ss [DIFF_DEF,IN_UNIV,SET_GSPEC,EMPTY_DEF]
 THEN METIS_TAC []))

(* used by commonTools.PUSH_IMP_CONV *)
val PUSH_IMP_THM = save_thm("PUSH_IMP_THM",prove(``!a b c. a ==> b ==> c = b ==> a ==> c``,PROVE_TAC []))

val _ = export_theory();
