open HolKernel Parse boolLib bossLib arithmeticTheory pred_setTheory
     listTheory sequenceTheory state_transformerTheory
     hurdUtils extra_numTheory combinTheory
     pairTheory realTheory realLib extra_boolTheory
     extra_pred_setTheory sumTheory res_quanTheory
     extra_realTheory extra_pred_setTools numTheory
     simpLib seqTheory sequenceTools subtypeTheory;

open util_probTheory real_measureTheory real_probabilityTheory;
open prob_algebraTheory probTheory;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "prob_trichotomy";

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val std_ss' = std_ss ++ boolSimps.ETA_ss;
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val STRONG_DISJ_TAC = CONV_TAC (REWR_CONV (GSYM IMP_DISJ_THM)) >> STRIP_TAC;
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond >| [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

(* ------------------------------------------------------------------------- *)
(* The simple trichotomy example used in the thesis.                         *)
(* ------------------------------------------------------------------------- *)

val prob_trichotomy_iter_def = Define
  `prob_trichotomy_iter = BIND sdest (\x. BIND sdest (\y. UNIT (x, y)))`;

val prob_trichotomy_def = Define
  `prob_trichotomy = prob_until prob_trichotomy_iter (\(x,y). x \/ y)`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. !k.                                                                    *)
(*      prob bern {s | FST (prob_trichotomy s) = k} =                        *)
(*      if k = (F, F) then 0 else 1 / 3                                      *)
(* ------------------------------------------------------------------------- *)

val INDEP_FN_PROB_TRICHOTOMY_ITER = store_thm
  ("INDEP_FN_PROB_TRICHOTOMY_ITER",
   ``prob_trichotomy_iter IN indep_fn``,
   RW_TAC std_ss [prob_trichotomy_iter_def, INDEP_FN_BIND, INDEP_FN_UNIT,
                  INDEP_FN_SDEST]);

val PROB_BERN_TRICHOTOMY_ITER = store_thm
  ("PROB_BERN_TRICHOTOMY_ITER",
   ``!s. prob bern (s o FST o prob_trichotomy_iter) = & (CARD s) / 4``,
   STRIP_TAC
   >> MATCH_MP_TAC REAL_EQ_LMUL_IMP
   >> Q.EXISTS_TAC `4`
   >> RW_TAC arith_ss [REAL_INJ, REAL_DIV_LMUL]
   >> ONCE_REWRITE_TAC [SET_PAIR_BOOL]
   >> SIMP_TAC std_ss [GSYM PREIMAGE_ALT, PREIMAGE_UNION]
   >> SIMP_TAC std_ss [PREIMAGE_ALT, GSYM UNION_ASSOC]
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC
      `4 * prob bern
         ((if (T,T) IN s then {(T,T)} else {}) o FST o prob_trichotomy_iter) +
       4 * prob bern
         ((if (T,F) IN s then {(T,F)} else {}) o FST o prob_trichotomy_iter
          UNION
          ((if (F,T) IN s then {(F,T)} else {}) o FST o prob_trichotomy_iter
           UNION
           (if (F,F) IN s then {(F,F)} else {}) o FST o prob_trichotomy_iter))`
   >> CONJ_TAC
   >- (SIMP_TAC arith_ss [GSYM REAL_ADD_LDISTRIB, REAL_EQ_LMUL, REAL_INJ]
       >> MATCH_MP_TAC PROB_ADDITIVE
       >> SIMP_TAC std_ss [INDEP_FN_FST_EVENTS, PROB_SPACE_BERN,
                           INDEP_FN_PROB_TRICHOTOMY_ITER, EVENTS_UNION,
                           IN_DISJOINT, IN_UNION]
       >> STRIP_TAC
       >> SEQ_CASES_TAC `x`
       >> SEQ_CASES_TAC `t`
       >> RW_TAC std_ss [IN_o, o_THM, prob_trichotomy_iter_def, BIND_DEF,
                         UNCURRY, UNIT_DEF, SHD_SCONS, STL_SCONS, sdest_def,
                         IN_INSERT, NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC
      `& (CARD (if (T,T) IN s then {(T,T)} else {})) +
       & (CARD
          ((if (T,F) IN s then {(T,F)} else {}) UNION
           ((if (F,T) IN s then {(F,T)} else {}) UNION
            (if (F,F) IN s then {(F,F)} else {}))))`
   >> REVERSE CONJ_TAC
   >- (SIMP_TAC std_ss [Q.ISPEC `if (T,T) IN s then {(T,T)} else {}`
                        (GSYM CARD_UNION), FINITE_PAIR_BOOL, REAL_ADD]
       >> RW_TAC arith_ss [INSERT_INTER, IN_UNION, IN_INSERT, NOT_IN_EMPTY,
                           INTER_EMPTY, CARD_EMPTY])
   >> Know `!a b c d : real. (a = c) /\ (b = d) ==> (a + b = c + d)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> CONJ_TAC
   >- (Suff
       `!a b.
          (if (a,b) IN s then {(a,b)} else {}) o FST o prob_trichotomy_iter =
          (if (a,b) IN s then prefix_set [a; b] else {})`
       >- (Rewr
           >> RW_TAC bool_ss [CARD_EMPTY, CARD_INSERT, FINITE_EMPTY,
                              NOT_IN_EMPTY, PROB_BERN_EMPTY, REAL_MUL_RZERO,
                              PROB_BERN_PREFIX_SET, LENGTH, pow, REAL_MUL_RID]
           >> RW_TAC arith_ss [GSYM REAL_INV_1OVER, GSYM REAL_INV_MUL, REAL_INJ,
                               REAL_MUL, REAL_MUL_RINV])
       >> SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM, NOT_IN_EMPTY]
       >> SEQ_CASES_TAC `x`
       >> SEQ_CASES_TAC `t`
       >> RW_TAC std_ss [IN_INSERT, prefix_set_def, IN_HALFSPACE, SHD_SCONS,
                         STL_SCONS, sdest_def, prob_trichotomy_iter_def,
                         BIND_DEF, UNCURRY, o_THM, UNIT_DEF, NOT_IN_EMPTY,
                         IN_INTER, IN_UNIV, IN_o])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC
      `4 * prob bern
         ((if (T,F) IN s then {(T,F)} else {}) o FST o prob_trichotomy_iter) +
       4 * prob bern
         ((if (F,T) IN s then {(F,T)} else {}) o FST o prob_trichotomy_iter
          UNION
          (if (F,F) IN s then {(F,F)} else {}) o FST o prob_trichotomy_iter)`
   >> CONJ_TAC
   >- (SIMP_TAC arith_ss [GSYM REAL_ADD_LDISTRIB, REAL_EQ_LMUL, REAL_INJ]
       >> MATCH_MP_TAC PROB_ADDITIVE
       >> SIMP_TAC std_ss [INDEP_FN_FST_EVENTS, PROB_SPACE_BERN,
                           INDEP_FN_PROB_TRICHOTOMY_ITER, EVENTS_UNION,
                           IN_DISJOINT, IN_UNION]
       >> STRIP_TAC
       >> SEQ_CASES_TAC `x`
       >> SEQ_CASES_TAC `t`
       >> RW_TAC std_ss [IN_o, o_THM, prob_trichotomy_iter_def, BIND_DEF,
                         UNCURRY, UNIT_DEF, SHD_SCONS, STL_SCONS, sdest_def,
                         IN_INSERT, NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC
      `& (CARD (if (T,F) IN s then {(T,F)} else {})) +
       & (CARD
          ((if (F,T) IN s then {(F,T)} else {}) UNION
           (if (F,F) IN s then {(F,F)} else {})))`
   >> REVERSE CONJ_TAC
   >- (SIMP_TAC std_ss [Q.ISPEC `if (T,F) IN s then {(T,F)} else {}`
                        (GSYM CARD_UNION), FINITE_PAIR_BOOL, REAL_ADD]
       >> RW_TAC arith_ss [INSERT_INTER, IN_UNION, IN_INSERT, NOT_IN_EMPTY,
                           INTER_EMPTY, CARD_EMPTY])
   >> Know `!a b c d : real. (a = c) /\ (b = d) ==> (a + b = c + d)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> CONJ_TAC
   >- (Suff
       `!a b.
          (if (a,b) IN s then {(a,b)} else {}) o FST o prob_trichotomy_iter =
          (if (a,b) IN s then prefix_set [a; b] else {})`
       >- (Rewr
           >> RW_TAC bool_ss [CARD_EMPTY, CARD_INSERT, FINITE_EMPTY,
                              NOT_IN_EMPTY, PROB_BERN_EMPTY, REAL_MUL_RZERO,
                              PROB_BERN_PREFIX_SET, LENGTH, pow, REAL_MUL_RID]
           >> RW_TAC arith_ss [GSYM REAL_INV_1OVER, GSYM REAL_INV_MUL, REAL_INJ,
                               REAL_MUL, REAL_MUL_RINV])
       >> SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM, NOT_IN_EMPTY]
       >> SEQ_CASES_TAC `x`
       >> SEQ_CASES_TAC `t`
       >> RW_TAC std_ss [IN_INSERT, prefix_set_def, IN_HALFSPACE, SHD_SCONS,
                         STL_SCONS, sdest_def, prob_trichotomy_iter_def,
                         BIND_DEF, UNCURRY, o_THM, UNIT_DEF, NOT_IN_EMPTY,
                         IN_INTER, IN_UNIV, IN_o])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC
      `4 * prob bern
         ((if (F,T) IN s then {(F,T)} else {}) o FST o prob_trichotomy_iter) +
       4 * prob bern
         ((if (F,F) IN s then {(F,F)} else {}) o FST o prob_trichotomy_iter)`
   >> CONJ_TAC
   >- (SIMP_TAC arith_ss [GSYM REAL_ADD_LDISTRIB, REAL_EQ_LMUL, REAL_INJ]
       >> MATCH_MP_TAC PROB_ADDITIVE
       >> SIMP_TAC std_ss [INDEP_FN_FST_EVENTS, PROB_SPACE_BERN,
                           INDEP_FN_PROB_TRICHOTOMY_ITER, EVENTS_UNION,
                           IN_DISJOINT, IN_UNION]
       >> STRIP_TAC
       >> SEQ_CASES_TAC `x`
       >> SEQ_CASES_TAC `t`
       >> RW_TAC std_ss [IN_o, o_THM, prob_trichotomy_iter_def, BIND_DEF,
                         UNCURRY, UNIT_DEF, SHD_SCONS, STL_SCONS, sdest_def,
                         IN_INSERT, NOT_IN_EMPTY]
       >> PROVE_TAC [])
   >> MATCH_MP_TAC EQ_TRANS
   >> Q.EXISTS_TAC
      `& (CARD (if (F,T) IN s then {(F,T)} else {})) +
       & (CARD (if (F,F) IN s then {(F,F)} else {}))`
   >> REVERSE CONJ_TAC
   >- (SIMP_TAC std_ss [Q.ISPEC `if (F,T) IN s then {(F,T)} else {}`
                        (GSYM CARD_UNION), FINITE_PAIR_BOOL, REAL_ADD]
       >> RW_TAC arith_ss [INSERT_INTER, IN_UNION, IN_INSERT, NOT_IN_EMPTY,
                           INTER_EMPTY, CARD_EMPTY])
   >> Know `!a b c d : real. (a = c) /\ (b = d) ==> (a + b = c + d)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> CONJ_TAC \\ (* 2 sub-goals here *)
    ( Suff
      `!a b.
         (if (a,b) IN s then {(a,b)} else {}) o FST o prob_trichotomy_iter =
         (if (a,b) IN s then prefix_set [a; b] else {})`
   >- (Rewr
       >> RW_TAC bool_ss [CARD_EMPTY, CARD_INSERT, FINITE_EMPTY,
                          NOT_IN_EMPTY, PROB_BERN_EMPTY, REAL_MUL_RZERO,
                          PROB_BERN_PREFIX_SET, LENGTH, pow, REAL_MUL_RID]
       >> RW_TAC arith_ss [GSYM REAL_INV_1OVER, GSYM REAL_INV_MUL, REAL_INJ,
                           REAL_MUL, REAL_MUL_RINV])
   >> SET_EQ_TAC
   >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM, NOT_IN_EMPTY]
   >> SEQ_CASES_TAC `x`
   >> SEQ_CASES_TAC `t`
   >> RW_TAC std_ss [IN_INSERT, prefix_set_def, IN_HALFSPACE, SHD_SCONS,
                     STL_SCONS, sdest_def, prob_trichotomy_iter_def, BIND_DEF,
                     UNCURRY, o_THM, UNIT_DEF, NOT_IN_EMPTY, IN_INTER,
                     IN_UNIV, IN_o] ));

val PROB_TRICHOTOMY_SET = store_thm
  ("PROB_TRICHOTOMY_SET",
   ``{a | (\(x,y). x \/ y) a} = {(T, T); (T, F); (F, T)}``,
   ONCE_REWRITE_TAC [SET_PAIR_BOOL]
   >> RW_TAC arith_ss [GSPECIFICATION, INSERT_UNION, IN_INSERT, NOT_IN_EMPTY,
                       UNION_EMPTY]);

val PROB_TERMINATES_TRICHOTOMY = store_thm
  ("PROB_TERMINATES_TRICHOTOMY",
   ``?*s. (\(x,y). x \/ y) (FST (prob_trichotomy_iter s))``,
   RW_TAC arith_ss [possibly_bern_def, possibly_def, EVENT_TRANSITION,
                    INDEP_FN_FST_EVENTS, INDEP_FN_PROB_TRICHOTOMY_ITER,
                    PROB_BERN_TRICHOTOMY_ITER, PROB_TRICHOTOMY_SET, CARD_INSERT,
                    FINITE_PAIR_BOOL, CARD_EMPTY, NOT_IN_EMPTY, IN_INSERT, ADD1]
   >> Suff `(0 :real) < 3 / 4` >- REAL_ARITH_TAC
   >> RW_TAC arith_ss [REAL_LT_DIV, REAL_LT]);

val INDEP_FN_PROB_TRICHOTOMY = store_thm
  ("INDEP_FN_PROB_TRICHOTOMY",
   ``prob_trichotomy IN indep_fn``,
   RW_TAC std_ss [prob_trichotomy_def, INDEP_FN_PROB_UNTIL,
                  INDEP_FN_PROB_TRICHOTOMY_ITER, PROB_TERMINATES_TRICHOTOMY]);

val PROB_TRICHOTOMY = store_thm
  ("PROB_TRICHOTOMY",
   ``!k.
       prob bern {s | FST (prob_trichotomy s) = k} =
       if k = (F, F) then 0 else 1 / 3``,
   Know `!k. {s | FST (prob_trichotomy s) = k} = {k} o FST o prob_trichotomy`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM, IN_INSERT, NOT_IN_EMPTY])
   >> Rewr
   >> SIMP_TAC std_ss [PROB_BERN_UNTIL, prob_trichotomy_def,
                       PROB_TERMINATES_TRICHOTOMY,
                       INDEP_FN_PROB_TRICHOTOMY_ITER,
                       PROB_BERN_TRICHOTOMY_ITER, PROB_TRICHOTOMY_SET,
                       INSERT_INTER, INTER_EMPTY, IN_INSERT, NOT_IN_EMPTY]
   >> Cases
   >> Cases_on `q`
   >> Cases_on `r`
   >> RW_TAC arith_ss [CARD_INSERT, FINITE_PAIR_BOOL, CARD_EMPTY, NOT_IN_EMPTY,
                       IN_INSERT, ADD1, REAL_DIV_LZERO]
   >> RW_TAC real_ss []);

val PROB_TRICHOTOMY_COMPUTE = store_thm
  ("PROB_TRICHOTOMY_COMPUTE",
   ``!s.
       prob_trichotomy s =
       BIND sdest
       (\x. BIND sdest (\y. if x \/ y then UNIT (x,y) else prob_trichotomy))
       s``,
   STRIP_TAC
   >> CONV_TAC (LAND_CONV (REWRITE_CONV [prob_trichotomy_def]))
   >> RW_TAC std_ss [CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) PROB_UNTIL_ADVANCE,
                     INDEP_FN_PROB_TRICHOTOMY_ITER, PROB_TERMINATES_TRICHOTOMY]
   >> RW_TAC std_ss [GSYM prob_trichotomy_def]
   >> RW_TAC std_ss [prob_trichotomy_iter_def, GSYM BIND_ASSOC,
                     BIND_LEFT_UNIT]);

val _ = export_theory ();
