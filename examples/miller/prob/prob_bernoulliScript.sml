open HolKernel Parse boolLib bossLib;

open arithmeticTheory pred_setTheory
     listTheory state_transformerTheory
     hurdUtils extra_numTheory combinTheory
     pairTheory realTheory realLib extra_boolTheory
     extra_pred_setTheory sumTheory
     extra_realTheory extra_pred_setTools numTheory
     simpLib seqTheory res_quanTheory;

open sequenceTheory sequenceTools subtypeTheory;
open util_probTheory real_measureTheory real_probabilityTheory;
open prob_algebraTheory probTheory;

val _ = new_theory "prob_bernoulli";

val std_ss' = std_ss ++ boolSimps.ETA_ss;

(* ------------------------------------------------------------------------- *)
(* The definition of the Bernoulli(p) sampling algorithm.                    *)
(* ------------------------------------------------------------------------- *)

val prob_bernoulli_iter_def = Define
  `prob_bernoulli_iter p =
   BIND sdest
   (\b.
    UNIT
    (if b then (if p <= (1 :real) / 2 then INR F else INL (2 * p - 1))
     else (if p <= 1 / 2 then INL (2 * p) else INR T)))`;

val prob_bernoulli_loop_def = new_definition
  ("prob_bernoulli_loop_def",
   ``prob_bernoulli_loop = prob_while ISL (prob_bernoulli_iter o OUTL)``);

val prob_bernoulli_def = Define
  `prob_bernoulli p = BIND (prob_bernoulli_loop (INL p)) (\a. UNIT (OUTR a))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. !p. 0 <= p /\ p <= 1 ==> prob bern {s | FST (prob_bernoulli p s)} = p  *)
(* ------------------------------------------------------------------------- *)

val INDEP_FN_PROB_BERNOULLI_ITER = store_thm
  ("INDEP_FN_PROB_BERNOULLI_ITER",
   ``!p. prob_bernoulli_iter p IN indep_fn``,
   RW_TAC std_ss [INDEP_FN_BIND, INDEP_FN_UNIT, prob_bernoulli_iter_def,
                  INDEP_FN_SDEST]);

val PROB_TERMINATES_BERNOULLI = store_thm
  ("PROB_TERMINATES_BERNOULLI",
   ``prob_while_terminates ISL (prob_bernoulli_iter o OUTL)``,
   RW_TAC std_ss [PROB_TERMINATES_HART, o_THM, INDEP_FN_PROB_BERNOULLI_ITER]
   >> Q.EXISTS_TAC `1 / 2`
   >> RW_TAC std_ss [HALF_POS, GBIGUNION_IMAGE]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC
      `prob bern
       ({x | ~ISL x} o FST o
        prob_while_cut ISL (prob_bernoulli_iter o OUTL) 1 a)`
   >> REVERSE CONJ_TAC
   >- (MATCH_MP_TAC PROB_INCREASING
       >> RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_BERNOULLI_ITER,
                         PROB_SPACE_BERN, INDEP_FN_PROB_WHILE_CUT, o_THM] >|
       [MATCH_MP_TAC EVENTS_COUNTABLE_UNION
        >> RW_TAC std_ss [PROB_SPACE_BERN, SUBSET_DEF, IN_UNIV, COUNTABLE_NUM,
                          IN_IMAGE, image_countable]
        >> Know
           `{s |
             ISR (FST (prob_while_cut
                        ISL (prob_bernoulli_iter o OUTL) n a s))} =
            {x | ISR x} o FST o
            prob_while_cut ISL (prob_bernoulli_iter o OUTL) n a`
        >- (SET_EQ_TAC
            >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM])
        >> Rewr
        >> RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_BERNOULLI_ITER,
                          PROB_SPACE_BERN, INDEP_FN_PROB_WHILE_CUT, o_THM],
        RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION,
                       IN_o, o_THM]
        >> PROVE_TAC []])
   >> REVERSE (Cases_on `a`)
   >- (RW_TAC std_ss [PROB_WHILE_CUT_ID, UNIT_DEF]
       >> Suff
          `{(x:real+bool) | ~ISL x} o FST o (\s. (INR y, s)) =
           (UNIV:(num->bool)->bool)`
       >- RW_TAC std_ss [PROB_BERN_UNIV, REAL_LT_IMP_LE, HALF_LT_1]
       >> SET_EQ_TAC
       >> RW_TAC std_ss [IN_UNIV, GSPECIFICATION, IN_o, o_THM])
   >> RW_TAC bool_ss [ONE]
   >> RW_TAC std_ss [prob_while_cut_def, PROB_WHILE_CUT_0,
                      BIND_RIGHT_UNIT, o_THM]
   >> MP_TAC (Q.SPEC `{x | ISR x} o FST o prob_bernoulli_iter x`
              (GSYM PROB_BERN_INTER_HALVES))
   >> impl_tac >- RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_BERNOULLI_ITER]
   >> Rewr'
   >> RW_TAC std_ss [prob_bernoulli_iter_def] \\ (* 2 sub-goals here *)
 ( Know `!f b.
         halfspace b INTER {x:real+bool | ISR x} o FST o BIND sdest (\b. f b) =
         halfspace b INTER ({x | ISR x} o FST o f b) o stl`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_o, o_THM, IN_HALFSPACE, IN_INTER, GSPECIFICATION,
                         BIND_DEF, UNCURRY, sdest_def]
       >> Cases_on `shd x'`
       >> Cases_on `b`
       >> RW_TAC std_ss [])
   >> DISCH_THEN (fn th => RW_TAC std_ss [th])
   >> RW_TAC bool_ss [REWRITE_RULE [o_ASSOC] INDEP_FN_FST_EVENTS,
                      PROB_BERN_STL_HALFSPACE, INDEP_FN_UNIT, o_ASSOC]
   >> RW_TAC bool_ss [GSYM o_ASSOC]
   >> Know
      `!x:real+bool.
         {x | ISR x} o FST o UNIT x =
         if ISL x then {} else (UNIV:(num->bool)->bool)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM, UNIT_DEF, IN_UNIV,
                         NOT_IN_EMPTY]
       >> FULL_SIMP_TAC (srw_ss()) [])
   >> Rewr
   >> RW_TAC std_ss [PROB_BERN_UNIV, PROB_BERN_EMPTY, GSYM ONE]
   >> RW_TAC real_ss [REAL_LE_REFL] ));

val INDEP_FN_PROB_BERNOULLI_LOOP = store_thm
  ("INDEP_FN_PROB_BERNOULLI_LOOP",
   ``!a. prob_bernoulli_loop a IN indep_fn``,
   RW_TAC std_ss [prob_bernoulli_loop_def, INDEP_FN_PROB_WHILE,
                  PROB_TERMINATES_BERNOULLI, INDEP_FN_PROB_BERNOULLI_ITER,
                  o_THM]);

val INDEP_FN_PROB_BERNOULLI = store_thm
  ("INDEP_FN_PROB_BERNOULLI",
   ``!p. prob_bernoulli p IN indep_fn``,
   RW_TAC std_ss [prob_bernoulli_def, INDEP_FN_BIND, INDEP_FN_UNIT,
                  INDEP_FN_PROB_BERNOULLI_LOOP]);

val PROB_BERNOULLI_ALT = store_thm
  ("PROB_BERNOULLI_ALT",
   ``prob_bernoulli p =
     BIND sdest
     (\b.
      if b then (if p <= 1 / 2 then UNIT F else prob_bernoulli (2 * p - 1))
      else (if p <= 1 / 2 then prob_bernoulli (2 * p) else UNIT T))``,
   SIMP_TAC std_ss [prob_bernoulli_def, prob_bernoulli_loop_def]
   >> MP_TAC (Q.SPECL [`ISL`, `prob_bernoulli_iter o OUTL`, `INL p`]
              (INST_TYPE [alpha |-> ``:real+bool``] PROB_WHILE_ADVANCE))
   >> impl_tac
   >- RW_TAC std_ss [INDEP_FN_PROB_BERNOULLI_ITER, PROB_TERMINATES_BERNOULLI,
                     o_THM]
   >> Rewr
   >> RW_TAC std_ss [o_THM, prob_bernoulli_iter_def, GSYM BIND_ASSOC,
                     BIND_LEFT_UNIT]
   >> RW_TAC (std_ss ++ boolSimps.COND_elim_ss) []
   >> RW_TAC std_ss [PROB_WHILE_ADVANCE, INDEP_FN_PROB_BERNOULLI_ITER, o_THM,
                     PROB_TERMINATES_BERNOULLI]
   >> RW_TAC (std_ss ++ boolSimps.COND_elim_ss) []
   >> RW_TAC std_ss [BIND_LEFT_UNIT]);

val PROB_BERNOULLI = store_thm
  ("PROB_BERNOULLI",
   ``!p. 0 <= p /\ p <= 1 ==> (prob bern {s | FST (prob_bernoulli p s)} = p)``,
   Know `!p. {s | FST (prob_bernoulli p s)} = I o FST o prob_bernoulli p`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM, IN_I])
   >> Rewr
   >> Know `!p. 0 <= prob bern (I o FST o prob_bernoulli p)`
   >- RW_TAC std_ss [PROB_POSITIVE, PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                     INDEP_FN_PROB_BERNOULLI]
   >> STRIP_TAC
   >> Know `!p. prob bern (I o FST o prob_bernoulli p) <= 1`
   >- RW_TAC std_ss [PROB_LE_1, PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                     INDEP_FN_PROB_BERNOULLI]
   >> STRIP_TAC
   >> RW_TAC bool_ss []
   >> MATCH_MP_TAC ABS_EQ
   >> RW_TAC bool_ss []
   >> MP_TAC (Q.SPEC `e` POW_HALF_SMALL)
   >> RW_TAC bool_ss []
   >> MATCH_MP_TAC REAL_LET_TRANS
   >> Q.EXISTS_TAC `(1 / 2) pow n`
   >> RW_TAC bool_ss []
   >> NTAC 2 (POP_ASSUM K_TAC)
   >> NTAC 2 (POP_ASSUM MP_TAC)
   >> REWRITE_TAC [AND_IMP_INTRO]
   >> Q.SPEC_TAC (`p`, `p`)
   >> Induct_on `n`
   >- (RW_TAC bool_ss [pow, abs]
       >> Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`)
       >> Q.PAT_X_ASSUM `!p. P p` (MP_TAC o Q.SPEC `p`)
       >> REPEAT (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC)
   >> GEN_TAC
   >> MP_TAC (Q.SPEC `I o FST o prob_bernoulli p` (GSYM PROB_BERN_INTER_HALVES))
   >> impl_tac >- RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_BERNOULLI]
   >> Rewr'
   >> REPEAT DISCH_TAC
   >> Know `!x y : real. abs 2 * x <= 2 * y ==> x <= y`
   >- (SIMP_TAC arith_ss [abs, REAL_LE]
       >> REAL_ARITH_TAC)
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC bool_ss [GSYM ABS_MUL, pow, REAL_MUL_ASSOC, HALF_CANCEL,
                      REAL_MUL_LID, REAL_SUB_LDISTRIB]
   >> ONCE_REWRITE_TAC [PROB_BERNOULLI_ALT]
   >> Know
      `!f b.
         halfspace b INTER I o FST o BIND sdest (\b. f b) =
         halfspace b INTER (I o FST o f b) o stl`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_o, o_THM, IN_HALFSPACE, IN_INTER, GSPECIFICATION,
                         BIND_DEF, UNCURRY, sdest_def, IN_I]
       >> Cases_on `shd x`
       >> Cases_on `b`
       >> RW_TAC std_ss [])
   >> DISCH_THEN
      (fn th =>
       RW_TAC bool_ss [th, PROB_BERN_STL_HALFSPACE, INDEP_FN_PROB_BERNOULLI,
                       INDEP_FN_FST_EVENTS, INDEP_FN_UNIT]
       >> RW_TAC bool_ss [GSYM REAL_ADD_LDISTRIB, REAL_MUL_ASSOC,
                          REAL_MUL_LID, HALF_CANCEL]) >|
   [Know `(I o FST o UNIT F) = ({}:(num->bool)->bool)`
    >- (SET_EQ_TAC
        >> RW_TAC std_ss [NOT_IN_EMPTY, IN_o, o_THM, IN_I, UNIT_DEF])
    >> Rewr
    >> RW_TAC bool_ss [PROB_BERN_EMPTY, REAL_ADD_LID]
    >> Q.PAT_X_ASSUM `!p. P p` MATCH_MP_TAC
    >> CONJ_TAC >- (Q.PAT_X_ASSUM `0 <= p` MP_TAC >> REAL_ARITH_TAC)
    >> Suff `2 * p <= 2 * (1 / 2)` >- RW_TAC std_ss [HALF_CANCEL]
    >> RW_TAC arith_ss [REAL_LE_LMUL, REAL_LT],
    Know `(I o FST o UNIT T) = (UNIV:(num->bool)->bool)`
    >- (SET_EQ_TAC
        >> RW_TAC std_ss [IN_UNIV, IN_o, o_THM, IN_I, UNIT_DEF])
    >> Rewr
    >> RW_TAC bool_ss [PROB_BERN_UNIV]
    >> Know `!x y : real. (x + 1) - y = x - (y - 1)` >- REAL_ARITH_TAC
    >> Rewr'
    >> Q.PAT_X_ASSUM `!p. P p` MATCH_MP_TAC
    >> REVERSE CONJ_TAC >- (Q.PAT_X_ASSUM `p <= 1` MP_TAC >> REAL_ARITH_TAC)
    >> Suff `~(2 * p <= 1)` >- REAL_ARITH_TAC
    >> STRIP_TAC
    >> Q.PAT_X_ASSUM `~x` MP_TAC
    >> RW_TAC std_ss []
    >> Know `2 * p <= 2 * (1 / 2)` >- RW_TAC std_ss [HALF_CANCEL]
    >> RW_TAC arith_ss [REAL_LE_LMUL, REAL_LT]]);

val _ = export_theory ();
