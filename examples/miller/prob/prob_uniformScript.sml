open HolKernel Parse boolLib bossLib;

open arithmeticTheory pred_setTheory
     listTheory sequenceTheory state_transformerTheory
     hurdUtils extra_numTheory combinTheory
     pairTheory realTheory realLib extra_boolTheory
     extra_pred_setTheory extra_realTheory extra_pred_setTools numTheory
     simpLib;

open util_probTheory real_measureTheory real_probabilityTheory;
open prob_algebraTheory probTheory;

val _ = new_theory "prob_uniform";
val _ = ParseExtras.temp_loose_equality()

val std_ss' = std_ss ++ boolSimps.ETA_ss;

(* ------------------------------------------------------------------------- *)
(* The definition of the uniform random number generator.                    *)
(* ------------------------------------------------------------------------- *)

val (prob_unif_def, prob_unif_ind) = Defn.tprove
  let val d = Hol_defn "prob_unif"
        `(prob_unif 0 s = (0:num, s))
         /\ (prob_unif n s = let (m, s') = prob_unif (n DIV 2) s
                        in (if shd s' then 2 * m + 1 else 2 * m, stl s'))`
      val g = `measure (\(x,y). x)`
  in (d, WF_REL_TAC g >> STRIP_TAC)
  end;

val _ = save_thm ("prob_unif_def", prob_unif_def);
val _ = save_thm ("prob_unif_ind", prob_unif_ind);

val prob_uniform_cut_def = Define
  `(prob_uniform_cut 0 (SUC n) s = (0, s)) /\
   (prob_uniform_cut (SUC t) (SUC n) s =
    let (res, s') = prob_unif n s
    in if res < SUC n then (res, s') else prob_uniform_cut t (SUC n) s')`;

val prob_uniform_def = Define
  `prob_uniform (SUC n) = prob_until (prob_unif n) (\x. x < SUC n)`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* k < n ==>                                                                 *)
(* abs (prob (\s. FST (prob_uniform_cut t n s) = k) - 1 / & n) <=            *)
(* (1 / 2) pow t                                                             *)
(* ------------------------------------------------------------------------- *)

val PROB_UNIF_MONAD = store_thm
  ("PROB_UNIF_MONAD",
   ``(prob_unif 0 = UNIT 0) /\
     (!n.
        prob_unif (SUC n) =
        BIND (prob_unif (SUC n DIV 2))
        (\m. BIND sdest (\b. UNIT (if b then 2 * m + 1 else 2 * m))))``,
   FUN_EQ_TAC
   >> RW_TAC arith_ss [BIND_DEF, UNIT_DEF, o_THM, prob_unif_def, sdest_def,
                       LET_DEF, UNCURRY, FST, SND]);

val PROB_UNIFORM_CUT_MONAD = store_thm
  ("PROB_UNIFORM_CUT_MONAD",
   ``(!n. prob_uniform_cut 0 (SUC n) = UNIT 0) /\
     (!t n.
        prob_uniform_cut (SUC t) (SUC n) =
        BIND (prob_unif n)
        (\m. if m < SUC n then UNIT m else prob_uniform_cut t (SUC n)))``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [BIND_DEF, UNIT_DEF, o_DEF, prob_uniform_cut_def,
                     sdest_def, LET_DEF, UNCURRY]);

val INDEP_FN_PROB_UNIF = store_thm
  ("INDEP_FN_PROB_UNIF",
   ``!n. prob_unif n IN indep_fn``,
   recInduct log2_ind
   >> RW_TAC std_ss [PROB_UNIF_MONAD, INDEP_FN_UNIT]
   >> MATCH_MP_TAC INDEP_FN_BIND
   >> RW_TAC std_ss []
   >> MATCH_MP_TAC INDEP_FN_BIND
   >> RW_TAC std_ss [INDEP_FN_UNIT, INDEP_FN_SDEST]);

val INDEP_FN_PROB_UNIFORM_CUT = store_thm
  ("INDEP_FN_PROB_UNIFORM_CUT",
   ``!t n. prob_uniform_cut t (SUC n) IN indep_fn``,
   Induct >- RW_TAC std_ss [PROB_UNIFORM_CUT_MONAD, INDEP_FN_UNIT]
   >> RW_TAC std_ss [PROB_UNIFORM_CUT_MONAD]
   >> MATCH_MP_TAC INDEP_FN_BIND
   >> RW_TAC std_ss [INDEP_FN_PROB_UNIF, INDEP_FN_UNIT]);

val PROB_BERN_UNIF = store_thm
  ("PROB_BERN_UNIF",
   ``!n k.
       prob bern {s | FST (prob_unif n s) = k} =
       if k < 2 EXP log2 n then (1 / 2) pow log2 n else 0``,
   recInduct log2_ind
   >> REPEAT STRIP_TAC
   >- (Know `(0 = k) = k < 1` >- DECIDE_TAC
       >> RW_TAC std_ss [prob_unif_def, log2_def, EXP, pow, GEMPTY, GUNIV,
                         PROB_BERN_BASIC])
   >> Suff
      `prob bern {s | FST (prob_unif (SUC v) s) = k} =
       (1 / 2) * prob bern {s | FST (prob_unif (SUC v DIV 2) s) = k DIV 2}`
   >- (STRIP_TAC
       >> ASM_REWRITE_TAC []
       >> KILL_TAC
       >> RW_TAC std_ss [log2_def, pow, DIV_TWO_EXP]
       >> RW_TAC real_ss [])
   >> KILL_TAC
   >> RW_TAC bool_ss [prob_unif_def]
   >> Know
      `!s.
         prob_unif (SUC v DIV 2) s =
         (FST (prob_unif (SUC v DIV 2) s), SND (prob_unif (SUC v DIV 2) s))`
   >- RW_TAC bool_ss [PAIR]
   >> Rewr'
   >> RW_TAC bool_ss []
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   >> RW_TAC bool_ss [COND_RAND, COND_EXPAND]
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   >> RW_TAC bool_ss [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR]
   >> Know `!x. ~x /\ x = F` >- PROVE_TAC []
   >> Rewr
   >> Know `!m n : num. (m + 1 = n) /\ (m = n) = F` >- DECIDE_TAC
   >> Rewr
   >> RW_TAC bool_ss []
   >> MP_TAC (Q.SPEC `k` EVEN_ODD_EXISTS_EQ)
   >> MP_TAC (Q.SPEC `k` EVEN_OR_ODD)
   >> (STRIP_TAC >> RW_TAC bool_ss [] >> RW_TAC bool_ss [DIV_TWO_CANCEL]) >|
   [Know `!k. ~(2 * k + 1 = 2 * m)`
    >- (STRIP_TAC
        >> Suff `~(SUC (2 * k) = 2 * m)` >- DECIDE_TAC
        >> PROVE_TAC [EVEN_DOUBLE, ODD_DOUBLE, EVEN_ODD])
    >> Rewr
    >> Know `!a b : num. (2 * a = 2 * b) = (a = b)` >- DECIDE_TAC
    >> Rewr
    >> KILL_TAC
    >> Q.SPEC_TAC (`SUC v DIV 2`, `n`)
    >> STRIP_TAC
    >> Suff
       `prob bern
        (($= m o FST o prob_unif n) INTER halfspace F o SND o prob_unif n) =
        1 / 2 * prob bern {s | FST (prob_unif n s) = m}`
    >- (DISCH_THEN (MP_TAC o SYM)
        >> Rewr
        >> RW_TAC std_ss []
        >> AP_TERM_TAC
        >> ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC bool_ss [IN_INTER, IN_o, IN_HALFSPACE, o_THM, GSPECIFICATION]
        >> RW_TAC std_ss [SPECIFICATION]
        >> METIS_TAC [PAIR, FST, SND])
    >> MP_TAC (Q.SPECL [`prob_unif n`, `$= m`, `halfspace F`]
               (INST_TYPE [alpha |-> numSyntax.num] INDEP_FN_PROB))
    >> RW_TAC bool_ss [INDEP_FN_PROB_UNIF, EVENTS_BERN_BASIC, PROB_BERN_BASIC]
    >> RW_TAC real_ss []
    >> KILL_TAC
    >> Suff `$= m o FST o prob_unif n = {s | FST (prob_unif n s) = m}`
    >- METIS_TAC [REAL_MUL_COMM]
    >> SET_EQ_TAC
    >> RW_TAC std_ss [GSPECIFICATION]
    >> RW_TAC std_ss [SPECIFICATION, o_THM]
    >> PROVE_TAC [],
    Know `!k. ~(2 * k = SUC (2 * m))`
    >- PROVE_TAC [EVEN_DOUBLE, ODD_DOUBLE, EVEN_ODD]
    >> Rewr
    >> Know `!a b. (2 * a + 1 = SUC (2 * b)) = (a = b)` >- DECIDE_TAC
    >> Rewr
    >> KILL_TAC
    >> Q.SPEC_TAC (`SUC v DIV 2`, `n`)
    >> STRIP_TAC
    >> Suff
       `prob bern
        (($= m o FST o prob_unif n) INTER halfspace T o SND o prob_unif n) =
        1 / 2 * prob bern {s | FST (prob_unif n s) = m}`
    >- (DISCH_THEN (MP_TAC o SYM)
        >> Rewr
        >> RW_TAC std_ss []
        >> AP_TERM_TAC
        >> ONCE_REWRITE_TAC [EXTENSION]
        >> RW_TAC bool_ss [IN_INTER, IN_o, IN_HALFSPACE, o_THM, GSPECIFICATION]
        >> RW_TAC std_ss [SPECIFICATION]
        >> METIS_TAC [PAIR, FST, SND])
    >> MP_TAC (Q.SPECL [`prob_unif n`, `$= m`, `halfspace T`]
               (INST_TYPE [alpha |-> numSyntax.num] INDEP_FN_PROB))
    >> RW_TAC std_ss [INDEP_FN_PROB_UNIF, EVENTS_BERN_BASIC, PROB_BERN_BASIC]
    >> RW_TAC real_ss []
    >> KILL_TAC
    >> Suff `$= m o FST o prob_unif n = {s | FST (prob_unif n s) = m}`
    >- METIS_TAC [REAL_MUL_COMM]
    >> SET_EQ_TAC
    >> RW_TAC std_ss [GSPECIFICATION]
    >> RW_TAC std_ss [SPECIFICATION, o_THM]
    >> PROVE_TAC []]);

val PROB_UNIF_RANGE = store_thm
  ("PROB_UNIF_RANGE",
   ``!n s. FST (prob_unif n s) < 2 EXP log2 n``,
   recInduct log2_ind
   >> RW_TAC arith_ss [prob_unif_def, log2_def, EXP]
   >> Q.PAT_X_ASSUM `!s. P s` (MP_TAC o Q.SPEC `s`)
   >> RW_TAC arith_ss []);

val PROB_BERN_UNIF_PAIR = store_thm
  ("PROB_BERN_UNIF_PAIR",
   ``!n k k'.
       (prob bern {s | FST (prob_unif n s) = k} =
        prob bern {s | FST (prob_unif n s) = k'}) =
       (k < 2 EXP log2 n = k' < 2 EXP log2 n)``,
   RW_TAC std_ss [PROB_BERN_UNIF]
   >> PROVE_TAC [POW_HALF_POS, REAL_LT_LE]);

val PROB_BERN_UNIF_LT = store_thm
  ("PROB_BERN_UNIF_LT",
   ``!n k.
       k <= 2 EXP log2 n ==>
       (prob bern {s | FST (prob_unif n s) < k} = &k * (1 / 2) pow log2 n)``,
   STRIP_TAC
   >> Induct
   >- (RW_TAC arith_ss [GEMPTY, PROB_BERN_BASIC]
       >> RW_TAC real_ss [])
   >> RW_TAC std_ss []
   >> Q.PAT_X_ASSUM `X ==> Y` MP_TAC
   >> impl_tac >- RW_TAC arith_ss []
   >> RW_TAC std_ss' [INDEP_FN_PROB_FST_SUC, INDEP_FN_PROB_UNIF]
   >> Know `k < 2 EXP log2 n` >- DECIDE_TAC
   >> POP_ASSUM (fn th => RW_TAC std_ss [th, o_DEF, PROB_BERN_UNIF])
   >> RW_TAC bool_ss [ADD1, REAL_ADD_RDISTRIB, GSYM REAL_ADD]
   >> RW_TAC real_ss []);

val PROB_BERN_UNIF_GOOD = store_thm
  ("PROB_BERN_UNIF_GOOD",
   ``!n. 1 / 2 <= prob bern {s | FST (prob_unif n s) < SUC n}``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`n`, `SUC n`] PROB_BERN_UNIF_LT)
   >> RW_TAC std_ss [LOG2_LOWER_SUC]
   >> KILL_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_INVINV_ALL]
   >> MATCH_MP_TAC REAL_LE_INV_LE
   >> Know `~(&(SUC n) = (0 :real)) /\ ~(((1 :real) / 2) pow log2 n = 0)`
   >- PROVE_TAC [POW_HALF_POS, REAL_INJ, REAL_LT_LE, NOT_SUC]
   >> RW_TAC std_ss [REAL_INV_MUL]
   >- (MATCH_MP_TAC REAL_LT_MUL
       >> CONJ_TAC >- PROVE_TAC [INV_SUC_POS, REAL_INV_1OVER]
       >> PROVE_TAC [POW_HALF_POS, REAL_INV_POS])
   >> RW_TAC std_ss [POW_HALF_EXP, REAL_INVINV_ALL, GSYM REAL_INV_1OVER]
   >> Know
      `!x y : real. (0:real) < &(SUC n) /\ &(SUC n) * x <= &(SUC n) * y ==> x <= y`
   >- PROVE_TAC [REAL_LE_LMUL]
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC arith_ss [REAL_LT, REAL_MUL_RINV, REAL_MUL_ASSOC, REAL_MUL_LID]
   >> RW_TAC std_ss [REAL_LE, REAL_MUL]
   >> Suff `SUC (2 * n) <= SUC n * 2`
   >- PROVE_TAC [LOG2_UPPER_SUC, LESS_EQ_TRANS]
   >> DECIDE_TAC);

val PROB_UNIFORM_CUT_RANGE = store_thm
  ("PROB_UNIFORM_CUT_RANGE",
   ``!t n s. FST (prob_uniform_cut t (SUC n) s) < SUC n``,
   Induct >- RW_TAC arith_ss [prob_uniform_cut_def]
   >> RW_TAC arith_ss [prob_uniform_cut_def]
   >> Cases_on `prob_unif n s`
   >> RW_TAC arith_ss []);

val PROB_BERN_UNIFORM_CUT_LOWER_BOUND = store_thm
  ("PROB_BERN_UNIFORM_CUT_LOWER_BOUND",
   ``!b.
       (!k.
          k < SUC n ==>
          prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k} < b) ==>
       !m.
         m < SUC n ==>
         prob bern
         {s | FST (prob_uniform_cut t (SUC n) s) < SUC m} < &(SUC m) * b``,
   NTAC 2 STRIP_TAC
   >> Induct
   >- (RW_TAC arith_ss []
       >> POP_ASSUM (MP_TAC o Q.SPEC `0`)
       >> Know `!m : num. m < 1 = (m = 0)` >- DECIDE_TAC
       >> Know `!n. 0 < SUC n` >- DECIDE_TAC
       >> RW_TAC std_ss [GSYM ONE]
       >> RW_TAC real_ss [])
   >> RW_TAC arith_ss []
   >> ASSUME_TAC (Q.SPECL [`t`, `n`] INDEP_FN_PROB_UNIFORM_CUT)
   >> Q.PAT_X_ASSUM `X ==> Y` MP_TAC
   >> RW_TAC arith_ss []
   >> MP_TAC
      (Q.SPECL [`prob_uniform_cut t (SUC n)`, `SUC m`] INDEP_FN_PROB_FST_SUC)
   >> ASM_REWRITE_TAC []
   >> Rewr
   >> Know `&(SUC (SUC m)) = &(SUC m) + (1 :real)`
   >- (RW_TAC arith_ss [REAL_ADD, REAL_INJ]
       >> DECIDE_TAC)
   >> Rewr
   >> RW_TAC std_ss [REAL_ADD_RDISTRIB]
   >> MATCH_MP_TAC REAL_LT_ADD2
   >> RW_TAC real_ss []);

val PROB_BERN_UNIFORM_CUT_UPPER_BOUND = store_thm
  ("PROB_BERN_UNIFORM_CUT_UPPER_BOUND",
   ``!b.
       (!k.
          k < SUC n ==>
          b < prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k}) ==>
       (!m.
          m < SUC n ==>
          &(SUC m) * b <
          prob bern {s | FST (prob_uniform_cut t (SUC n) s) < SUC m})``,
   NTAC 2 STRIP_TAC
   >> Induct
   >- (RW_TAC arith_ss []
       >> POP_ASSUM (MP_TAC o Q.SPEC `0`)
       >> Know `!m. m < SUC 0 = (m = 0)` >- DECIDE_TAC
       >> STRIP_TAC
       >> RW_TAC real_ss [DECIDE ``(x:num) < 1 = (x = 0)``])
   >> RW_TAC arith_ss []
   >> ASSUME_TAC (Q.SPECL [`t`, `n`] INDEP_FN_PROB_UNIFORM_CUT)
   >> Q.PAT_X_ASSUM `X ==> Y` MP_TAC
   >> RW_TAC arith_ss []
   >> MP_TAC (Q.SPECL [`prob_uniform_cut t (SUC n)`, `SUC m`]
              INDEP_FN_PROB_FST_SUC)
   >> ASM_REWRITE_TAC []
   >> RW_TAC std_ss []
   >> Know `&(SUC (SUC m)) = &(SUC m) + (1 :real)`
   >- (RW_TAC arith_ss [REAL_ADD,REAL_INJ] >> DECIDE_TAC)
   >> RW_TAC std_ss [REAL_ADD_RDISTRIB]
   >> MATCH_MP_TAC REAL_LT_ADD2
   >> RW_TAC real_ss []);

val PROB_BERN_UNIFORM_CUT_PAIR = store_thm
  ("PROB_BERN_UNIFORM_CUT_PAIR",
   ``!t n k k'.
       k < SUC n /\ k' < SUC n ==>
       abs
       (prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k} -
        prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k'}) <=
       (1 / 2) pow t``,
   RW_TAC std_ss []
   >> Induct_on `t`
   >- (RW_TAC bool_ss [prob_uniform_cut_def, pow]
       >> MATCH_MP_TAC ABS_UNIT_INTERVAL
       >> Cases_on `k`
       >> Cases_on `k'`
       >> RW_TAC std_ss [GEMPTY, GUNIV, PROB_BERN_BASIC]
       >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [prob_uniform_cut_def, LET_DEF]
   >> Know `!s. prob_unif n s = (FST (prob_unif n s), SND (prob_unif n s))`
   >- RW_TAC std_ss [PAIR]
   >> Rewr'
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   >> RW_TAC std_ss [COND_RAND, COND_EXPAND]
   >> (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   >> RW_TAC std_ss [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR]
   >> Know `!x. ~x /\ x = F` >- PROVE_TAC []
   >> Rewr
   >> Know `!m. (m = k) /\ (m < SUC n) = (m = k)` >- DECIDE_TAC
   >> Know `!m. (m = k') /\ (m < SUC n) = (m = k')` >- RW_TAC arith_ss []
   >> Know `!x y. x \/ (x /\ y) = x` >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> NTAC 3 (POP_ASSUM (K ALL_TAC))
   >> Know
      `{s |
        ~(FST (prob_unif n s) < SUC n) /\
        (FST (prob_uniform_cut t (SUC n) (SND (prob_unif n s))) = k) \/
        (FST (prob_unif n s) = k)} =
       (\m. ~(m < SUC n)) o FST o prob_unif n INTER
       (\m. m = k) o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n UNION
       (\m. m = k) o FST o prob_unif n`
   >- (PSET_TAC [o_DEF, EXTENSION]
       >> RW_TAC std_ss [SPECIFICATION, GSYM EXTENSION])
   >> Rewr
   >> Know
      `prob bern
       ((\m. ~(m < SUC n)) o FST o prob_unif n INTER
        (\m. m = k) o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n UNION
        (\m. m = k) o FST o prob_unif n) =
       prob bern
       ((\m. ~(m < SUC n)) o FST o prob_unif n INTER
        (\m. m = k) o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n) +
       prob bern ((\m. m = k) o FST o prob_unif n)`
   >- (MATCH_MP_TAC PROB_ADDITIVE
       >> ASSUME_TAC (Q.SPEC `n` INDEP_FN_PROB_UNIF)
       >> ASSUME_TAC (Q.SPECL [`t`, `n`] INDEP_FN_PROB_UNIFORM_CUT)
       >> RW_TAC std_ss [PROB_SPACE_BERN] >|
       [MATCH_MP_TAC EVENTS_INTER
        >> RW_TAC bool_ss [INDEP_FN_FST_EVENTS', PROB_SPACE_BERN,
                          INDEP_FN_SND_EVENTS', o_ASSOC],
        RW_TAC bool_ss [INDEP_FN_FST_EVENTS],
        RW_TAC bool_ss [IN_DISJOINT, IN_INTER, IN_o, o_THM]
        >> RW_TAC bool_ss [SPECIFICATION]
        >> PROVE_TAC []])
   >> Rewr
   >> Know
      `prob bern
       ((\m. ~(m < SUC n)) o FST o prob_unif n INTER
        (\m. m = k) o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n) =
       prob bern ((\m. ~(m < SUC n)) o FST o prob_unif n) *
       prob bern ((\m. m = k) o FST o prob_uniform_cut t (SUC n))`
   >- (MP_TAC (Q.ISPEC `prob_unif n` INDEP_FN_PROB)
       >> MP_TAC (Q.SPEC `n` INDEP_FN_PROB_UNIF)
       >> RW_TAC bool_ss [o_ASSOC]
       >> POP_ASSUM MATCH_MP_TAC
       >> RW_TAC bool_ss [INDEP_FN_FST_EVENTS', INDEP_FN_PROB_UNIFORM_CUT])
   >> Rewr
   >> Know
      `{s |
        ~(FST (prob_unif n s) < SUC n) /\
        (FST (prob_uniform_cut t (SUC n) (SND (prob_unif n s))) = k') \/
        (FST (prob_unif n s) = k')} =
       (\m. ~(m < SUC n)) o FST o prob_unif n INTER
       (\m. m = k') o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n UNION
       (\m. m = k') o FST o prob_unif n`
   >- (PSET_TAC [o_DEF, EXTENSION]
       >> RW_TAC std_ss [SPECIFICATION, GSYM EXTENSION])
   >> Rewr
   >> Know
      `prob bern
       ((\m. ~(m < SUC n)) o FST o prob_unif n INTER
        (\m. m = k') o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n
        UNION (\m. m = k') o FST o prob_unif n) =
       prob bern
       ((\m. ~(m < SUC n)) o FST o prob_unif n INTER
        (\m. m = k') o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n) +
       prob bern ((\m. m = k') o FST o prob_unif n)`
   >- (MATCH_MP_TAC PROB_ADDITIVE
       >> ASSUME_TAC (Q.SPEC `n` INDEP_FN_PROB_UNIF)
       >> ASSUME_TAC (Q.SPECL [`t`, `n`] INDEP_FN_PROB_UNIFORM_CUT)
       >> RW_TAC bool_ss [PROB_SPACE_BERN] >|
       [MATCH_MP_TAC EVENTS_INTER
        >> RW_TAC bool_ss [INDEP_FN_FST_EVENTS', PROB_SPACE_BERN,
                          INDEP_FN_SND_EVENTS', o_ASSOC],
        RW_TAC bool_ss [INDEP_FN_FST_EVENTS],
        RW_TAC bool_ss [IN_DISJOINT, IN_INTER, IN_o, o_THM]
        >> RW_TAC bool_ss [SPECIFICATION]
        >> PROVE_TAC []])
   >> Rewr
   >> Know
      `prob bern
       ((\m. ~(m < SUC n)) o FST o prob_unif n INTER
        (\m. m = k') o FST o prob_uniform_cut t (SUC n) o SND o prob_unif n) =
       prob bern ((\m. ~(m < SUC n)) o FST o prob_unif n) *
       prob bern ((\m. m = k') o FST o prob_uniform_cut t (SUC n))`
   >- (MP_TAC (Q.ISPEC `prob_unif n` INDEP_FN_PROB)
       >> MP_TAC (Q.SPEC `n` INDEP_FN_PROB_UNIF)
       >> RW_TAC bool_ss [o_ASSOC]
       >> POP_ASSUM MATCH_MP_TAC
       >> RW_TAC bool_ss [INDEP_FN_FST_EVENTS', INDEP_FN_PROB_UNIFORM_CUT])
   >> Rewr
   >> Know
      `prob bern ((\m. m = k) o FST o prob_unif n) =
       prob bern ((\m. m = k') o FST o prob_unif n)`
   >- (Know
       `!k. ((\m. m = k) o FST o prob_unif n) = {s | FST (prob_unif n s) = k}`
       >- (PSET_TAC [EXTENSION]
           >> RW_TAC bool_ss [o_THM, SPECIFICATION, GSYM EXTENSION])
       >> Rewr
       >> RW_TAC bool_ss [o_DEF, Q.SPECL [`n`, `k`, `k'`] PROB_BERN_UNIF_PAIR]
       >> MP_TAC (Q.SPEC `n` LOG2_LOWER)
       >> DECIDE_TAC)
   >> Rewr
   >> RW_TAC bool_ss [REAL_ADD2_SUB2, REAL_SUB_REFL, REAL_ADD_RID]
   >> RW_TAC bool_ss [GSYM REAL_SUB_LDISTRIB, ABS_MUL, pow]
   >> MATCH_MP_TAC REAL_LE_MUL2
   >> reverse (RW_TAC bool_ss [ABS_POS])
   >- (POP_ASSUM MP_TAC
       >> RW_TAC bool_ss [o_DEF, GSPEC_DEST])
   >> KILL_TAC
   >> RW_TAC bool_ss [ABS_PROB, PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                     INDEP_FN_PROB_UNIF]
   >> Know
      `(\m. ~(m < SUC n)) o FST o prob_unif n =
       COMPL ((\m. m < SUC n) o FST o prob_unif n)`
   >- (PSET_TAC [o_DEF, EXTENSION]
       >> RW_TAC bool_ss [SPECIFICATION])
   >> Rewr
   >> ASSUME_TAC (Q.ISPECL [`bern`, `(\m. m < SUC n) o FST o prob_unif n`, `(1 :real) / 2`]
                           PROB_COMPL_LE1)
   >> POP_ASSUM (MP_TAC o (REWRITE_RULE [PROB_SPACE_BERN, SPACE_BERN_UNIV, GSYM COMPL_DEF]))
   >> MP_TAC (Q.ISPEC `prob_unif n` INDEP_FN_FST_EVENTS)
   >> RW_TAC bool_ss [INDEP_FN_PROB_UNIF, o_ASSOC, PROB_SPACE_BERN]
   >> KILL_TAC
   >> MP_TAC (Q.SPEC `n` PROB_BERN_UNIF_GOOD)
   >> RW_TAC real_ss [o_DEF, GSPEC_DEST]
   >> RW_TAC bool_ss [ONE_MINUS_HALF]);

val PROB_BERN_UNIFORM_CUT_SUC = store_thm
  ("PROB_BERN_UNIFORM_CUT_SUC",
   ``!t n k.
       k < SUC n ==>
       abs
       (prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k} - 1 / & (SUC n))
       <= (1 / 2) pow t``,
   RW_TAC bool_ss [GSYM ABS_BETWEEN_LE]
   >> REWRITE_TAC [real_lte] >| (* 3 sub-goals here *)
  [ (* goal 1 (of 3) *)
    PROVE_TAC [POW_HALF_POS, REAL_LT_LE, real_lte],
    (* goal 2 (of 3) *)
    STRIP_TAC
    >> Know
       `!k.
          k < SUC n ==>
          prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k} <
          1 / & (SUC n)`
    >- (RW_TAC bool_ss [real_lt]
        >> STRIP_TAC
        >> Know
           `(1 / 2) pow t <
            prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k'} -
            prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k}`
        >- (Q.PAT_X_ASSUM `x < y - z` MP_TAC
            >> RW_TAC bool_ss [GSYM REAL_LT_ADD_SUB]
            >> PROVE_TAC [REAL_ADD_SYM, REAL_LTE_TRANS])
        >> STRIP_TAC
        >> MP_TAC (Q.SPECL [`t`, `n`, `k'`, `k`] PROB_BERN_UNIFORM_CUT_PAIR)
        >> RW_TAC bool_ss [GSYM real_lt, abs]
        >> Suff `F` >- PROVE_TAC []
        >> POP_ASSUM MP_TAC
        >> RW_TAC bool_ss []
        >> PROVE_TAC [POW_HALF_POS, REAL_LT_TRANS, REAL_LT_LE])
    >> STRIP_TAC
    >> Suff `prob bern {s | FST (prob_uniform_cut t (SUC n) s) < SUC n} < 1`
    >- RW_TAC bool_ss [PROB_UNIFORM_CUT_RANGE, GUNIV, PROB_BERN_BASIC,
                      REAL_LT_REFL]
    >> MP_TAC (Q.SPEC `1 / &(SUC n)` PROB_BERN_UNIFORM_CUT_LOWER_BOUND)
    >> ASM_REWRITE_TAC []
    >> DISCH_THEN (MP_TAC o Q.SPEC `n`)
    >> Know `~(& (SUC n) = (0 :real))` >- RW_TAC arith_ss [REAL_INJ]
    >> RW_TAC arith_ss [GSYM REAL_INV_1OVER, REAL_MUL_RINV],
    (* goal 3 (of 3) *)
    STRIP_TAC
    >> Know
       `!k.
          k < SUC n ==>
          1 / & (SUC n) <
          prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k}`
    >- (RW_TAC bool_ss [real_lt]
        >> STRIP_TAC
        >> Know
           `(1 / 2) pow t <
            prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k} -
            prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k'}`
        >- (RW_TAC bool_ss [GSYM REAL_LT_ADD_SUB]
            >> ONCE_REWRITE_TAC [REAL_ADD_SYM]
            >> MP_TAC
               (Q.SPECL
                [`prob bern {s | FST (prob_uniform_cut t (SUC n) s) = k'}`,
                 `1 / & (SUC n)`, `(1 / 2) pow t`]
                REAL_LE_RADD)
            >> RW_TAC bool_ss []
            >> PROVE_TAC [REAL_ADD_SYM, REAL_LET_TRANS])
        >> STRIP_TAC
        >> MP_TAC (Q.SPECL [`t`, `n`, `k`, `k'`] PROB_BERN_UNIFORM_CUT_PAIR)
        >> RW_TAC bool_ss [GSYM real_lt, abs]
        >> Suff `F` >- PROVE_TAC []
        >> POP_ASSUM MP_TAC
        >> RW_TAC bool_ss []
        >> PROVE_TAC [POW_HALF_POS, REAL_LT_TRANS, REAL_LT_LE])
    >> STRIP_TAC
    >> Suff `1 < prob bern {s | FST (prob_uniform_cut t (SUC n) s) < SUC n}`
    >- RW_TAC bool_ss [PROB_UNIFORM_CUT_RANGE, GUNIV, PROB_BERN_BASIC,
                      REAL_LT_REFL]
    >> MP_TAC (Q.SPEC `1 / &(SUC n)` PROB_BERN_UNIFORM_CUT_UPPER_BOUND)
    >> ASM_REWRITE_TAC []
    >> DISCH_THEN (MP_TAC o Q.SPEC `n`)
    >> Know `~(& (SUC n) = (0 :real))` >- RW_TAC arith_ss [REAL_INJ]
    >> RW_TAC arith_ss [GSYM REAL_INV_1OVER, REAL_MUL_RINV]]);

val PROB_BERN_UNIFORM_CUT = store_thm
  ("PROB_BERN_UNIFORM_CUT",
   ``!t n k.
       k < n ==>
       abs (prob bern {s | FST (prob_uniform_cut t n s) = k} - 1 / &n) <=
       (1 / 2) pow t``,
   NTAC 3 STRIP_TAC
   >> Cases_on `n` >- RW_TAC arith_ss []
   >> RW_TAC bool_ss [PROB_BERN_UNIFORM_CUT_SUC]);

val PROB_PROB_UNIFORM_CUT_LOWER_SUC = store_thm
  ("PROB_PROB_UNIFORM_CUT_LOWER_SUC",
   ``!t n k.
       k < n /\ 2 * log2 (n + 1) <= t ==>
       1 / (&n + 1) <= prob bern {s | FST (prob_uniform_cut t n s) = k}``,
   REPEAT STRIP_TAC
   >> MP_TAC (Q.SPECL [`t`, `n`, `k`] PROB_BERN_UNIFORM_CUT)
   >> ASM_REWRITE_TAC [GSYM ABS_BETWEEN_LE]
   >> REPEAT STRIP_TAC
   >> POP_ASSUM K_TAC
   >> Suff `((1 :real) / 2) pow t <= 1 / &n - 1 / (&n + 1)`
   >- (POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> POP_ASSUM K_TAC
   >> Know `0 < n` >- DECIDE_TAC
   >> PROVE_TAC [LOG2_SUC]);

val PROB_BERN_UNIFORM_CUT_CARD_LOWER = store_thm
  ("PROB_BERN_UNIFORM_CUT_CARD_LOWER",
   ``!t n a.
       0 < n /\ a SUBSET count n ==>
       &(CARD a) * (1 / &n - (1 / 2) pow t) <=
       prob bern {s | FST (prob_uniform_cut t n s) IN a}``,
   REPEAT STRIP_TAC
   >> Know `FINITE a`
   >- PROVE_TAC [FINITE_COUNT, SUBSET_FINITE]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `a SUBSET x` MP_TAC
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`a`, `a`)
   >> HO_MATCH_MP_TAC FINITE_INDUCT
   >> CONJ_TAC
   >- RW_TAC real_ss [CARD_EMPTY, PROB_BERN_BASIC, NOT_IN_EMPTY, GEMPTY,
                      REAL_LE_REFL]
   >> POP_ASSUM MP_TAC
   >> Cases_on `n` >- RW_TAC std_ss []
   >> MP_TAC (Q.ISPEC `prob_uniform_cut t (SUC n')` INDEP_FN_PROB_FST_INSERT)
   >> RW_TAC std_ss [INDEP_FN_PROB_UNIFORM_CUT]
   >> RW_TAC bool_ss [CARD_INSERT, ADD1, GSYM REAL_ADD, REAL_RDISTRIB]
   >> Know `!a b c d : real. a <= d /\ b <= c ==> a + b <= c + d`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC bool_ss [GSYM ADD1, REAL_ADD]
   >- (Q.PAT_X_ASSUM `x ==> y` MATCH_MP_TAC
       >> POP_ASSUM MP_TAC
       >> RW_TAC bool_ss [SUBSET_DEF, IN_INSERT])
   >> Suff
      `abs
       (prob bern {s | FST (prob_uniform_cut t (SUC n') s) = e} - 1 / &(SUC n'))
       <= (1 / 2) pow t`
   >- RW_TAC bool_ss [REAL_MUL_LID, GSYM ABS_BETWEEN_LE]
   >> MATCH_MP_TAC PROB_BERN_UNIFORM_CUT
   >> Suff `e IN count (SUC n')` >- RW_TAC bool_ss [SPECIFICATION, IN_COUNT]
   >> PROVE_TAC [IN_INSERT, SUBSET_DEF]);

val PROB_BERN_UNIFORM_CUT_CARD_LOWER_SUC = store_thm
  ("PROB_BERN_UNIFORM_CUT_CARD_LOWER_SUC",
   ``!t n a.
       0 < n /\ a SUBSET count n /\ 2 * log2 (n + 1) <= t ==>
       &(CARD a) * (1 / &(n + 1)) <=
       prob bern {s | FST (prob_uniform_cut t n s) IN a}``,
   REPEAT STRIP_TAC
   >> Cases_on `a = {}`
   >- RW_TAC real_ss [CARD_EMPTY, PROB_BERN_BASIC, NOT_IN_EMPTY, GEMPTY,
                      REAL_LE_REFL]
   >> MP_TAC (Q.SPECL [`t`, `n`, `a`] PROB_BERN_UNIFORM_CUT_CARD_LOWER)
   >> MP_TAC (Q.SPECL [`n`, `t`] LOG2_SUC)
   >> ASM_REWRITE_TAC []
   >> MP_TAC (Q.SPEC `&(CARD (a : num -> bool))` REAL_MULT_LE_CANCEL)
   >> Know `FINITE (a : num -> bool)`
   >- PROVE_TAC [FINITE_COUNT, SUBSET_FINITE]
   >> STRIP_TAC
   >> Know `(0 :real) < &(CARD (a : num -> bool))`
   >- (MATCH_MP_TAC REAL_NZ_IMP_LT
       >> RW_TAC bool_ss [REAL_INJ, CARD_EQ_0])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Q.SPEC_TAC (`(1 / 2) pow t`, `x`)
   >> Q.SPEC_TAC
      (`inv (&(CARD a)) * prob bern {s | FST (prob_uniform_cut t n s) IN a}`,
       `y`)
   >> KILL_TAC
   >> REWRITE_TAC [REAL_ADD]
   >> REAL_ARITH_TAC);

val PROB_UNIFORM_TERMINATES = store_thm
  ("PROB_UNIFORM_TERMINATES",
   ``!n. ?*s. FST (prob_unif n s) < SUC n``,
   RW_TAC bool_ss [possibly_bern_def, possibly_def]
   >- (Suff
       `{s | FST (prob_unif n s) < SUC n} = {x | x < SUC n} o FST o prob_unif n`
       >- RW_TAC bool_ss [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_UNIF]
       >> SET_EQ_TAC
       >> PSET_TAC [o_THM])
   >> MP_TAC (Q.SPECL [`n`, `SUC n`] PROB_BERN_UNIF_LT)
   >> impl_tac >- RW_TAC bool_ss [LOG2_LOWER_SUC]
   >> Rewr
   >> RW_TAC bool_ss [REAL_ENTIRE, REAL_INJ]
   >> PROVE_TAC [POW_HALF_POS, REAL_LT_LE]);

val INDEP_FN_PROB_UNIFORM = store_thm
  ("INDEP_FN_PROB_UNIFORM",
   ``!n. prob_uniform (SUC n) IN indep_fn``,
   RW_TAC bool_ss [prob_uniform_def, INDEP_FN_PROB_UNTIL, INDEP_FN_PROB_UNIF,
                  PROB_UNIFORM_TERMINATES]);

val PROB_BERN_UNIFORM = store_thm
  ("PROB_BERN_UNIFORM",
   ``!n k. k < n ==> (prob bern {s | FST (prob_uniform n s) = k} = 1 / &n)``,
   Cases >- RW_TAC arith_ss []
   >> RW_TAC bool_ss [prob_uniform_def]
   >> (MP_TAC o
       Q.SPECL [`{k}`, `prob_unif n'`, `\x. x < SUC n'`] o
       INST_TYPE [alpha |-> ``:num``])
      PROB_BERN_UNTIL
   >> impl_tac >- RW_TAC bool_ss [INDEP_FN_PROB_UNIF, PROB_UNIFORM_TERMINATES]
   >> Know
      `{k} o FST o prob_until (prob_unif n') (\x. x < SUC n') =
       {s | FST (prob_until (prob_unif n') (\x. x < SUC n') s) = k}`
   >- (SET_EQ_TAC
       >> PSET_TAC [o_THM])
   >> Rewr
   >> Rewr
   >> Know
      `({k} INTER {x | (\x. x < SUC n') x}) o FST o prob_unif n' =
       {s | FST (prob_unif n' s) = k}`
   >- (SET_EQ_TAC
       >> PSET_TAC [o_THM]
       >> RW_TAC arith_ss [])
   >> Rewr
   >> Know
      `{x | (\x. x < SUC n') x} o FST o prob_unif n' =
       {s | FST (prob_unif n' s) < SUC n'}`
   >- (SET_EQ_TAC
       >> PSET_TAC [o_THM])
   >> Rewr
   >> MP_TAC (Q.SPECL [`n'`, `SUC n'`] PROB_BERN_UNIF_LT)
   >> MP_TAC (Q.SPEC `n'` LOG2_LOWER_SUC)
   >> STRIP_TAC
   >> ASM_REWRITE_TAC []
   >> Rewr
   >> MP_TAC (Q.SPECL [`n'`, `k`] PROB_BERN_UNIF)
   >> RW_TAC arith_ss []
   >> MATCH_MP_TAC REAL_DIV_EQ
   >> RW_TAC bool_ss [REAL_ENTIRE, REAL_INJ, REAL_MUL_LID]
   >- PROVE_TAC [POW_HALF_POS, REAL_LT_LE]
   >> RW_TAC bool_ss [REAL_MUL_SYM]);

val PROB_UNIFORM_RANGE = store_thm
  ("PROB_UNIFORM_RANGE",
   ``!n. !*s. FST (prob_uniform (SUC n) s) < SUC n``,
   RW_TAC bool_ss [prob_uniform_def]
   >> MP_TAC (Q.ISPECL [`prob_unif n`, `\x. x < SUC n`] PROB_UNTIL_POST)
   >> RW_TAC bool_ss [PROB_UNIFORM_TERMINATES, INDEP_FN_PROB_UNIF]);

val _ = export_theory ();
