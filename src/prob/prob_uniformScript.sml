open HolKernel Parse boolLib bossLib arithmeticTheory numTheory
     realTheory seqTheory pred_setTheory listTheory rich_listTheory
     pairTheory combinTheory realLib probTools boolean_sequenceTheory
     boolean_sequenceTools prob_extraTheory prob_extraTools
     prob_canonTheory prob_canonTools prob_algebraTheory probTheory
     state_transformerTheory prob_indepTheory realSimps;

val _ = new_theory "prob_uniform";

infixr 0 ++ << || ORELSEC ##;
infix 1 >> |->;
nonfix THEN THENL ORELSE;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

local
  infix ++;
  open simpLib boolSimps
in
  val std_ss' =
    (bool_ss ++ pairSimps.PAIR_ss ++ optionSimps.OPTION_ss ++
     numSimps.REDUCE_ss ++ sumSimps.SUM_ss ++ ETA_ss ++ LET_ss)
  val arith_ss = arith_ss ++ LET_ss
end;

(* ------------------------------------------------------------------------- *)
(* The definition of the uniform random number generator.                    *)
(* ------------------------------------------------------------------------- *)

val (unif_bound_def, unif_bound_ind) = Defn.tprove
  let val d = Hol_defn "unif_bound"
        `(unif_bound 0 = 0)
         /\ (unif_bound n = SUC (unif_bound (n DIV 2)))`
      val g = `measure (\x. x)`
  in (d,
      WF_REL_TAC g
      ++ STRIP_TAC
      ++ KNOW_TAC `2 * (SUC v DIV 2) <= SUC v`
      >> PROVE_TAC [DECIDE ``2 = SUC 1``, DIV_THEN_MULT]
      ++ DECIDE_TAC)
  end;

val _ = save_thm ("unif_bound_def", unif_bound_def);
val _ = save_thm ("unif_bound_ind", unif_bound_ind);

val (unif_def, unif_ind) = Defn.tprove
  let val d = Hol_defn "unif"
        `(unif 0 s = (0:num, s))
         /\ (unif n s = let (m, s') = unif (n DIV 2) s
	                in (if SHD s' then 2 * m + 1 else 2 * m, STL s'))`
      val g = `measure (\(x,y). x)`
  in (d,
      WF_REL_TAC g
      ++ STRIP_TAC
      ++ KNOW_TAC `2 * (SUC v2 DIV 2) <= SUC v2`
      >> PROVE_TAC [DECIDE ``2 = SUC 1``, DIV_THEN_MULT]
      ++ DECIDE_TAC)
  end;

val _ = save_thm ("unif_def", unif_def);
val _ = save_thm ("unif_ind", unif_ind);

val uniform_def = Define `(uniform 0 (SUC n) s = (0, s))
  /\ (uniform (SUC t) (SUC n) s
      = let (res, s') = unif n s
        in if res < SUC n then (res, s') else uniform t (SUC n) s')`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. k < n ==>                                                              *)
(*    abs (prob (\s. FST (uniform t n s) = k) - 1 / & n) <= (1 / 2) pow t    *)
(* ------------------------------------------------------------------------- *)

val SUC_DIV_TWO_ZERO = store_thm
  ("SUC_DIV_TWO_ZERO",
   ``!n. (SUC n DIV 2 = 0) = (n = 0)``,
   RW_TAC std_ss' []
   ++ REVERSE EQ_TAC
   >> (MP_TAC DIV_TWO_BASIC
       ++ KNOW_TAC `SUC 0 = 1` >> DECIDE_TAC
       ++ RW_TAC arith_ss [])
   ++ RW_TAC std_ss' []
   ++ MP_TAC (Q.SPEC `SUC n` DIV_TWO)
   ++ RW_TAC arith_ss [MULT_CLAUSES, MOD_TWO]);

val UNIF_BOUND_LOWER = store_thm
  ("UNIF_BOUND_LOWER",
   ``!n. n < 2 EXP unif_bound n``,
   recInduct unif_bound_ind
   ++ RW_TAC arith_ss [unif_bound_def, EXP]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss' [DIV_TWO_EXP, EXP]);

val UNIF_BOUND_LOWER_SUC = store_thm
  ("UNIF_BOUND_LOWER_SUC",
   ``!n. SUC n <= 2 EXP unif_bound n``,
   RW_TAC std_ss' []
   ++ MP_TAC (Q.SPEC `n` UNIF_BOUND_LOWER)
   ++ DECIDE_TAC);

val UNIF_BOUND_UPPER = store_thm
  ("UNIF_BOUND_UPPER",
   ``!n. ~(n = 0) ==> 2 EXP unif_bound n <= 2 * n``,
   recInduct unif_bound_ind
   ++ RW_TAC arith_ss [unif_bound_def, EXP]
   ++ Cases_on `SUC v DIV 2 = 0`
   >> (POP_ASSUM MP_TAC
       ++ RW_TAC std_ss' [SUC_DIV_TWO_ZERO]
       ++ RW_TAC arith_ss [DECIDE ``SUC 0 = 1``, DIV_TWO_BASIC,
			   unif_bound_def, EXP])
   ++ RES_TAC
   ++ POP_ASSUM MP_TAC
   ++ KILL_ALL_TAC
   ++ Q.SPEC_TAC (`SUC v`, `n`)
   ++ GEN_TAC
   ++ Q.SPEC_TAC (`2 EXP unif_bound (n DIV 2)`, `m`)
   ++ GEN_TAC
   ++ SUFF_TAC `2 * (n DIV 2) <= n` >> DECIDE_TAC
   ++ MP_TAC (Q.SPEC `n` DIV_TWO)
   ++ DECIDE_TAC);

val UNIF_BOUND_UPPER_SUC = store_thm
  ("UNIF_BOUND_UPPER_SUC",
   ``!n. 2 EXP unif_bound n <= SUC (2 * n)``,
   STRIP_TAC
   ++ MP_TAC (Q.SPEC `n` UNIF_BOUND_UPPER)
   ++ REVERSE (Cases_on `n = 0`) >> RW_TAC arith_ss []
   ++ RW_TAC arith_ss [unif_bound_def, EXP]);

val UNIF_DEF_ALT = prove
  (``!n. unif n = if (n = 0) then \s. (0, s) else
       \s. let (m,s') = unif (n DIV 2) s
           in (if SHD s' then 2 * m + 1 else 2 * m, STL s')``,
   Cases
   ++ RW_TAC arith_ss [GSYM EQ_EXT_EQ, unif_def]);

val UNIF_DEF_MONAD = store_thm
  ("UNIF_DEF_MONAD",
   ``(unif 0 = UNIT (0:num))
     /\ (!n. unif (SUC n) = BIND (unif (SUC n DIV 2))
               (\m. BIND SDEST (\b. UNIT (if b then 2 * m + 1 else 2 * m))))``,
   RW_TAC arith_ss [BIND_DEF, UNIT_DEF, o_DEF, unif_def, SDEST_def, LET_DEF,
                    GSYM EQ_EXT_EQ]);

val UNIFORM_DEF_ALT = prove
  (``!t n. uniform t n = if (n = 0) then uniform t 0 else
       if (t = 0) then \s. (0, s)
       else \s. let (res,s') = unif (n - 1) s in
         (if res < n then (res,s') else uniform (t - 1) n s')``,
   Cases
   ++ Cases
   ++ RW_TAC arith_ss [GSYM EQ_EXT_EQ, uniform_def]);

val UNIFORM_DEF_MONAD = store_thm
  ("UNIFORM_DEF_MONAD",
   ``(!n. uniform 0 (SUC n) = UNIT (0:num))
     /\ (!t n. uniform (SUC t) (SUC n) = BIND (unif n)
                 (\m. if m < SUC n then UNIT m else uniform t (SUC n)))``,
   ONCE_REWRITE_TAC [GSYM EQ_EXT_EQ]
   ++ RW_TAC std_ss' [BIND_DEF, UNIT_DEF, o_DEF, uniform_def, SDEST_def, LET_DEF]
   ++ Cases_on `unif n x`
   ++ RW_TAC std_ss' []);

val INDEP_UNIF = store_thm
  ("INDEP_UNIF",
   ``!n. indep (unif n)``,
   recInduct unif_bound_ind
   ++ RW_TAC std_ss' [UNIF_DEF_MONAD, INDEP_UNIT]
   ++ MATCH_MP_TAC INDEP_BIND
   ++ RW_TAC std_ss' []
   ++ MATCH_MP_TAC INDEP_BIND_SDEST
   ++ RW_TAC std_ss' [INDEP_UNIT]);

val INDEP_UNIFORM = store_thm
  ("INDEP_UNIFORM",
   ``!t n. indep (uniform t (SUC n))``,
   Induct >> RW_TAC std_ss' [UNIFORM_DEF_MONAD, INDEP_UNIT]
   ++ RW_TAC std_ss' [UNIFORM_DEF_MONAD]
   ++ MATCH_MP_TAC INDEP_BIND
   ++ RW_TAC std_ss' [INDEP_UNIF, INDEP_UNIT]);

val PROB_UNIF = store_thm
  ("PROB_UNIF",
   ``!n k. prob (\s. FST (unif n s) = k)
           = if k < 2 EXP unif_bound n then (1 / 2) pow unif_bound n else 0``,
   recInduct unif_bound_ind
   ++ REPEAT STRIP_TAC
   >> (KNOW_TAC `(0 = k) = k < 1` >> DECIDE_TAC
       ++ RW_TAC std_ss' [unif_def, unif_bound_def, EXP, pow, GSYM EMPTY_DEF,
                         GSYM UNIV_DEF, PROB_BASIC])
   ++ SUFF_TAC `prob (\s. FST (unif (SUC v) s) = k)
                = 1 / 2 * prob (\s. FST (unif (SUC v DIV 2) s) = k DIV 2)`
   >> (STRIP_TAC
       ++ ASM_REWRITE_TAC []
       ++ KILL_ALL_TAC
       ++ RW_TAC std_ss' [unif_bound_def, pow, DIV_TWO_EXP]
       ++ RW_TAC real_ac_ss [])
   ++ KILL_ALL_TAC
   ++ RW_TAC std_ss' [unif_def]
   ++ KNOW_TAC `!s. unif (SUC v DIV 2) s
                  = (FST (unif (SUC v DIV 2) s), SND (unif (SUC v DIV 2) s))`
   >> RW_TAC std_ss' [PAIR]
   ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
   ++ RW_TAC std_ss' []
   ++ (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   ++ RW_TAC std_ss' [COND_RAND, COND_EXPAND]
   ++ (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   ++ RW_TAC std_ss' [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR]
   ++ RW_TAC std_ss' [PROVE [] ``~X /\ X = F``,
                     DECIDE ``((m:num) + 1 = n) /\ (m = n) = F``]
   ++ MP_TAC (Q.SPEC `k` EVEN_ODD_EXISTS_EQ)
   ++ MP_TAC (Q.SPEC `k` EVEN_OR_ODD)
   ++ (STRIP_TAC ++ RW_TAC std_ss' [] ++ RW_TAC std_ss' [DIV_TWO_CANCEL]) <<
   [KNOW_TAC `!k. ~(2 * k + 1 = 2 * m)`
    >> (STRIP_TAC
        ++ SUFF_TAC `~(SUC (2 * k) = 2 * m)` >> DECIDE_TAC
        ++ PROVE_TAC [EVEN_DOUBLE, ODD_DOUBLE, EVEN_ODD])
    ++ RW_TAC std_ss' [DECIDE ``(2:num * a = 2 * b) = (a = b)``]
    ++ KILL_ALL_TAC
    ++ Q.SPEC_TAC (`SUC v DIV 2`, `n`)
    ++ STRIP_TAC
    ++ SUFF_TAC `prob ($= m o FST o unif n
                       INTER (\s. SHD s = F) o SND o unif n)
                 =  1 / 2 * prob (\s. FST (unif n s) = m)`
    >> (DISCH_THEN (MP_TAC o SYM)
        ++ RW_TAC std_ss' []
        ++ MATCH_MP_TAC RAND_THM
        ++ PSET_TAC [o_DEF]
        ++ PROVE_TAC [])
    ++ MP_TAC (Q.SPECL [`unif n`, `$= m`, `\s. SHD s = F`]
               (INST_TYPE [alpha |-> numSyntax.num] INDEP_PROB))
    ++ RW_TAC std_ss' [INDEP_UNIF, MEASURABLE_BASIC]
    ++ KILL_ALL_TAC
    ++ MP_TAC (Q.SPEC `F` (CONJUNCT2 (CONJUNCT2 PROB_BASIC)))
    ++ RW_TAC real_ac_ss [o_DEF]
    ++ (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
    ++ RW_TAC std_ss' [],
    KNOW_TAC `!k. ~(2 * k = SUC (2 * m))`
    >> PROVE_TAC [EVEN_DOUBLE, ODD_DOUBLE, EVEN_ODD]
    ++ RW_TAC std_ss' [DECIDE ``(2 * a + 1 = SUC (2 * b)) = (a = b)``]
    ++ KILL_ALL_TAC
    ++ Q.SPEC_TAC (`SUC v DIV 2`, `n`)
    ++ STRIP_TAC
    ++ SUFF_TAC `prob ($= m o FST o unif n
                       INTER (\s. SHD s = T) o SND o unif n)
                 =  1 / 2 * prob (\s. FST (unif n s) = m)`
    >> (DISCH_THEN (MP_TAC o SYM)
        ++ RW_TAC std_ss' []
        ++ MATCH_MP_TAC RAND_THM
        ++ PSET_TAC [o_DEF]
        ++ PROVE_TAC [])
    ++ MP_TAC (Q.SPECL [`unif n`, `$= m`, `\s. SHD s = T`]
               (INST_TYPE [alpha |-> numSyntax.num] INDEP_PROB))
    ++ RW_TAC std_ss' [INDEP_UNIF, MEASURABLE_BASIC]
    ++ KILL_ALL_TAC
    ++ MP_TAC (Q.SPEC `T` (CONJUNCT2 (CONJUNCT2 PROB_BASIC)))
    ++ RW_TAC std_ss' [o_DEF]
    ++ (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
    ++ RW_TAC real_ac_ss []]);

val UNIF_RANGE = store_thm
  ("UNIF_RANGE",
   ``!n s. FST (unif n s) < 2 EXP unif_bound n``,
   recInduct unif_bound_ind
   ++ RW_TAC arith_ss [unif_def, unif_bound_def, EXP]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `s`)
   ++ Cases_on `unif (SUC v DIV 2) s`
   ++ RW_TAC arith_ss []);

val PROB_UNIF_PAIR = store_thm
  ("PROB_UNIF_PAIR",
   ``!n k k'. (prob (\s. FST (unif n s) = k) = prob (\s. FST (unif n s) = k'))
              = (k < 2 EXP unif_bound n = k' < 2 EXP unif_bound n)``,
   RW_TAC std_ss' [PROB_UNIF]
   ++ PROVE_TAC [POW_HALF_POS, REAL_LT_LE]);

val PROB_UNIF_BOUND = store_thm
  ("PROB_UNIF_BOUND",
   ``!n k. k <= 2 EXP unif_bound n
           ==> (prob (\s. FST (unif n s) < k)
		= &k * (1 / 2) pow unif_bound n)``,
   STRIP_TAC
   ++ Induct
   >> (RW_TAC arith_ss [GSYM EMPTY_DEF, PROB_BASIC]
       ++ RW_TAC real_ac_ss [])
   ++ RW_TAC std_ss' []
   ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
   ++ KNOW_TAC `k <= 2 EXP unif_bound n` >> RW_TAC arith_ss []
   ++ POP_ASSUM (fn th => RW_TAC std_ss' [th])
   ++ KNOW_TAC `(\s. FST (unif n s) < SUC k) =
                (\m. m < k) o FST o unif n UNION (\m. m = k) o FST o unif n`
   >> (PSET_TAC [o_DEF] ++ DECIDE_TAC)
   ++ POP_ASSUM (fn th => RW_TAC std_ss' [th])
   ++ KNOW_TAC `prob ((\m. m < k) o FST o unif n UNION
		      (\m. m = k) o FST o unif n)
		= prob ((\m. m < k) o FST o unif n)
		  + prob ((\m. m = k) o FST o unif n)`
   >> (MATCH_MP_TAC PROB_ADDITIVE
       ++ ASSUME_TAC (Q.SPEC `n` INDEP_UNIF)
       ++ RW_TAC std_ss' [INDEP_MEASURABLE1]
       ++ PSET_TAC [o_DEF]
       ++ DECIDE_TAC)
   ++ KNOW_TAC `k < 2 EXP unif_bound n` >> DECIDE_TAC
   ++ POP_ASSUM (fn th => RW_TAC std_ss' [th, o_DEF, PROB_UNIF])
   ++ KNOW_TAC `&(SUC k) = &k + 1`
   >> (RW_TAC real_ac_ss [REAL_ADD,REAL_INJ])
   ++ POP_ASSUM (fn th => RW_TAC std_ss' [th, REAL_ADD_RDISTRIB, REAL_MUL_LID]));

val PROB_UNIF_GOOD = store_thm
  ("PROB_UNIF_GOOD",
   ``!n. 1 / 2 <= prob (\s. FST (unif n s) < SUC n)``,
   RW_TAC std_ss' []
   ++ MP_TAC (Q.SPECL [`n`, `SUC n`] PROB_UNIF_BOUND)
   ++ RW_TAC std_ss' [UNIF_BOUND_LOWER_SUC]
   ++ KILL_ALL_TAC
   ++ ONCE_REWRITE_TAC [GSYM REAL_INVINV_ALL]
   ++ MATCH_MP_TAC REAL_LE_INV_LE
   ++ KNOW_TAC `~(&(SUC n) = 0) /\ ~((1/2) pow unif_bound n = 0)`
   >> PROVE_TAC [POW_HALF_POS, REAL_INJ, REAL_LT_LE, NOT_SUC]
   ++ RW_TAC std_ss' [REAL_INV_MUL]
   >> (MATCH_MP_TAC REAL_LT_MUL
       ++ CONJ_TAC >> PROVE_TAC [INV_SUC_POS, REAL_INV_1OVER]
       ++ PROVE_TAC [POW_HALF_POS, REAL_INV_POS])
   ++ RW_TAC std_ss' [POW_HALF_EXP, REAL_INVINV_ALL, GSYM REAL_INV_1OVER]
   ++ MATCH_MP_TAC (PROVE [REAL_LE_LMUL]
       ``0:real < &(SUC n) /\ &(SUC n):real * x <= &(SUC n) * y ==> x <= y``)
   ++ RW_TAC arith_ss [REAL_LT, REAL_MUL_RINV, REAL_MUL_ASSOC, REAL_MUL_LID]
   ++ RW_TAC std_ss' [REAL_LE, REAL_MUL]
   ++ SUFF_TAC `SUC (2 * n) <= SUC n * 2`
   >> PROVE_TAC [UNIF_BOUND_UPPER_SUC, LESS_EQ_TRANS]
   ++ DECIDE_TAC);

val UNIFORM_RANGE = store_thm
  ("UNIFORM_RANGE",
   ``!t n s. FST (uniform t (SUC n) s) < SUC n``,
   Induct >> RW_TAC arith_ss [uniform_def]
   ++ RW_TAC arith_ss [uniform_def]
   ++ Cases_on `unif n s`
   ++ RW_TAC arith_ss []);

val PROB_UNIFORM_LOWER_BOUND = store_thm
  ("PROB_UNIFORM_LOWER_BOUND",
   ``!b. (!k. k < SUC n ==> prob (\s. FST (uniform t (SUC n) s) = k) < b)
         ==> (!m. m < SUC n ==>
                prob (\s. FST (uniform t (SUC n) s) < SUC m) < &(SUC m) * b)``,
   NTAC 2 STRIP_TAC
   ++ Induct
   >> (RW_TAC arith_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
       ++ RW_TAC arith_ss [DECIDE ``!m. m < 1n = (m = 0)``]
       ++ RW_TAC real_ac_ss [])
   ++ RW_TAC arith_ss []
   ++ KNOW_TAC `indep (uniform t (SUC n))` >> RW_TAC std_ss' [INDEP_UNIFORM]
   ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
   ++ RW_TAC arith_ss []
   ++ MP_TAC (Q.SPECL [`uniform t (SUC n)`, `SUC m`] PROB_INDEP_BOUND)
   ++ ASM_REWRITE_TAC []
   ++ RW_TAC std_ss' []
   ++ KNOW_TAC `&(SUC (SUC m)) = &(SUC m) + 1`
   >> (RW_TAC arith_ss [REAL_ADD,REAL_INJ] ++ DECIDE_TAC)
   ++ RW_TAC std_ss' [REAL_ADD_RDISTRIB]
   ++ MATCH_MP_TAC REAL_LT_ADD2
   ++ RW_TAC real_ac_ss []);

val PROB_UNIFORM_UPPER_BOUND = store_thm
  ("PROB_UNIFORM_UPPER_BOUND",
   ``!b. (!k. k < SUC n ==> b < prob (\s. FST (uniform t (SUC n) s) = k))
         ==> (!m. m < SUC n ==>
                &(SUC m) * b < prob (\s. FST (uniform t (SUC n) s) < SUC m))``,
   NTAC 2 STRIP_TAC
   ++ Induct
   >> (RW_TAC arith_ss []
       ++ POP_ASSUM (MP_TAC o Q.SPEC `0`)
       ++ RW_TAC arith_ss [DECIDE ``!m. m < 1n = (m = 0)``]
       ++ RW_TAC real_ac_ss [])
   ++ RW_TAC arith_ss []
   ++ KNOW_TAC `indep (uniform t (SUC n))` >> RW_TAC std_ss' [INDEP_UNIFORM]
   ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
   ++ RW_TAC arith_ss []
   ++ MP_TAC (Q.SPECL [`uniform t (SUC n)`, `SUC m`] PROB_INDEP_BOUND)
   ++ ASM_REWRITE_TAC []
   ++ RW_TAC std_ss' []
   ++ KNOW_TAC `&(SUC (SUC m)) = &(SUC m) + 1`
   >> (RW_TAC arith_ss [REAL_ADD,REAL_INJ] ++ DECIDE_TAC)
   ++ RW_TAC std_ss' [REAL_ADD_RDISTRIB]
   ++ MATCH_MP_TAC REAL_LT_ADD2
   ++ RW_TAC real_ac_ss []);

val PROB_UNIFORM_PAIR_SUC = store_thm
  ("PROB_UNIFORM_PAIR_SUC",
   ``!t n k k'. k < SUC n /\ k' < SUC n
                ==> abs (prob (\s. FST (uniform t (SUC n) s) = k)
                         - prob (\s. FST (uniform t (SUC n) s) = k'))
                 <= (1 / 2) pow t``,
   RW_TAC std_ss' []
   ++ Induct_on `t`
   >> (RW_TAC std_ss' [uniform_def, pow]
       ++ MATCH_MP_TAC ABS_UNIT_INTERVAL
       ++ Cases_on `k`
       ++ Cases_on `k'`
       ++ RW_TAC std_ss' [GSYM EMPTY_DEF, GSYM UNIV_DEF, PROB_BASIC]
       ++ REAL_ARITH_TAC)
   ++ RW_TAC std_ss' [uniform_def]
   ++ KNOW_TAC `!s. unif n s = (FST (unif n s), SND (unif n s))`
   >> RW_TAC std_ss' [PAIR]
   ++ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
   ++ (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   ++ RW_TAC std_ss' [COND_RAND, COND_EXPAND]
   ++ (CONV_TAC o RATOR_CONV o ONCE_REWRITE_CONV) [EQ_SYM_EQ]
   ++ RW_TAC std_ss' [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR]
   ++ RW_TAC std_ss' [PROVE [] ``~X /\ X = F``]
   ++ KNOW_TAC `!m. (m = k) /\ (m < SUC n) = (m = k)` >> DECIDE_TAC
   ++ KNOW_TAC `!m. (m = k') /\ (m < SUC n) = (m = k')` >> RW_TAC arith_ss []
   ++ RW_TAC std_ss' [PROVE [] ``X \/ (X /\ Y) = X``]
   ++ NTAC 2 (POP_ASSUM (K ALL_TAC))
   ++ KNOW_TAC `(\s. ~(FST (unif n s) < SUC n) /\
            (FST (uniform t (SUC n) (SND (unif n s))) = k) \/
            (FST (unif n s) = k))
          = (\m. ~(m < SUC n)) o FST o unif n INTER
            (\m. m = k) o FST o uniform t (SUC n) o SND o unif n UNION
            (\m. m = k) o FST o unif n`
   >> PSET_TAC [o_DEF]
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ KNOW_TAC `prob ((\m. ~(m < SUC n)) o FST o unif n INTER
            (\m. m = k) o FST o uniform t (SUC n) o SND o unif n UNION
            (\m. m = k) o FST o unif n)
          = prob ((\m. ~(m < SUC n)) o FST o unif n INTER
              (\m. m = k) o FST o uniform t (SUC n) o SND o unif n)
            + prob ((\m. m = k) o FST o unif n)`
   >> (MATCH_MP_TAC PROB_ADDITIVE
       ++ ASSUME_TAC (Q.SPEC `n` INDEP_UNIF)
       ++ ASSUME_TAC (Q.SPECL [`t`, `n`] INDEP_UNIFORM)
       ++ RW_TAC std_ss' [] <<
       [MATCH_MP_TAC MEASURABLE_INTER
        ++ MP_TAC (Q.SPEC `unif n`
                   (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE2))
        ++ MP_TAC (Q.SPEC `unif n`
                   (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE1))
        ++ RW_TAC std_ss' [o_ASSOC]
        ++ POP_ASSUM MATCH_MP_TAC
        ++ MP_TAC (Q.SPEC `uniform t (SUC n)`
                   (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE1))
        ++ RW_TAC std_ss' [o_ASSOC],
        MP_TAC (Q.SPEC `unif n`
                (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE1))
        ++ RW_TAC std_ss' [o_ASSOC],
        PSET_TAC [o_DEF]
        ++ PROVE_TAC []])
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ KNOW_TAC `prob ((\m. ~(m < SUC n)) o FST o unif n INTER
            (\m. m = k) o FST o uniform t (SUC n) o SND o unif n)
          = prob ((\m. ~(m < SUC n)) o FST o unif n)
            * prob ((\m. m = k) o FST o uniform t (SUC n))`
   >> (MP_TAC (Q.SPEC `unif n`
               (INST_TYPE [alpha |-> numSyntax.num] INDEP_PROB))
       ++ MP_TAC (Q.SPEC `n` INDEP_UNIF)
       ++ RW_TAC std_ss' [o_ASSOC]
       ++ POP_ASSUM MATCH_MP_TAC
       ++ MATCH_MP_TAC (REWRITE_RULE [o_ASSOC] INDEP_MEASURABLE1)
       ++ RW_TAC std_ss' [INDEP_UNIFORM])
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ KNOW_TAC `(\s. ~(FST (unif n s) < SUC n) /\
            (FST (uniform t (SUC n) (SND (unif n s))) = k') \/
            (FST (unif n s) = k'))
          = (\m. ~(m < SUC n)) o FST o unif n INTER
            (\m. m = k') o FST o uniform t (SUC n) o SND o unif n UNION
            (\m. m = k') o FST o unif n`
   >> PSET_TAC [o_DEF]
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ KNOW_TAC `prob ((\m. ~(m < SUC n)) o FST o unif n INTER
            (\m. m = k') o FST o uniform t (SUC n) o SND o unif n UNION
            (\m. m = k') o FST o unif n)
          = prob ((\m. ~(m < SUC n)) o FST o unif n INTER
              (\m. m = k') o FST o uniform t (SUC n) o SND o unif n)
            + prob ((\m. m = k') o FST o unif n)`
   >> (MATCH_MP_TAC PROB_ADDITIVE
       ++ ASSUME_TAC (Q.SPEC `n` INDEP_UNIF)
       ++ ASSUME_TAC (Q.SPECL [`t`, `n`] INDEP_UNIFORM)
       ++ RW_TAC std_ss' [] <<
       [MATCH_MP_TAC MEASURABLE_INTER
        ++ MP_TAC (Q.SPEC `unif n`
                   (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE2))
        ++ MP_TAC (Q.SPEC `unif n`
                   (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE1))
        ++ RW_TAC std_ss' [o_ASSOC]
        ++ POP_ASSUM MATCH_MP_TAC
        ++ MP_TAC (Q.SPEC `uniform t (SUC n)`
                   (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE1))
        ++ RW_TAC std_ss' [o_ASSOC],
        MP_TAC (Q.SPEC `unif n`
                (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE1))
        ++ RW_TAC std_ss' [o_ASSOC],
        PSET_TAC [o_DEF]
        ++ PROVE_TAC []])
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ KNOW_TAC `prob ((\m. ~(m < SUC n)) o FST o unif n INTER
            (\m. m = k') o FST o uniform t (SUC n) o SND o unif n)
          = prob ((\m. ~(m < SUC n)) o FST o unif n)
            * prob ((\m. m = k') o FST o uniform t (SUC n))`
   >> (MP_TAC (Q.SPEC `unif n`
               (INST_TYPE [alpha |-> numSyntax.num] INDEP_PROB))
       ++ MP_TAC (Q.SPEC `n` INDEP_UNIF)
       ++ RW_TAC std_ss' [o_ASSOC]
       ++ POP_ASSUM MATCH_MP_TAC
       ++ MATCH_MP_TAC (REWRITE_RULE [o_ASSOC] INDEP_MEASURABLE1)
       ++ RW_TAC std_ss' [INDEP_UNIFORM])
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ KNOW_TAC `prob ((\m. m = k) o FST o unif n)
                = prob ((\m. m = k') o FST o unif n)`
   >> (RW_TAC std_ss' [o_DEF, Q.SPECL [`n`, `k`, `k'`] PROB_UNIF_PAIR]
       ++ MP_TAC (Q.SPEC `n` UNIF_BOUND_LOWER)
       ++ DECIDE_TAC)
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ RW_TAC std_ss' [REAL_ADD2_SUB2, REAL_SUB_REFL, REAL_ADD_RID]
   ++ RW_TAC std_ss' [GSYM REAL_SUB_LDISTRIB, ABS_MUL, ABS_PROB, pow]
   ++ MATCH_MP_TAC REAL_LE_MUL2
   ++ REVERSE (RW_TAC std_ss' [ABS_POS, PROB_POS]) >> RW_TAC std_ss' [o_DEF]
   ++ KILL_ALL_TAC
   ++ KNOW_TAC `(\m. ~(m < SUC n)) o FST o unif n
                = COMPL ((\m. m < SUC n) o FST o unif n)`
   >> PSET_TAC [o_DEF]
   ++ POP_ASSUM (fn th => REWRITE_TAC [th])
   ++ MP_TAC (Q.SPECL [`(\m. m < SUC n) o FST o unif n`, `1 / 2`]
              PROB_COMPL_LE1)
   ++ MP_TAC (Q.SPEC `unif n`
              (INST_TYPE [alpha |-> numSyntax.num] INDEP_MEASURABLE1))
   ++ RW_TAC std_ss' [INDEP_UNIF, o_ASSOC]
   ++ KILL_ALL_TAC
   ++ RW_TAC real_ac_ss [o_DEF]
   ++ MP_TAC (Q.SPEC `n` PROB_UNIF_GOOD)
   ++ RW_TAC std_ss' [le_ratl]);

val PROB_UNIFORM_SUC = store_thm
  ("PROB_UNIFORM_SUC",
   ``!t n k. k < SUC n
             ==> abs (prob (\s. FST (uniform t (SUC n) s) = k) - 1 / & (SUC n))
                 <= (1 / 2) pow t``,
   (RW_TAC std_ss' [GSYM ABS_BETWEEN_LE] ++ REWRITE_TAC [real_lte]) <<
   [PROVE_TAC [POW_HALF_POS, REAL_LT_LE, real_lte],
    STRIP_TAC
    ++ KNOW_TAC `!k. k < SUC n ==> prob (\s. FST (uniform t (SUC n) s) = k) <
          1 / & (SUC n)`
    >> (RW_TAC std_ss' [real_lt]
	++ STRIP_TAC
	++ KNOW_TAC `(1 / 2) pow t
	             < prob (\s. FST (uniform t (SUC n) s) = k')
	               - prob (\s. FST (uniform t (SUC n) s) = k)`
	>> (Q.PAT_ASSUM `x < y - z` MP_TAC
	    ++ RW_TAC std_ss' [GSYM REAL_LT_ADD_SUB]
	    ++ PROVE_TAC [REAL_ADD_SYM, REAL_LTE_TRANS])
	++ MP_TAC (Q.SPECL [`t`, `n`, `k'`, `k`] PROB_UNIFORM_PAIR_SUC)
	++ RW_TAC std_ss' [GSYM real_lt, abs]
	++ SUFF_TAC `F` >> PROVE_TAC []
	++ POP_ASSUM MP_TAC
	++ RW_TAC std_ss' []
	++ PROVE_TAC [POW_HALF_POS, REAL_LT_TRANS, REAL_LT_LE])
    ++ SUFF_TAC `prob (\s. FST (uniform t (SUC n) s) < SUC n) < 1`
    >> RW_TAC std_ss' [UNIFORM_RANGE, GSYM UNIV_DEF, PROB_BASIC, REAL_LT_REFL]
    ++ MP_TAC (Q.SPEC `1 / &(SUC n)` PROB_UNIFORM_LOWER_BOUND)
    ++ ASM_REWRITE_TAC []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `n`)
    ++ KNOW_TAC `~(& (SUC n) = 0)` >> RW_TAC arith_ss [REAL_INJ]
    ++ RW_TAC arith_ss [GSYM REAL_INV_1OVER, REAL_MUL_RINV],
    STRIP_TAC
    ++ KNOW_TAC `!k. k < SUC n ==>
                   1 / & (SUC n) < prob (\s. FST (uniform t (SUC n) s) = k)`
    >> (RW_TAC std_ss' [real_lt]
	++ STRIP_TAC
	++ KNOW_TAC `(1 / 2) pow t
	             < prob (\s. FST (uniform t (SUC n) s) = k)
	               - prob (\s. FST (uniform t (SUC n) s) = k')`
	>> (RW_TAC std_ss' [GSYM REAL_LT_ADD_SUB]
            ++ ONCE_REWRITE_TAC [REAL_ADD_SYM]
            ++ MP_TAC (Q.SPECL [`prob (\s. FST (uniform t (SUC n) s) = k')`,
                                `1 / & (SUC n)`, `(1 / 2) pow t`]
                       REAL_LE_RADD)
            ++ RW_TAC std_ss' []
	    ++ PROVE_TAC [REAL_ADD_SYM, REAL_LET_TRANS])
	++ MP_TAC (Q.SPECL [`t`, `n`, `k`, `k'`] PROB_UNIFORM_PAIR_SUC)
	++ RW_TAC std_ss' [GSYM real_lt, abs]
	++ SUFF_TAC `F` >> PROVE_TAC []
	++ POP_ASSUM MP_TAC
	++ RW_TAC std_ss' []
	++ PROVE_TAC [POW_HALF_POS, REAL_LT_TRANS, REAL_LT_LE])
    ++ SUFF_TAC `1 < prob (\s. FST (uniform t (SUC n) s) < SUC n)`
    >> RW_TAC std_ss' [UNIFORM_RANGE, GSYM UNIV_DEF, PROB_BASIC, REAL_LT_REFL]
    ++ MP_TAC (Q.SPEC `1 / &(SUC n)` PROB_UNIFORM_UPPER_BOUND)
    ++ ASM_REWRITE_TAC []
    ++ DISCH_THEN (MP_TAC o Q.SPEC `n`)
    ++ KNOW_TAC `~(& (SUC n) = 0)` >> RW_TAC arith_ss [REAL_INJ]
    ++ RW_TAC arith_ss [GSYM REAL_INV_1OVER, REAL_MUL_RINV]]);

val PROB_UNIFORM = store_thm
  ("PROB_UNIFORM",
   ``!t n k. k < n
             ==> abs (prob (\s. FST (uniform t n s) = k) - 1 / &n)
                 <= (1 / 2) pow t``,
   NTAC 3 STRIP_TAC
   ++ Cases_on `n` >> RW_TAC arith_ss []
   ++ RW_TAC std_ss' [PROB_UNIFORM_SUC]);

val _ = export_theory ();
