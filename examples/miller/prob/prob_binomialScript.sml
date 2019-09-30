open HolKernel Parse boolLib bossLib arithmeticTheory pred_setTheory
     listTheory sequenceTheory state_transformerTheory
     hurdUtils extra_numTheory combinTheory
     pairTheory realTheory realLib extra_boolTheory
     extra_pred_setTheory extra_realTheory extra_pred_setTools numTheory
     simpLib seqTheory sequenceTools subtypeTheory res_quanTheory
     binomialTheory sumTheory;

open real_measureTheory real_probabilityTheory prob_algebraTheory probTheory;

val _ = new_theory "prob_binomial";

infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val STRONG_DISJ_TAC = CONV_TAC (REWR_CONV (GSYM IMP_DISJ_THM)) ++ STRIP_TAC;
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond << [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

(* bool *)

(* num *)

(* state_transformer *)

(* sequence *)

(* extra_pred_set *)

(* extra_real *)

(* measure *)

(* probability *)

(* prob_algebra *)

(* prob *)

(* ------------------------------------------------------------------------- *)
(* The definition of the binomial random number generator.                   *)
(* ------------------------------------------------------------------------- *)

val prob_binomial_def = Define
  `(prob_binomial 0 = UNIT 0) /\
   (prob_binomial (SUC n) =
    BIND (prob_binomial n)
    (\m. BIND sdest (\b. UNIT (if b then SUC m else m))))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. prob_binomial n IN indep_fn                                            *)
(* 2. !n m.                                                                  *)
(*      prob bern {s | FST (prob_binomial n s) = m} = binomial n m / 2 pow n *)
(* ------------------------------------------------------------------------- *)

val INDEP_FN_PROB_BINOMIAL = store_thm
  ("INDEP_FN_PROB_BINOMIAL",
   ``!n. prob_binomial n IN indep_fn``,
   Induct
   ++ RW_TAC std_ss [prob_binomial_def, INDEP_FN_SDEST, INDEP_FN_BIND,
                     INDEP_FN_UNIT]);

val PROB_BERN_BINOMIAL = store_thm
  ("PROB_BERN_BINOMIAL",
   ``!n m.
       prob bern {s | FST (prob_binomial n s) = m} =
       &(binomial n m) * (1 / 2) pow n``,
   Induct
   >> (Cases
       ++ RW_TAC arith_ss [prob_binomial_def, UNIT_DEF, binomial_def,
                           GEMPTY, GUNIV, PROB_BERN_BASIC, pow, REAL_OVER1,
                           REAL_DIV_LZERO, REAL_MUL_LID, REAL_MUL_LZERO])
   ++ RW_TAC arith_ss [prob_binomial_def]
   ++ Know
      `{s |
        FST
        (BIND (prob_binomial n)
         (\m. BIND sdest (\b. UNIT (if b then SUC m else m))) s) =
        m} =
       ($= m) o FST o BIND (prob_binomial n)
       (\m. BIND sdest (\b. UNIT (if b then SUC m else m)))`
   >> (SET_EQ_TAC
       ++ RW_TAC std_ss [GSPECIFICATION]
       ++ RW_TAC std_ss [SPECIFICATION, o_THM]
       ++ PROVE_TAC [])
   ++ Rewr
   ++ Know
      `prob bern
       ($= m o FST o
        BIND (prob_binomial n)
        (\m. BIND sdest (\b. UNIT (if b then SUC m else m)))) =
       prob bern
       ($= m o FST o
        BIND sdest
        (\b. BIND (prob_binomial n) (\m. UNIT (if b then SUC m else m))))`
   >> (HO_MATCH_MP_TAC PROB_BERN_BIND_COMM
       ++ RW_TAC std_ss [INDEP_FN_PROB_BINOMIAL, INDEP_FN_SDEST, INDEP_FN_UNIT])
   ++ Rewr
   ++ RW_TAC std_ss' [PROB_BERN_BIND_SDEST, INDEP_FN_BIND, INDEP_FN_UNIT,
                      INDEP_FN_PROB_BINOMIAL, BIND_RIGHT_UNIT]
   ++ Know
      `($= m o FST o BIND (prob_binomial n) (\m. UNIT (SUC m))) =
       ((\x. m = SUC x) o FST o prob_binomial n)`
   >> (FUN_EQ_TAC
       ++ RW_TAC std_ss [o_THM, BIND_DEF, UNIT_DEF, UNCURRY])
   ++ Rewr
   ++ POP_ASSUM MP_TAC
   ++ Know
      `!m. {s | FST (prob_binomial n s) = m} = ($= m o FST o prob_binomial n)`
   >> (SET_EQ_TAC
       ++ RW_TAC std_ss [GSPECIFICATION]
       ++ RW_TAC std_ss [SPECIFICATION, o_THM]
       ++ PROVE_TAC [])
   ++ Rewr
   ++ STRIP_TAC
   ++ Cases_on `m`
   >> (RW_TAC arith_ss [binomial_def, o_DEF, pow, GSYM EMPTY_DEF,
                        PROB_BERN_EMPTY, BIND_RIGHT_UNIT]
       ++ Cases_on `n`
       ++ RW_TAC real_ss [binomial_def])
   ++ RW_TAC std_ss' [binomial_def, REAL_ADD_RDISTRIB, pow, GSYM REAL_ADD]
   ++ Know `!a b c d : real. (a = b) /\ (c = d) ==> (a + c = d + b)`
   >> REAL_ARITH_TAC
   ++ DISCH_THEN MATCH_MP_TAC
   ++ PROVE_TAC [REAL_MUL_ASSOC, REAL_MUL_SYM]);

val _ = export_theory ();



