open HolKernel Parse boolLib bossLib arithmeticTheory pred_setTheory
     listTheory sequenceTheory state_transformerTheory
     hurdUtils extra_numTheory combinTheory
     pairTheory realTheory realLib extra_boolTheory
     extra_pred_setTheory extra_realTheory extra_pred_setTools numTheory
     simpLib seqTheory sequenceTools subtypeTheory res_quanTheory;

open util_probTheory real_measureTheory real_probabilityTheory;
open prob_algebraTheory probTheory;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "prob_geometric";

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
(* The definition of the geometric(1/2) random number generator.             *)
(* ------------------------------------------------------------------------- *)

val prob_geometric_iter_def = Define
  `prob_geometric_iter s = BIND sdest (\b. UNIT (b, SUC (SND s)))`;

val prob_geometric_loop_def = Define
  `prob_geometric_loop = prob_while FST prob_geometric_iter`;

val prob_geometric_def = Define
  `prob_geometric =
   BIND (BIND (UNIT (T, 0)) prob_geometric_loop) (\s. UNIT (SND s - 1))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. prob_geometric IN indep_fn                                             *)
(* 2. !n. prob {s | FST (prob_geometric s) = n} = (1 / 2) pow (n + 1)        *)
(* ------------------------------------------------------------------------- *)

val INDEP_FN_PROB_GEOMETRIC_ITER = store_thm
  ("INDEP_FN_PROB_GEOMETRIC_ITER",
   ``!a. prob_geometric_iter a IN indep_fn``,
   RW_TAC std_ss [prob_geometric_iter_def, INDEP_FN_SDEST, INDEP_FN_BIND,
                  INDEP_FN_UNIT]);

val PROB_GEOMETRIC_LOOP_TERMINATES = store_thm
  ("PROB_GEOMETRIC_LOOP_TERMINATES",
   ``prob_while_terminates FST prob_geometric_iter``,
   MATCH_MP_TAC PROB_WHILE_TERMINATES_SUFFICIENT
   >> RW_TAC std_ss [INDEP_FN_PROB_GEOMETRIC_ITER, possibly_bern_def,
                     possibly_def] \\
    ( RW_TAC std_ss [prob_geometric_iter_def, UNIT_DEF, BIND_DEF, o_DEF,
                     UNCURRY]
   >> Suff `{s | ~FST (sdest s)} = halfspace F`
   >- (RW_TAC std_ss [EVENTS_BERN_HALFSPACE, PROB_BERN_HALFSPACE]
       >> PROVE_TAC [REAL_LT_LE, HALF_POS])
   >> SET_EQ_TAC
   >> RW_TAC std_ss [GSPECIFICATION, IN_HALFSPACE, sdest_def] ));

val INDEP_FN_PROB_GEOMETRIC_LOOP = store_thm
  ("INDEP_FN_PROB_GEOMETRIC_LOOP",
   ``!a. prob_geometric_loop a IN indep_fn``,
   RW_TAC std_ss [prob_geometric_loop_def, INDEP_FN_PROB_WHILE,
                  PROB_GEOMETRIC_LOOP_TERMINATES,
                  INDEP_FN_PROB_GEOMETRIC_ITER]);

val INDEP_FN_PROB_GEOMETRIC = store_thm
  ("INDEP_FN_PROB_GEOMETRIC",
   ``prob_geometric IN indep_fn``,
   RW_TAC std_ss [prob_geometric_def, INDEP_FN_BIND, INDEP_FN_UNIT,
                  INDEP_FN_PROB_GEOMETRIC_LOOP]);

val PROB_GEOMETRIC_LOOP_F = store_thm
  ("PROB_GEOMETRIC_LOOP_F",
   ``!n. !*s. FST (prob_geometric_loop (F, n) s) = (F, n)``,
   RW_TAC std_ss [prob_geometric_loop_def]
   >> MP_TAC (Q.ISPEC `\w : bool # num. w = (F, n)` PROB_WHILE)
   >> RW_TAC std_ss []
   >> POP_ASSUM MATCH_MP_TAC
   >> RW_TAC std_ss [PROB_GEOMETRIC_LOOP_TERMINATES,
                     INDEP_FN_PROB_GEOMETRIC_ITER]
   >> MATCH_MP_TAC DEFINITELY_PROBABLY
   >> Cases_on `n'`
   >> RW_TAC std_ss [prob_while_cut_def, BIND_DEF, o_THM, UNCURRY,
                     prob_geometric_iter_def, UNIT_DEF, sdest_def]);

val PROB_GEOMETRIC_LOOP_T_RANGE = store_thm
  ("PROB_GEOMETRIC_LOOP_T_RANGE",
   ``!n. !*s. n < SND (FST (prob_geometric_loop (T,n) s))``,
   RW_TAC std_ss [prob_geometric_loop_def]
   >> MP_TAC (Q.ISPEC `\w : bool # num. n < SND w` PROB_WHILE)
   >> RW_TAC std_ss []
   >> POP_ASSUM MATCH_MP_TAC
   >> RW_TAC std_ss [PROB_GEOMETRIC_LOOP_TERMINATES,
                     INDEP_FN_PROB_GEOMETRIC_ITER]
   >> MATCH_MP_TAC DEFINITELY_PROBABLY
   >> Q.SPEC_TAC (`n`, `n`)
   >> Induct_on `n'` >- RW_TAC std_ss [prob_while_cut_def, UNIT_DEF]
   >> REPEAT GEN_TAC
   >> (REVERSE (Cases_on `shd s`)
       >> RW_TAC std_ss [prob_while_cut_def, BIND_DEF, o_THM, UNCURRY,
                         prob_geometric_iter_def, UNIT_DEF, sdest_def])
   >- (POP_ASSUM MP_TAC
       >> Cases_on `n'`
       >> RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF])
   >> MATCH_MP_TAC LESS_TRANS
   >> Q.EXISTS_TAC `SUC n`
   >> CONJ_TAC >- DECIDE_TAC
   >> Q.PAT_X_ASSUM `!s. P s` MATCH_MP_TAC
   >> RW_TAC std_ss []);

val PROB_GEOMETRIC_LOOP_STOPS = store_thm
  ("PROB_GEOMETRIC_LOOP_STOPS",
   ``!n. !*s. (SND (FST (prob_geometric_loop (b,n) s)) = n) = ~b``,
   RW_TAC std_ss [prob_geometric_loop_def]
   >> MP_TAC (Q.ISPEC `\w : bool # num. (SND w = n) = ~b` PROB_WHILE)
   >> RW_TAC std_ss []
   >> POP_ASSUM MATCH_MP_TAC
   >> RW_TAC std_ss [PROB_GEOMETRIC_LOOP_TERMINATES,
                     INDEP_FN_PROB_GEOMETRIC_ITER]
   >> Cases_on `n'`
   >- (RW_TAC std_ss [prob_while_cut_def, UNIT_DEF]
       >> MATCH_MP_TAC DEFINITELY_PROBABLY
       >> RW_TAC std_ss [])
   >> RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, PROBABLY_TRUE, BIND_DEF,
                     UNCURRY, o_THM, prob_geometric_iter_def, sdest_def]
   >> MATCH_MP_TAC DEFINITELY_PROBABLY
   >> RW_TAC std_ss []
   >> KILL_TAC
   >> Know `!a b : num. b < a ==> ~(a = b)` >- DECIDE_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> Know `n < SUC n` >- DECIDE_TAC
   >> Q.SPEC_TAC (`SUC n`, `m`)
   >> Q.SPEC_TAC (`shd s`, `b`)
   >> Q.SPEC_TAC (`stl s`, `s`)
   >> Induct_on `n''` >- RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF]
   >> RW_TAC arith_ss [prob_while_cut_def, BIND_DEF, UNIT_DEF, UNCURRY, o_THM,
                       prob_geometric_iter_def, sdest_def]);

val PROB_BERN_GEOMETRIC_LOOP_LEMMA = store_thm
  ("PROB_BERN_GEOMETRIC_LOOP_LEMMA",
   ``!d n.
       prob bern
       ((\x. SND x = n + SUC d) o FST o
        BIND sdest (\a. BIND (UNIT (a,SUC n)) prob_geometric_loop)) =
       1 / 2 *
       prob bern
       ((\x. SND x = n + SUC d) o FST o
        (\a. BIND (UNIT (a,SUC n)) prob_geometric_loop) T) +
       1 / 2 *
       prob bern
       ((\x. SND x = n + SUC d) o FST o
        (\a. BIND (UNIT (a,SUC n)) prob_geometric_loop) F)``,
   REPEAT GEN_TAC
   >> (MP_TAC o
       Q.SPECL
       [`sdest`,
        `\a. BIND (UNIT (a,SUC n)) (prob_while FST prob_geometric_iter)`,
        `1 / 2`,
        `\x. SND x = n + SUC d`] o
       INST_TYPE [alpha |-> ``:bool # num``])
      PROB_BERN_BIND_BOOL
   >> Cond
   >- (REVERSE (RW_TAC std_ss [INDEP_FN_SDEST])
       >- (Suff `FST o sdest = halfspace T`
           >- RW_TAC std_ss [PROB_BERN_HALFSPACE]
           >> SET_EQ_TAC
           >> RW_TAC std_ss [IN_HALFSPACE, sdest_def, IN_o]
           >> RW_TAC std_ss [SPECIFICATION])
       >> MATCH_MP_TAC INDEP_FN_BIND
       >> RW_TAC std_ss [INDEP_FN_UNIT]
       >> MATCH_MP_TAC INDEP_FN_PROB_WHILE
       >> RW_TAC std_ss [INDEP_FN_PROB_GEOMETRIC_ITER,
                         PROB_GEOMETRIC_LOOP_TERMINATES])
   >> RW_TAC std_ss [ONE_MINUS_HALF, prob_geometric_loop_def]);

val PROB_BERN_GEOMETRIC_LOOP = store_thm
  ("PROB_BERN_GEOMETRIC_LOOP",
   ``!n d.
       prob bern {s | SND (FST (prob_geometric_loop (T,n) s)) = n + SUC d} =
       (1 / 2) pow SUC d``,
   RW_TAC std_ss [prob_geometric_loop_def]
   >> RW_TAC std_ss [PROB_WHILE_ADVANCE, INDEP_FN_PROB_GEOMETRIC_ITER,
                     PROB_GEOMETRIC_LOOP_TERMINATES, prob_geometric_iter_def,
                     GSYM BIND_ASSOC]
   >> Know
      `!f : (num -> bool) -> (bool # num) # (num -> bool).
         {s | SND (FST (f s)) = n + SUC d} = (\x. SND x = n + SUC d) o FST o f`
   >- (SET_EQ_TAC
       >> PSET_TAC []
       >> RW_TAC std_ss [SPECIFICATION, o_THM])
   >> Rewr
   >> RW_TAC std_ss [GSYM prob_geometric_loop_def]
   >> Q.SPEC_TAC (`n`, `n`)
   >> Induct_on `d`
   >- (RW_TAC std_ss [PROB_BERN_GEOMETRIC_LOOP_LEMMA]
       >> RW_TAC real_ss [ADD_CLAUSES, pow, o_DEF, BIND_DEF, UNCURRY, UNIT_DEF,
                          prob_geometric_loop_def]
       >> Know
          `prob bern
           (\x.
              SND (FST (prob_while FST prob_geometric_iter (F,SUC n) x)) =
              n + 1) =
           prob bern UNIV`
       >- (REWRITE_TAC [GSYM ADD1]
           >> MATCH_MP_TAC PROB_BERN_UNIVERSAL
           >> Q.EXISTS_TAC
              `\s. (SND (FST (prob_geometric_loop (F, SUC n) s)) = SUC n) = ~F`
           >> RW_TAC std_ss [PROB_GEOMETRIC_LOOP_STOPS, EVENTS_BERN_UNIV,
                             IN_UNIV]
           >- (RW_TAC std_ss [SYM prob_geometric_loop_def]
               >> Suff
                  `(\x. SND (FST (prob_geometric_loop (F,SUC n) x)) = SUC n) =
                   (\x. SND x = SUC n) o FST o prob_geometric_loop (F, SUC n)`
               >- (Rewr
                   >> PROVE_TAC [INDEP_FN_FST_EVENTS,
                                 INDEP_FN_PROB_GEOMETRIC_LOOP])
               >> FUN_EQ_TAC
               >> RW_TAC std_ss [o_DEF])
           >> RW_TAC std_ss [SPECIFICATION, GSYM prob_geometric_loop_def])
       >> Rewr
       >> Know
          `prob bern
           (\x.
              SND (FST (prob_while FST prob_geometric_iter (T,SUC n) x)) =
              n + 1) =
           prob bern {}`
       >- (REWRITE_TAC [GSYM ADD1]
           >> MATCH_MP_TAC PROB_BERN_UNIVERSAL
           >> Q.EXISTS_TAC
              `\s. (SND (FST (prob_geometric_loop (T, SUC n) s)) = SUC n) = ~T`
           >> RW_TAC std_ss [PROB_GEOMETRIC_LOOP_STOPS, EVENTS_BERN_EMPTY,
                             NOT_IN_EMPTY]
           >- (RW_TAC std_ss [SYM prob_geometric_loop_def]
               >> Suff
                  `(\x. SND (FST (prob_geometric_loop (T,SUC n) x)) = SUC n) =
                   (\x. SND x = SUC n) o FST o prob_geometric_loop (T, SUC n)`
               >- (Rewr
                   >> PROVE_TAC [INDEP_FN_FST_EVENTS,
                                 INDEP_FN_PROB_GEOMETRIC_LOOP])
               >> FUN_EQ_TAC
               >> RW_TAC std_ss [o_DEF])
           >> RW_TAC std_ss [SPECIFICATION, GSYM prob_geometric_loop_def])
       >> Rewr
       >> RW_TAC real_ss [PROB_BERN_BASIC])
   >> RW_TAC std_ss [PROB_BERN_GEOMETRIC_LOOP_LEMMA]
   >> RW_TAC std_ss [prob_geometric_loop_def, BIND_DEF, o_DEF, UNCURRY,
                     UNIT_DEF]
   >> RW_TAC std_ss [PROB_WHILE_ADVANCE, INDEP_FN_PROB_GEOMETRIC_ITER,
                     PROB_GEOMETRIC_LOOP_TERMINATES, prob_geometric_iter_def,
                     GSYM BIND_ASSOC, UNIT_DEF]
   >> Know `!n d. (SUC n = n + SUC (SUC d)) = F` >- DECIDE_TAC
   >> Rewr
   >> RW_TAC bool_ss [GSYM EMPTY_DEF, PROB_BERN_EMPTY, REAL_MUL_RZERO,
                      GSYM prob_geometric_loop_def, REAL_ADD_RID]
   >> ONCE_REWRITE_TAC [pow]
   >> RW_TAC std_ss [REAL_EQ_MUL_LCANCEL]
   >> DISJ2_TAC
   >> Suff
      `(\x.
         SND
           (FST
              (BIND sdest
                 (\a. BIND (\s. ((a,SUC (SUC n)),s)) prob_geometric_loop) x)) =
         n + SUC (SUC d)) =
         ((\x. SND x = SUC n + SUC d) o FST o
           BIND sdest (\a. BIND (UNIT (a,SUC (SUC n))) prob_geometric_loop))`
   >- (Rewr
       >> RW_TAC std_ss [])
   >> FUN_EQ_TAC
   >> RW_TAC std_ss [BIND_DEF, UNIT_DEF, o_DEF, UNCURRY, ADD_CLAUSES]);

val PROB_BERN_GEOMETRIC = store_thm
  ("PROB_BERN_GEOMETRIC",
   ``!n. prob bern {s | FST (prob_geometric s) = n} = (1 / 2) pow (n + 1)``,
   RW_TAC std_ss [prob_geometric_def, BIND_DEF, o_THM, UNCURRY, UNIT_DEF]
   >> Suff
      `prob bern {s | SND (FST (prob_geometric_loop (T,0) s)) - 1 = n} =
       prob bern {s | SND (FST (prob_geometric_loop (T,0) s)) = 0 + (n + 1)}`
   >- (Rewr
       >> RW_TAC bool_ss [GSYM ADD1, PROB_BERN_GEOMETRIC_LOOP])
   >> MATCH_MP_TAC PROB_BERN_UNIVERSAL
   >> Q.EXISTS_TAC `\s. 0 < SND (FST (prob_geometric_loop (T,0) s))`
   >> RW_TAC std_ss [PROB_GEOMETRIC_LOOP_T_RANGE] >|
   [Suff
    `{s | SND (FST (prob_geometric_loop (T,0) s)) - 1 = n} =
     (\x. SND x - 1 = n) o FST o prob_geometric_loop (T, 0)`
    >- (Rewr
        >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_GEOMETRIC_LOOP])
    >> SET_EQ_TAC
    >> PSET_TAC []
    >> RW_TAC std_ss [SPECIFICATION, o_DEF],
    Suff
    `{s | SND (FST (prob_geometric_loop (T,0) s)) = n + 1} =
     (\x. SND x = n + 1) o FST o prob_geometric_loop (T, 0)`
    >- (Rewr
        >> PROVE_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_PROB_GEOMETRIC_LOOP])
    >> SET_EQ_TAC
    >> PSET_TAC []
    >> RW_TAC std_ss [SPECIFICATION, o_DEF],
    RW_TAC std_ss [GSPECIFICATION]
    >> DECIDE_TAC]);

val _ = export_theory ();
