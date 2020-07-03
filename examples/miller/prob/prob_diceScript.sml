open HolKernel Parse boolLib bossLib;

open arithmeticTheory pred_setTheory listTheory
     state_transformerTheory combinTheory pairTheory
     realTheory realLib extra_boolTheory res_quanTheory
     hurdUtils extra_numTheory
     extra_realTheory numTheory simpLib seqTheory;

open sequenceTheory sequenceTools extra_pred_setTheory extra_pred_setTools subtypeTheory;
open util_probTheory real_measureTheory real_probabilityTheory;
open prob_algebraTheory probTheory;

(* interactive mode
quietdec := false;
*)

val _ = new_theory "prob_dice";
val _ = ParseExtras.temp_loose_equality()

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val STRONG_DISJ_TAC = CONV_TAC (REWR_CONV (GSYM IMP_DISJ_THM)) THEN STRIP_TAC;
val Cond =
  DISCH_THEN
  (fn mp_th =>
   let
     val cond = fst (dest_imp (concl mp_th))
   in
     KNOW_TAC cond >| [ALL_TAC, DISCH_THEN (MP_TAC o MP mp_th)]
   end);

(* ------------------------------------------------------------------------- *)
(* Some tools.                                                               *)
(* ------------------------------------------------------------------------- *)

fun DDG_INDEP_FN_CONV tm =
  EQT_INTRO
  (prove
   (tm,
    REPEAT
    (CONJ_TAC ORELSE
     MATCH_MP_TAC INDEP_FN_COIN_FLIP ORELSE
     MATCH_MP_TAC INDEP_FN_MMAP)
    >> MATCH_ACCEPT_TAC INDEP_FN_UNIT));

val ddg_ss = std_ss ++ simpLib.SSFRAG {
  ac = [], name = NONE,
  convs = [{conv = K (K DDG_INDEP_FN_CONV), key = SOME ([], ``x IN indep_fn``),
            name = "DDG_INDEP_FN_CONV", trace = 10}],
  dprocs = [],
  filter = NONE,
  rewrs = map (fn th => (NONE, th))
              [IS_SOME_MMAP, IS_SOME_INTER_MMAP, FST_o_UNIT],
  congs = []};

(* ------------------------------------------------------------------------- *)
(* The definition of Knuth's dice.                                           *)
(* ------------------------------------------------------------------------- *)

val dice_def = Define
  `dice : (num -> bool) -> num # (num -> bool) =
   coin_flip
   (prob_repeat
    (coin_flip
     (coin_flip
      (UNIT NONE)
      (UNIT (SOME (1 : num))))
     (MMAP SOME
      (coin_flip
       (UNIT 2)
       (UNIT 3)))))
   (prob_repeat
    (coin_flip
     (MMAP SOME
      (coin_flip
       (UNIT 4)
       (UNIT 5)))
     (coin_flip
      (UNIT (SOME 6))
      (UNIT NONE))))`;

val two_dice_def = Define
  `two_dice = BIND dice (\a. BIND dice (\b. UNIT (a + b)))`;

val optimal_two_dice_def = Define
  `optimal_two_dice : (num -> bool) -> num # (num -> bool) =
   coin_flip
   (prob_repeat
    (coin_flip
     (coin_flip
      (coin_flip
       (coin_flip
        (coin_flip
         (UNIT (SOME 2))
         (coin_flip
          (UNIT NONE)
          (UNIT (SOME 2))))
        (UNIT (SOME 3)))
       (UNIT (SOME 4)))
      (UNIT (SOME 6)))
     (MMAP SOME
      (coin_flip
       (coin_flip
        (coin_flip
         (coin_flip
          (UNIT 3)
          (coin_flip
           (coin_flip
            (UNIT 2)
            (UNIT 4))
           (UNIT 3)))
         (UNIT 5))
        (UNIT 5))
       (UNIT 7)))))
   (prob_repeat
    (coin_flip
     (MMAP SOME
      (coin_flip
       (coin_flip
        (coin_flip
         (coin_flip
          (UNIT 4)
          (coin_flip
           (UNIT 6)
           (coin_flip
            (UNIT 6)
            (UNIT 8))))
         (UNIT 7))
        (UNIT 9))
       (UNIT 8)))
     (coin_flip
      (MMAP SOME
       (coin_flip
        (coin_flip
         (coin_flip
          (UNIT 5)
          (UNIT 9))
         (UNIT 9))
        (UNIT 10)))
      (coin_flip
       (MMAP SOME
        (coin_flip
         (coin_flip
          (coin_flip
           (UNIT 7)
           (UNIT 8))
          (UNIT 10))
         (UNIT 11)))
       (coin_flip
        (MMAP SOME
         (coin_flip
          (coin_flip
           (coin_flip
            (UNIT 10)
            (UNIT 12))
           (UNIT 11))
          (UNIT 11)))
        (coin_flip
         (coin_flip
          (UNIT (SOME 12))
          (UNIT NONE))
         (UNIT (SOME 12))))))))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. dice IN indep_fn                                                       *)
(* 2. !n.                                                                    *)
(*      prob bern {s | FST (dice s) = n} =                                   *)
(*      if 1 <= n /\ n <= 6 then 1 / 6 else 0                                *)
(* ------------------------------------------------------------------------- *)

val PROB_TERMINATES_DICE1 = store_thm
  ("PROB_TERMINATES_DICE1",
   ``?*s.
       IS_SOME
       (FST
        (coin_flip
         (coin_flip (UNIT NONE) (UNIT (SOME (1 : num))))
         (MMAP SOME (coin_flip (UNIT 2) (UNIT 3))) s))``,
   HO_MATCH_MP_TAC POSSIBLY_SOME_COIN_FLIP2
   >> RW_TAC std_ss [POSSIBLY_IS_SOME_MMAP, INDEP_FN_MMAP, INDEP_FN_COIN_FLIP,
                     INDEP_FN_UNIT]);

val INDEP_FN_DICE1 = store_thm
  ("INDEP_FN_DICE1",
   ``prob_repeat
     (coin_flip
      (coin_flip (UNIT NONE) (UNIT (SOME (1 : num))))
      (MMAP SOME (coin_flip (UNIT 2) (UNIT 3)))) IN indep_fn``,
   MATCH_MP_TAC INDEP_FN_PROB_REPEAT
   >> RW_TAC std_ss [PROB_TERMINATES_DICE1, INDEP_FN_COIN_FLIP, INDEP_FN_MMAP,
                     INDEP_FN_UNIT]);

val PROB_TERMINATES_DICE2 = store_thm
  ("PROB_TERMINATES_DICE2",
   ``?*s.
       IS_SOME
       (FST
        (coin_flip
         (MMAP SOME (coin_flip (UNIT (4 : num)) (UNIT 5)))
         (coin_flip (UNIT (SOME 6)) (UNIT NONE)) s))``,
   HO_MATCH_MP_TAC POSSIBLY_SOME_COIN_FLIP1
   >> RW_TAC std_ss [POSSIBLY_IS_SOME_MMAP, INDEP_FN_MMAP, INDEP_FN_COIN_FLIP,
                     INDEP_FN_UNIT]);

val INDEP_FN_DICE2 = store_thm
  ("INDEP_FN_DICE2",
   ``prob_repeat
     (coin_flip
      (MMAP SOME (coin_flip (UNIT (4 : num)) (UNIT 5)))
      (coin_flip (UNIT (SOME 6)) (UNIT NONE))) IN indep_fn``,
   MATCH_MP_TAC INDEP_FN_PROB_REPEAT
   >> RW_TAC std_ss [INDEP_FN_COIN_FLIP, INDEP_FN_MMAP, INDEP_FN_UNIT,
                     PROB_TERMINATES_DICE2]);

val INDEP_FN_DICE = store_thm
  ("INDEP_FN_DICE",
   ``dice IN indep_fn``,
   RW_TAC std_ss [dice_def, INDEP_FN_COIN_FLIP, INDEP_FN_DICE1,
                  INDEP_FN_DICE2]);

val PROB_BERN_DICE = store_thm
  ("PROB_BERN_DICE",
   ``!n.
       prob bern {s | FST (dice s) = n} =
       if 1 <= n /\ n <= 6 then 1 / 6 else 0``,
   STRIP_TAC
   >> MP_TAC (Q.ISPEC `\x : num. x = n` EVENT_TRANSITION)
   >> SIMP_TAC std_ss []
   >> DISCH_THEN K_TAC
   >> SIMP_TAC std_ss [dice_def, PROB_BERN_COIN_FLIP, INDEP_FN_DICE1,
                       INDEP_FN_DICE2, COIN_FLIP_CARNAGE]
   >> SIMP_TAC std_ss [PROB_BERN_REPEAT, INDEP_FN_COIN_FLIP, INDEP_FN_UNIT,
                       INDEP_FN_MMAP, PROB_TERMINATES_DICE1,
                       PROB_TERMINATES_DICE2, PROB_BERN_COIN_FLIP, IS_SOME_MMAP,
                       PROB_BERN_UNIV, IS_SOME_INTER_MMAP]
   >> SIMP_TAC std_ss [FST_o_UNIT, GSPECIFICATION, PROB_BERN_EMPTY,
                       PROB_BERN_UNIV, IN_INTER, IN_o]
   >> SIMP_TAC real_ss [REAL_DIV_ADD]
   >> SIMP_TAC real_ss [GSYM REAL_ADD_LDISTRIB]
   >> MATCH_MP_TAC REAL_LDIV_EQ
   >> CONJ_TAC >- RW_TAC real_ss []
   >> NTAC 3
      (Cases_on `n` >- RW_TAC real_ss [PROB_BERN_EMPTY, PROB_BERN_UNIV]
       >> Cases_on `n'` >- RW_TAC real_ss [PROB_BERN_EMPTY, PROB_BERN_UNIV])
   >> Cases_on `n` >- RW_TAC real_ss [PROB_BERN_EMPTY, PROB_BERN_UNIV]
   >> RW_TAC arith_ss []
   >> RW_TAC real_ss [PROB_BERN_EMPTY, PROB_BERN_UNIV]);

val INDEP_FN_TWO_DICE = store_thm
  ("INDEP_FN_TWO_DICE",
   ``two_dice IN indep_fn``,
   RW_TAC std_ss [INDEP_FN_BIND, two_dice_def, INDEP_FN_UNIT, INDEP_FN_DICE]);

val PROB_BERN_TWO_DICE = store_thm
  ("PROB_BERN_TWO_DICE",
   ``!n.
       prob bern {s | FST (two_dice s) = n} =
       if (n = 2) \/ (n = 12) then 1 / 36
       else if (n = 3) \/ (n = 11) then 2 / 36
       else if (n = 4) \/ (n = 10) then 3 / 36
       else if (n = 5) \/ (n = 9) then 4 / 36
       else if (n = 6) \/ (n = 8) then 5 / 36
       else if (n = 7) then 6 / 36
       else 0``,
   STRIP_TAC
   >> SIMP_TAC std_ss [two_dice_def]
   >> Know
      `{s | FST (BIND dice (\a. BIND dice (\b. (UNIT (a + b)))) s) = n} =
       BIGUNION
       (IMAGE
        (\m. {m} o FST o dice INTER ({n - m} o FST o dice) o SND o dice)
        {m | m <= n})`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_BIGUNION_IMAGE]
       >> PSET_TAC [o_THM]
       >> RW_TAC arith_ss [BIND_DEF, UNIT_DEF, UNCURRY, o_THM])
   >> Rewr
   >> Know
      `prob bern
       (BIGUNION
        (IMAGE
         (\m. {m} o FST o dice INTER ({n - m} o FST o dice) o SND o dice)
         {m | m <= n})) =
       sum (0, SUC n)
       (prob bern o
        (\m. {m} o FST o dice INTER ({n - m} o FST o dice) o SND o dice))`
   >- (MATCH_MP_TAC EQ_SYM
       >> MATCH_MP_TAC PROB_FINITELY_ADDITIVE
       >> RW_TAC std_ss [DISJOINT_ALT, PROB_SPACE_BERN, IN_o, IN_SING,
                         IN_INTER, IN_FUNSET]
       >- (MATCH_MP_TAC EVENTS_INTER
           >> RW_TAC bool_ss
                (o_ASSOC :: map (REWRITE_RULE [o_ASSOC])
                                [INDEP_FN_SND_EVENTS, INDEP_FN_FST_EVENTS,
                                 INDEP_FN_DICE, PROB_SPACE_BERN]))
       >> Suff `{m | m <= n} = count (SUC n)` >- RW_TAC std_ss []
       >> Know `!m. m <= n = m < SUC n` >- DECIDE_TAC
       >> SET_EQ_TAC
       >> PSET_TAC [])
   >> Rewr
   >> ONCE_REWRITE_TAC [o_DEF]
   >> SIMP_TAC bool_ss [INDEP_FN_DICE, INDEP_FN_PROB, INDEP_FN_FST_EVENTS]
   >> Know `!x. {x} o FST o dice = {s | FST (dice s) = x}`
   >- (SET_EQ_TAC
       >> PSET_TAC [o_THM])
   >> Rewr
   >> SIMP_TAC std_ss [PROB_BERN_DICE]
   >> Know `!x y : real. (36 * x = 36 * y) ==> (x = y)` >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> Know
      `36:real *
       (if (n = 2) \/ (n = 12) then 1 / 36
        else if (n = 3) \/ (n = 11) then 2 / 36
        else if (n = 4) \/ (n = 10) then 3 / 36
        else if (n = 5) \/ (n = 9) then 4 / 36
        else if (n = 6) \/ (n = 8) then 5 / 36
        else if (n = 7) then 6 / 36
        else 0) =
       (if (n = 2) \/ (n = 12) then 1
        else if (n = 3) \/ (n = 11) then 2
        else if (n = 4) \/ (n = 10) then 3
        else if (n = 5) \/ (n = 9) then 4
        else if (n = 6) \/ (n = 8) then 5
        else if (n = 7) then 6
        else 0)`
   >- (Suff `!x. (36 :real) * (x / 36) = x` >- RW_TAC std_ss [REAL_MUL_RZERO]
       >> RW_TAC std_ss [real_div]
       >> Know `~((36 :real) = 0)` >- RW_TAC arith_ss [REAL_INJ]
       >> STRIP_TAC
       >> Know `36 * (x * inv 36) = 36 * (inv 36 * x)`
       >- PROVE_TAC [REAL_MUL_SYM]
       >> RW_TAC std_ss []
       >> RW_TAC std_ss [REAL_MUL_RINV, REAL_MUL_ASSOC, REAL_MUL_LID])
   >> Rewr
   >> SIMP_TAC std_ss [GSYM SUM_CMUL]
   >> Know
      `!n'.
         (36 :real) *
         ((if 1 <= n' /\ n' <= 6 then 1 / 6 else 0) *
          (if 1 <= n - n' /\ n <= n' + 6 then 1 / 6 else 0)) =
         (6 * (if 1 <= n' /\ n' <= 6 then 1 / 6 else 0)) *
         (6 * (if 1 <= n - n' /\ n - n' <= 6 then 1 / 6 else 0))`
   >- (Know `(36 :real) = 6 * 6` >- RW_TAC arith_ss [REAL_INJ, REAL_MUL]
       >> Rewr
       >> RW_TAC real_ss [])
   >> Rewr
   >> Know `!c. (6 :real) * (if c then 1 / 6 else 0) = (if c then 1 else 0)`
   >- (RW_TAC arith_ss [REAL_MUL_RINV, GSYM REAL_INV_1OVER, REAL_INJ,
                        REAL_MUL_RZERO])
   >> Rewr
   >> Know
      `!c c'.
         (if c then (1 :real) else 0) * (if c' then 1 else 0) =
         if c /\ c' then 1 else 0`
   >- (RW_TAC arith_ss [REAL_MUL, REAL_INJ]
       >> PROVE_TAC [])
   >> Rewr
   >> Cases_on `12 < n` >- RW_TAC arith_ss [SUM_0]
   >> Know
      `(12 = SUC 11) /\ (11 = SUC 10) /\ (10 = SUC 9) /\ (9 = SUC 8) /\
       (8 = SUC 7) /\ (7 = SUC 6) /\ (6 = SUC 5) /\ (5 = SUC 4) /\
       (4 = SUC 3) /\ (3 = SUC 2) /\ (2 = SUC 1) /\ (1 = SUC 0)`
   >- DECIDE_TAC
   >> Rewr
   >> NTAC 7
      (Cases_on `n` >- RW_TAC arith_ss [REAL_INJ, REAL_MUL, sum, REAL_ADD]
       >> SIMP_TAC std_ss [prim_recTheory.INV_SUC_EQ, NOT_SUC]
       >> Cases_on `n'` >- RW_TAC arith_ss [REAL_INJ, REAL_MUL, sum, REAL_ADD]
       >> SIMP_TAC std_ss [prim_recTheory.INV_SUC_EQ, NOT_SUC])
   >> Suff `F` >- PROVE_TAC []
   >> DECIDE_TAC);

val PROB_TERMINATES_OPTIMAL_TWO_DICE1 = store_thm
  ("PROB_TERMINATES_OPTIMAL_TWO_DICE1",
   ``?*s.
       IS_SOME
       (FST
        (coin_flip
         (coin_flip
          (coin_flip
           (coin_flip
            (coin_flip
             (UNIT (SOME (2 : num)))
             (coin_flip
              (UNIT NONE)
              (UNIT (SOME 2))))
            (UNIT (SOME 3)))
           (UNIT (SOME 4)))
          (UNIT (SOME 6)))
         (MMAP SOME
          (coin_flip
           (coin_flip
            (coin_flip
             (coin_flip
              (UNIT 3)
              (coin_flip
               (coin_flip
                (UNIT 2)
                (UNIT 4))
               (UNIT 3)))
             (UNIT 5))
            (UNIT 5))
           (UNIT 7))) s))``,
   HO_MATCH_MP_TAC POSSIBLY_SOME_COIN_FLIP2
   >> SIMP_TAC std_ss [POSSIBLY_IS_SOME_MMAP]
   >> PROVE_TAC [INDEP_FN_MMAP, INDEP_FN_COIN_FLIP, INDEP_FN_UNIT]);

val INDEP_FN_OPTIMAL_TWO_DICE1R = store_thm
  ("INDEP_FN_OPTIMAL_TWO_DICE1R",
   ``coin_flip
     (coin_flip
      (coin_flip
       (coin_flip
        (coin_flip
         (UNIT (SOME (2 : num)))
         (coin_flip
          (UNIT NONE)
          (UNIT (SOME 2))))
        (UNIT (SOME 3)))
       (UNIT (SOME 4)))
      (UNIT (SOME 6)))
     (MMAP SOME
      (coin_flip
       (coin_flip
        (coin_flip
         (coin_flip
          (UNIT 3)
          (coin_flip
           (coin_flip
            (UNIT 2)
            (UNIT 4))
           (UNIT 3)))
         (UNIT 5))
        (UNIT 5))
       (UNIT 7))) IN indep_fn``,
   CONV_TAC DDG_INDEP_FN_CONV);

val INDEP_FN_OPTIMAL_TWO_DICE1 = store_thm
  ("INDEP_FN_OPTIMAL_TWO_DICE1",
   ``prob_repeat
     (coin_flip
      (coin_flip
       (coin_flip
        (coin_flip
         (coin_flip
          (UNIT (SOME (2 : num)))
          (coin_flip
           (UNIT NONE)
           (UNIT (SOME 2))))
         (UNIT (SOME 3)))
        (UNIT (SOME 4)))
       (UNIT (SOME 6)))
      (MMAP SOME
       (coin_flip
        (coin_flip
         (coin_flip
          (coin_flip
           (UNIT 3)
           (coin_flip
            (coin_flip
             (UNIT 2)
             (UNIT 4))
            (UNIT 3)))
          (UNIT 5))
         (UNIT 5))
        (UNIT 7)))) IN indep_fn``,
   MATCH_MP_TAC INDEP_FN_PROB_REPEAT
   >> SIMP_TAC ddg_ss [PROB_TERMINATES_OPTIMAL_TWO_DICE1]);

val PROB_TERMINATES_OPTIMAL_TWO_DICE2 = store_thm
  ("PROB_TERMINATES_OPTIMAL_TWO_DICE2",
   ``?*s.
       IS_SOME
       (FST
        (coin_flip
         (MMAP SOME
          (coin_flip
           (coin_flip
            (coin_flip
             (coin_flip
              (UNIT (4 : num))
              (coin_flip
               (UNIT 6)
               (coin_flip
                (UNIT 6)
                (UNIT 8))))
             (UNIT 7))
            (UNIT 9))
           (UNIT 8)))
         (coin_flip
          (MMAP SOME
           (coin_flip
            (coin_flip
             (coin_flip
              (UNIT 5)
              (UNIT 9))
             (UNIT 9))
            (UNIT 10)))
          (coin_flip
           (MMAP SOME
            (coin_flip
             (coin_flip
              (coin_flip
               (UNIT 7)
               (UNIT 8))
              (UNIT 10))
             (UNIT 11)))
           (coin_flip
            (MMAP SOME
             (coin_flip
              (coin_flip
               (coin_flip
                (UNIT 10)
                (UNIT 12))
               (UNIT 11))
              (UNIT 11)))
            (coin_flip
             (coin_flip
              (UNIT (SOME 12))
              (UNIT NONE))
             (UNIT (SOME 12)))))) s))``,
   HO_MATCH_MP_TAC POSSIBLY_SOME_COIN_FLIP1
   >> SIMP_TAC std_ss [POSSIBLY_IS_SOME_MMAP]
   >> REPEAT
      (CONJ_TAC ORELSE
       MATCH_MP_TAC INDEP_FN_COIN_FLIP ORELSE
       MATCH_MP_TAC INDEP_FN_MMAP)
   >> MATCH_ACCEPT_TAC INDEP_FN_UNIT);

val INDEP_FN_OPTIMAL_TWO_DICE2R = store_thm
  ("INDEP_FN_OPTIMAL_TWO_DICE2R",
   ``coin_flip
     (MMAP SOME
      (coin_flip
       (coin_flip
        (coin_flip
         (coin_flip
          (UNIT (4 : num))
          (coin_flip
           (UNIT 6)
           (coin_flip
            (UNIT 6)
            (UNIT 8))))
         (UNIT 7))
        (UNIT 9))
       (UNIT 8)))
     (coin_flip
      (MMAP SOME
       (coin_flip
        (coin_flip
         (coin_flip
          (UNIT 5)
          (UNIT 9))
         (UNIT 9))
        (UNIT 10)))
      (coin_flip
       (MMAP SOME
        (coin_flip
         (coin_flip
          (coin_flip
           (UNIT 7)
           (UNIT 8))
          (UNIT 10))
         (UNIT 11)))
       (coin_flip
        (MMAP SOME
         (coin_flip
          (coin_flip
           (coin_flip
            (UNIT 10)
            (UNIT 12))
           (UNIT 11))
          (UNIT 11)))
        (coin_flip
         (coin_flip
          (UNIT (SOME 12))
          (UNIT NONE))
         (UNIT (SOME 12)))))) IN indep_fn``,
   REPEAT
   (CONJ_TAC ORELSE
    MATCH_MP_TAC INDEP_FN_COIN_FLIP ORELSE
    MATCH_MP_TAC INDEP_FN_MMAP)
   >> MATCH_ACCEPT_TAC INDEP_FN_UNIT);

val INDEP_FN_OPTIMAL_TWO_DICE2 = store_thm
  ("INDEP_FN_OPTIMAL_TWO_DICE2",
   ``prob_repeat
     (coin_flip
      (MMAP SOME
       (coin_flip
        (coin_flip
         (coin_flip
          (coin_flip
           (UNIT (4 : num))
           (coin_flip
            (UNIT 6)
            (coin_flip
             (UNIT 6)
             (UNIT 8))))
          (UNIT 7))
         (UNIT 9))
        (UNIT 8)))
      (coin_flip
       (MMAP SOME
        (coin_flip
         (coin_flip
          (coin_flip
           (UNIT 5)
           (UNIT 9))
          (UNIT 9))
         (UNIT 10)))
       (coin_flip
        (MMAP SOME
         (coin_flip
          (coin_flip
           (coin_flip
           (UNIT 7)
            (UNIT 8))
           (UNIT 10))
          (UNIT 11)))
        (coin_flip
         (MMAP SOME
          (coin_flip
           (coin_flip
            (coin_flip
             (UNIT 10)
             (UNIT 12))
            (UNIT 11))
          (UNIT 11)))
         (coin_flip
          (coin_flip
           (UNIT (SOME 12))
           (UNIT NONE))
          (UNIT (SOME 12))))))) IN indep_fn``,
   MATCH_MP_TAC INDEP_FN_PROB_REPEAT
   >> SIMP_TAC std_ss [PROB_TERMINATES_OPTIMAL_TWO_DICE2,
                       INDEP_FN_OPTIMAL_TWO_DICE2R]);

val INDEP_FN_OPTIMAL_TWO_DICE = store_thm
  ("INDEP_FN_OPTIMAL_TWO_DICE",
   ``optimal_two_dice IN indep_fn``,
   RW_TAC std_ss [optimal_two_dice_def, INDEP_FN_COIN_FLIP,
                  INDEP_FN_OPTIMAL_TWO_DICE1,
                  INDEP_FN_OPTIMAL_TWO_DICE2]);

val PROB_BERN_OPTIMAL_TWO_DICE = store_thm
  ("PROB_BERN_OPTIMAL_TWO_DICE",
   ``!n.
       prob bern {s | FST (optimal_two_dice s) = n} =
       if (n = 2) \/ (n = 12) then 1 / 36
       else if (n = 3) \/ (n = 11) then 2 / 36
       else if (n = 4) \/ (n = 10) then 3 / 36
       else if (n = 5) \/ (n = 9) then 4 / 36
       else if (n = 6) \/ (n = 8) then 5 / 36
       else if (n = 7) then 6 / 36
       else 0``,
   STRIP_TAC
   >> MP_TAC (Q.ISPEC `\x : num. x = n` EVENT_TRANSITION)
   >> SIMP_TAC std_ss []
   >> DISCH_THEN K_TAC
   >> SIMP_TAC std_ss [optimal_two_dice_def, PROB_BERN_COIN_FLIP,
                       INDEP_FN_OPTIMAL_TWO_DICE1,
                       INDEP_FN_OPTIMAL_TWO_DICE2, COIN_FLIP_CARNAGE]
   >> SIMP_TAC std_ss [PROB_BERN_REPEAT, PROB_TERMINATES_OPTIMAL_TWO_DICE1,
                       INDEP_FN_OPTIMAL_TWO_DICE1R,
                       PROB_TERMINATES_OPTIMAL_TWO_DICE2,
                       INDEP_FN_OPTIMAL_TWO_DICE2R]
   >> SIMP_TAC ddg_ss [PROB_BERN_COIN_FLIP, PROB_BERN_UNIV, GSPECIFICATION,
                       PROB_BERN_EMPTY, IN_INTER, IN_o]
   >> SIMP_TAC std_ss [REAL_ADD_LID, REAL_ADD_RID, REAL_MUL_LID, REAL_MUL_RID,
                       REAL_MUL_RZERO, REAL_MUL_LZERO]
   >> SIMP_TAC std_ss [ADD1_HALF_MULT, ADD2_HALF_MULT, HALF_CANCEL,
                       HALF_CANCEL_REV, HALF_CANCEL_MULT, HALF_CANCEL_MULT_REV]
   >> Know
      `((1 :real) + 1 / 2 + 2 * 1 + 2 * (2 * 1) + 2 * (2 * (2 * 1)) +
        2 * (2 * (2 * (2 * 1)))) = (1 / 2) * 63`
   >- (RW_TAC arith_ss [REAL_ADD, REAL_MUL]
       >> Know `!x y :real. (2 * x = 2 * y) ==> (x = y)`
       >- REAL_ARITH_TAC
       >> DISCH_THEN MATCH_MP_TAC
       >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
       >> RW_TAC arith_ss [REAL_ADD, REAL_MUL])
   >> Rewr
   >> Know
      `((2 :real) * (2 * (2 * (2 * 1))) +
       (2 * (2 * (2 * 1)) + (2 * (2 * 1) + (2 * 1 + (1 / 2 + 1))))) =
       (1 / 2) * 63`
   >- (RW_TAC arith_ss [REAL_ADD, REAL_MUL]
       >> Know `!x y :real. (2 * x = 2 * y) ==> (x = y)`
       >- REAL_ARITH_TAC
       >> DISCH_THEN MATCH_MP_TAC
       >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
       >> RW_TAC arith_ss [REAL_ADD, REAL_MUL])
   >> Rewr
   >> Know `~((63 :real) = 0)` >- RW_TAC arith_ss [REAL_INJ]
   >> Know `~((1 :real) / 2 = 0)` >- RW_TAC std_ss [REAL_POS_NZ, HALF_POS]
   >> SIMP_TAC std_ss [REAL_DIV_MUL, REAL_ENTIRE]
   >> REPEAT STRIP_TAC
   >> SIMP_TAC std_ss [REAL_DIV_ADD]
   >> MATCH_MP_TAC REAL_LDIV_EQ
   >> CONJ_TAC >- RW_TAC arith_ss []
   >> Know `!x y : real. (2 * x = 2 * y) ==> (x = y)`
   >- REAL_ARITH_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> SIMP_TAC std_ss [REAL_ADD_LDISTRIB, HALF_CANCEL_MULT]
   >> SIMP_TAC std_ss [REAL_MUL_ASSOC]
   >> Know `(2:real) * 63 * 2 = 7 * 36` >- RW_TAC arith_ss [REAL_MUL, REAL_INJ]
   >> Rewr
   >> SIMP_TAC std_ss [GSYM REAL_MUL_ASSOC]
   >> Know
      `(36 :real) *
       (if (n = 2) \/ (n = 12) then 1 / 36
        else if (n = 3) \/ (n = 11) then 2 / 36
        else if (n = 4) \/ (n = 10) then 3 / 36
        else if (n = 5) \/ (n = 9) then 4 / 36
        else if (n = 6) \/ (n = 8) then 5 / 36
        else if (n = 7) then 6 / 36
        else 0) =
       (if (n = 2) \/ (n = 12) then 1
        else if (n = 3) \/ (n = 11) then 2
        else if (n = 4) \/ (n = 10) then 3
        else if (n = 5) \/ (n = 9) then 4
        else if (n = 6) \/ (n = 8) then 5
        else if (n = 7) then 6
        else 0)`
   >- (Suff `!x. (36 :real) * (x / 36) = x` >- RW_TAC std_ss [REAL_MUL_RZERO]
       >> RW_TAC std_ss [real_div]
       >> Know `~((36 :real) = 0)` >- RW_TAC arith_ss [REAL_INJ]
       >> STRIP_TAC
       >> Know `(36 :real) * (x * inv 36) = 36 * (inv 36 * x)`
       >- PROVE_TAC [REAL_MUL_SYM]
       >> RW_TAC std_ss []
       >> RW_TAC std_ss [REAL_MUL_RINV, REAL_MUL_ASSOC, REAL_MUL_LID])
   >> Rewr
   >> Know
      `(12 = SUC 11) /\ (11 = SUC 10) /\ (10 = SUC 9) /\ (9 = SUC 8) /\
       (8 = SUC 7) /\ (7 = SUC 6) /\ (6 = SUC 5) /\ (5 = SUC 4) /\
       (4 = SUC 3) /\ (3 = SUC 2) /\ (2 = SUC 1) /\ (1 = SUC 0)`
   >- DECIDE_TAC
   >> Rewr
   >> NTAC 7
      (Cases_on `n`
       >- (SIMP_TAC bool_ss [REAL_INJ, NOT_SUC, PROB_BERN_EMPTY, REAL_MUL_RZERO,
                             REAL_ADD_LID, PROB_BERN_UNIV, REAL_ADD_RID,
                             REAL_MUL_RID, REAL_ADD, REAL_MUL]
           >> RW_TAC arith_ss [])
       >> SIMP_TAC bool_ss [prim_recTheory.INV_SUC_EQ]
       >> Cases_on `n'`
       >- (SIMP_TAC bool_ss [REAL_INJ, NOT_SUC, PROB_BERN_EMPTY, REAL_MUL_RZERO,
                             REAL_ADD_LID, PROB_BERN_UNIV, REAL_ADD_RID,
                             REAL_MUL_RID, REAL_ADD, REAL_MUL]
           >> RW_TAC arith_ss [])
       >> SIMP_TAC bool_ss [prim_recTheory.INV_SUC_EQ])
   >> SIMP_TAC std_ss [NOT_SUC, REAL_INJ, PROB_BERN_EMPTY, REAL_MUL_RZERO,
                       REAL_ADD_LID]);

val OPTIMAL_TWO_DICE_CORRECT = store_thm
  ("OPTIMAL_TWO_DICE_CORRECT",
   ``!n.
       prob bern {s | FST (optimal_two_dice s) = n} =
       prob bern {s | FST (two_dice s) = n}``,
   SIMP_TAC std_ss [PROB_BERN_OPTIMAL_TWO_DICE, PROB_BERN_TWO_DICE]);

val _ = export_theory ();
