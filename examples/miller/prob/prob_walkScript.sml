open HolKernel Parse boolLib bossLib arithmeticTheory pred_setTheory
     listTheory sequenceTheory state_transformerTheory
     hurdUtils extra_numTheory combinTheory
     pairTheory realTheory realLib extra_boolTheory
     extra_pred_setTheory extra_realTheory extra_pred_setTools numTheory
     simpLib seqTheory sequenceTools subtypeTheory res_quanTheory;

open real_measureTheory real_probabilityTheory;
open prob_algebraTheory probTheory;

val _ = new_theory "prob_walk";
val _ = ParseExtras.temp_loose_equality()

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
(* The definition of a simple random walk.                                   *)
(* ------------------------------------------------------------------------- *)

val random_lurch_def = Define
  `random_lurch (n:num) = BIND sdest (\b. UNIT (if b then n + 1 else n - 1))`;

val random_walk_def = Define
  `random_walk n k =
   BIND (prob_while_cost ($< 0) random_lurch (n, k)) (\x. UNIT (SND x))`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. prob_while_terminates ($< 0) random_lurch                              *)
(* 2. !n l. !*s. EVEN (FST (random_walk n s)) = EVEN n                       *)
(* ------------------------------------------------------------------------- *)

val RANDOM_LURCHES_TRANSLATION = store_thm
  ("RANDOM_LURCHES_TRANSLATION",
   ``!p i n.
       prob_while_cut ($< p) random_lurch n (p + i) =
       BIND (prob_while_cut ($< 0) random_lurch n i) (\l. UNIT (p + l))``,
   RW_TAC std_ss []
   >> Know `i = (p + i) - p` >- DECIDE_TAC
   >> Rewr'
   >> Know `p <= p + i` >- DECIDE_TAC
   >> Q.SPEC_TAC (`p + i`, `q`)
   >> RW_TAC arith_ss []
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`q`, `q`)
   >> Induct_on `n`
   >- RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, UNCURRY, o_DEF]
   >> FUN_EQ_TAC
   >> REPEAT STRIP_TAC
   >> SEQ_CASES_TAC `x`
   >> BasicProvers.NORM_TAC arith_ss
      [prob_while_cut_def, random_lurch_def, BIND_DEF, o_THM,
       sdest_def, SHD_SCONS, STL_SCONS, UNCURRY, UNIT_DEF]
   >> Suff `F` >- PROVE_TAC []
   >> DECIDE_TAC);

val INDEP_FN_RANDOM_LURCH = store_thm
  ("INDEP_FN_RANDOM_LURCH",
   ``!a. random_lurch a IN indep_fn``,
   RW_TAC std_ss [random_lurch_def, INDEP_FN_BIND, INDEP_FN_UNIT,
                  INDEP_FN_SDEST]);

val INDEP_FN_RANDOM_LURCHES = store_thm
  ("INDEP_FN_RANDOM_LURCHES",
   ``!a b c. prob_while_cut a random_lurch b c IN indep_fn``,
   RW_TAC std_ss [INDEP_FN_PROB_WHILE_CUT, INDEP_FN_RANDOM_LURCH]);

val EVENTS_BERN_RANDOM_LURCHES = store_thm
  ("EVENTS_BERN_RANDOM_LURCHES",
   ``!a.
       {s | ?n. FST (prob_while_cut ($< 0) random_lurch n a s) = 0} IN
       events bern``,
   RW_TAC std_ss [GBIGUNION_IMAGE]
   >> MATCH_MP_TAC EVENTS_COUNTABLE_UNION
   >> RW_TAC std_ss [PROB_SPACE_BERN, COUNTABLE_NUM, image_countable,
                     SUBSET_DEF, IN_IMAGE, IN_UNIV]
   >> Suff
      `{s | FST (prob_while_cut ($< 0) random_lurch n a s) = 0} =
       ($= 0) o FST o prob_while_cut ($< 0) random_lurch n a`
   >- RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_RANDOM_LURCHES]
   >> SET_EQ_TAC
   >> RW_TAC std_ss [GSPECIFICATION, IN_o, o_THM]
   >> RW_TAC std_ss [SPECIFICATION]
   >> PROVE_TAC []);

val RANDOM_LURCHES_MULTIPLICATIVE = store_thm
  ("RANDOM_LURCHES_MULTIPLICATIVE",
   ``!a.
       prob bern
       {s |
        ?n. FST (prob_while_cut ($< 0) random_lurch n a s) = 0} =
       (prob bern
        {s |
         ?n. FST (prob_while_cut ($< 0) random_lurch n 1 s) = 0}) pow a``,
   Induct
   >- (Know `!n s. FST (prob_while_cut ($< 0) random_lurch n 0 s) = 0`
       >- (Cases
           >> RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, UNCURRY,
                               o_THM])
       >> Rewr
       >> RW_TAC std_ss [PROB_BERN_UNIV, GUNIV, pow])
   >> Know
      `!s.
         (?n. FST (prob_while_cut ($< 0) random_lurch n (SUC a) s) = 0) =
         (?n. (FST (prob_while_cut ($< a) random_lurch n (SUC a) s) = a) /\
              (FST (BIND (prob_while_cut ($< a) random_lurch n (SUC a))
                    (\l. prob_while_cut ($< 0) random_lurch n l) s) = 0))`
   >- (POP_ASSUM K_TAC
       >> RW_TAC std_ss' []
       >> EQ_TAC >|
       [RW_TAC std_ss []
        >> Q.EXISTS_TAC `n`
        >> CONJ_TAC >|
        [POP_ASSUM MP_TAC
         >> Know `a < SUC a` >- DECIDE_TAC
         >> Q.SPEC_TAC (`SUC a`, `b`)
         >> Q.SPEC_TAC (`s`, `s`)
         >> Induct_on `n`
         >- RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF]
         >> RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, UNCURRY,
                             o_THM, random_lurch_def]
         >> Know `a < b - 1 \/ (a = b - 1)`
         >- (Q.PAT_X_ASSUM `!x. P x` K_TAC >> DECIDE_TAC)
         >> RW_TAC std_ss [] >- PROVE_TAC []
         >> Cases_on `n`
         >> RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, UNCURRY,
                             o_THM],
         Suff
         `!m.
            n <= m ==>
            (FST (BIND (prob_while_cut ($< a) random_lurch n (SUC a))
                  (prob_while_cut ($< 0) random_lurch m) s) = 0)`
         >- PROVE_TAC [LESS_EQ_REFL]
         >> GEN_TAC
         >> POP_ASSUM MP_TAC
         >> Q.SPEC_TAC (`SUC a`, `b`)
         >> Q.SPEC_TAC (`s`, `s`)
         >> Induct_on `n`
         >- (RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, UNCURRY,
                              o_THM]
             >> Cases_on `m`
             >> RW_TAC arith_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF,
                                 UNCURRY, o_THM])
         >> REPEAT STRIP_TAC
         >> Know `n <= m` >- (Q.PAT_X_ASSUM `!x. P x` K_TAC >> DECIDE_TAC)
         >> STRIP_TAC
         >> Q.PAT_X_ASSUM `x = y` MP_TAC
         >> RW_TAC arith_ss [prob_while_cut_def, GSYM BIND_ASSOC] >|
         [POP_ASSUM MP_TAC
          >> ONCE_REWRITE_TAC [BIND_DEF]
          >> RW_TAC std_ss [UNCURRY, UNIT_DEF, o_THM, random_lurch_def],
          Cases_on `m` >- FULL_SIMP_TAC arith_ss []
          >> POP_ASSUM MP_TAC
          >> Know `!n : num. (n = 0) = ~(0 < n)` >- RW_TAC arith_ss []
          >> RW_TAC std_ss [BIND_DEF, UNIT_DEF, o_THM, UNCURRY,
                            prob_while_cut_def]
          >> MATCH_MP_TAC PROB_WHILE_CUT_MONO
          >> Q.EXISTS_TAC `n`
          >> FULL_SIMP_TAC arith_ss [],
          Know `b = 0` >- RW_TAC arith_ss []
          >> Cases_on `m` >- FULL_SIMP_TAC arith_ss []
          >> RW_TAC arith_ss [BIND_DEF, UNIT_DEF, UNCURRY, prob_while_cut_def,
                              o_THM]]],
        RW_TAC std_ss []
        >> Q.EXISTS_TAC `n + n`
        >> Suff
           `!m n b s.
              (FST (BIND (prob_while_cut ($< a) random_lurch m b)
                    (prob_while_cut ($< 0) random_lurch n) s) = 0) ==>
              (FST (prob_while_cut ($< 0) random_lurch (m + n) b s) = 0)`
        >- PROVE_TAC []
        >> POP_ASSUM_LIST K_TAC
        >> Induct
        >- RW_TAC arith_ss [prob_while_cut_def, BIND_DEF, UNIT_DEF, UNCURRY,
                            o_THM]
        >> RW_TAC arith_ss [prob_while_cut_def, BIND_DEF, UNIT_DEF, UNCURRY,
                            o_THM]
        >- RW_TAC arith_ss [prob_while_cut_def, BIND_DEF, UNIT_DEF, UNCURRY,
                            o_THM, ADD_CLAUSES]
        >> Q.PAT_X_ASSUM `!x. P x` K_TAC
        >> Know `!n : num. (n = 0) = ~(0 < n)` >- DECIDE_TAC
        >> DISCH_THEN (fn th => FULL_SIMP_TAC std_ss [th])
        >> MATCH_MP_TAC PROB_WHILE_CUT_MONO
        >> Q.EXISTS_TAC `n`
        >> RW_TAC arith_ss []])
   >> Rewr
   >> Know
      `!n m b s.
         (FST (prob_while_cut ($< a) random_lurch n b s) = a) /\
         (FST (BIND (prob_while_cut ($< a) random_lurch n b)
               (\l. prob_while_cut ($< 0) random_lurch m l) s) = 0) =
         (FST (prob_while_cut ($< a) random_lurch n b s) = a) /\
         (FST (BIND (prob_while_cut ($< a) random_lurch n b)
               (\l. prob_while_cut ($< 0) random_lurch m a) s) = 0)`
   >- (POP_ASSUM K_TAC
       >> Know `!a b c. (a /\ b = a /\ c) = (a ==> (b = c))` >- DECIDE_TAC
       >> Rewr
       >> Induct
       >- RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, BIND_DEF, UNCURRY,
                         o_THM]
       >> RW_TAC std_ss [PROB_WHILE_CUT_REV, UNIT_DEF, BIND_DEF, UNCURRY,
                         o_THM])
   >> Rewr
   >> Know
      `!n s.
         (FST (prob_while_cut ($< a) random_lurch n (SUC a) s) = a) /\
         (FST (BIND (prob_while_cut ($< a) random_lurch n (SUC a))
               (\l. prob_while_cut ($< 0) random_lurch n a) s) = 0) =
         s IN
         (($= a o FST o prob_while_cut ($< a) random_lurch n (SUC a)) INTER
          (($= 0 o FST o prob_while_cut ($< 0) random_lurch n a) o
           SND o prob_while_cut ($< a) random_lurch n (SUC a)))`
   >- (POP_ASSUM K_TAC
       >> RW_TAC std_ss [IN_INTER, IN_o, o_THM]
       >> RW_TAC arith_ss [SPECIFICATION]
       >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
       >> Know `!a b c. (a /\ b = a /\ c) = (a ==> (b = c))` >- DECIDE_TAC
       >> Rewr
       >> RW_TAC std_ss [UNIT_DEF, BIND_DEF, UNCURRY, o_THM])
   >> Rewr
   >> MATCH_MP_TAC SEQ_UNIQ
   >> Q.EXISTS_TAC
      `prob bern o
       (\n.
          {s |
           s IN
           $= a o FST o prob_while_cut ($< a) random_lurch n (SUC a) INTER
           ($= 0 o FST o prob_while_cut ($< 0) random_lurch n a) o SND o
           prob_while_cut ($< a) random_lurch n (SUC a)})`
   >> CONJ_TAC
   >- (MATCH_MP_TAC PROB_INCREASING_UNION
       >> RW_TAC std_ss [GBIGUNION_IMAGE, PROB_SPACE_BERN, IN_FUNSET, IN_UNIV,
                         SUBSET_DEF, GSPECIFICATION, GDEST] >|
       [MATCH_MP_TAC EVENTS_INTER
        >> STRONG_CONJ_TAC >- RW_TAC std_ss [PROB_SPACE_BERN]
        >> POP_ASSUM K_TAC
        >> METIS_TAC [INDEP_FN_FST_EVENTS, INDEP_FN_RANDOM_LURCHES,
                      INDEP_FN_SND_EVENTS, o_ASSOC],
        POP_ASSUM MP_TAC
        >> SIMP_TAC std_ss [IN_INTER, IN_o, o_THM]
        >> RW_TAC arith_ss [SPECIFICATION, PROB_WHILE_CUT_REV, BIND_DEF, o_THM,
                            UNCURRY, UNIT_DEF]])
   >> ONCE_REWRITE_TAC [o_DEF]
   >> RW_TAC std_ss [GDEST]
   >> MP_TAC (GEN ``x:num``
              (Q.SPECL [`prob_while_cut ($< a) random_lurch x (SUC a)`,
                        `$= a`,
                        `$= 0 o FST o prob_while_cut ($< 0) random_lurch x a`]
               (INST_TYPE [alpha |-> ``:num``] INDEP_FN_PROB)))
   >> RW_TAC std_ss [INDEP_FN_RANDOM_LURCHES, INDEP_FN_FST_EVENTS, pow]
   >> POP_ASSUM K_TAC
   >> HO_MATCH_MP_TAC SEQ_MUL
   >> Know `!f. (\x : num. prob bern (f x)) = prob bern o f`
   >- RW_TAC std_ss [o_DEF]
   >> DISCH_THEN (CONV_TAC o DEPTH_CONV o HO_REWR_CONV)
   >> POP_ASSUM (REWRITE_TAC o wrap o SYM)
   >> RW_TAC std_ss [] >|
   [MATCH_MP_TAC PROB_INCREASING_UNION
    >> SET_EQ_TAC
    >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, INDEP_FN_FST_EVENTS,
                      INDEP_FN_RANDOM_LURCHES, SUBSET_DEF,
                      IN_BIGUNION_IMAGE, GSPECIFICATION, IN_o, o_THM,
                      PROB_WHILE_CUT_REV, BIND_DEF, UNIT_DEF, UNCURRY]
    >> FULL_SIMP_TAC arith_ss [SPECIFICATION, ADD1, RANDOM_LURCHES_TRANSLATION,
                               BIND_DEF, UNCURRY, UNIT_DEF, o_THM]
    >> Suff `!x. (a = a + x) = (x = 0)` >- RW_TAC std_ss []
    >> DECIDE_TAC,
    MATCH_MP_TAC PROB_INCREASING_UNION
    >> SET_EQ_TAC
    >> RW_TAC std_ss [PROB_SPACE_BERN, IN_FUNSET, IN_UNIV, INDEP_FN_FST_EVENTS,
                      INDEP_FN_RANDOM_LURCHES, SUBSET_DEF,
                      IN_BIGUNION_IMAGE, GSPECIFICATION, IN_o, o_THM,
                      PROB_WHILE_CUT_REV, BIND_DEF, UNIT_DEF, UNCURRY]
    >> FULL_SIMP_TAC arith_ss [SPECIFICATION, ADD1, RANDOM_LURCHES_TRANSLATION,
                               BIND_DEF, UNCURRY, UNIT_DEF, o_THM]
    >> PROVE_TAC []]);

val PROB_TERMINATES_RANDOM_WALK = store_thm
  ("PROB_TERMINATES_RANDOM_WALK",
   ``prob_while_terminates ($< 0) random_lurch``,
   Know `!n : num. ~(0 < n) = (n = 0)` >- DECIDE_TAC
   >> RW_TAC std_ss [PROB_WHILE_TERMINATES, probably_bern_def, probably_def,
                     EVENTS_BERN_RANDOM_LURCHES]
   >> POP_ASSUM K_TAC
   >> ONCE_REWRITE_TAC [RANDOM_LURCHES_MULTIPLICATIVE]
   >> Know
      `?p.
         prob bern {s | ?n. FST (prob_while_cut ($< 0) random_lurch n 1 s) = 0}
         = p`
   >- PROVE_TAC []
   >> STRIP_TAC
   >> ASM_SIMP_TAC std_ss []
   >> Suff `p = 1` >- RW_TAC std_ss [POW_ONE]
   >> Suff `p = 1 / 2 * (p * p) + 1 / 2`
   >- (POP_ASSUM K_TAC
       >> STRIP_TAC
       >> Suff `(p - 1) = 0` >- REAL_ARITH_TAC
       >> MATCH_MP_TAC POW_ZERO
       >> Q.EXISTS_TAC `2`
       >> RW_TAC bool_ss [TWO, pow, POW_1, REAL_SUB_LDISTRIB]
       >> Suff `2 * p = p * p + 1` >- REAL_ARITH_TAC
       >> Suff `2 * p = 2 * ((1 / 2) * ((p * p) + 1))`
       >- RW_TAC std_ss [REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID]
       >> RW_TAC std_ss [REAL_EQ_LMUL]
       >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_RID]
       >> PROVE_TAC [])
   >> POP_ASSUM
      (fn th => CONV_TAC (LAND_CONV (REWR_CONV (SYM th))) >> ASSUME_TAC th)
   >> MP_TAC
      (Q.SPEC `{s | ?n. FST (prob_while_cut ($< 0) random_lurch n 1 s) = 0}`
       (GSYM PROB_BERN_INTER_HALVES))
   >> Cond >- RW_TAC std_ss [EVENTS_BERN_RANDOM_LURCHES]
   >> Rewr'
   >> Know
      `!s.
         (?n. FST (prob_while_cut ($< 0) random_lurch n 1 s) = 0) =
         (?n. FST (prob_while_cut ($< 0) random_lurch (SUC n) 1 s) = 0)`
   >- (REVERSE (REPEAT (STRIP_TAC ORELSE EQ_TAC)) >- PROVE_TAC []
       >> REVERSE (Cases_on `n`) >- PROVE_TAC []
       >> FULL_SIMP_TAC arith_ss [prob_while_cut_def, UNIT_DEF])
   >> Rewr
   >> SIMP_TAC arith_ss [prob_while_cut_def, random_lurch_def, BIND_DEF,
                         UNIT_DEF, UNCURRY, o_THM]
   >> Know
      `halfspace T INTER
       {s |
        ?n.
          FST (prob_while_cut ($< 0) random_lurch n
               (if FST (sdest s) then 2 else 0) (SND (sdest s))) = 0} =
       halfspace T INTER
       ({s | ?n. FST (prob_while_cut ($< 0) random_lurch n 2 s) = 0} o stl)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER, IN_HALFSPACE, GSPECIFICATION, sdest_def,
                         IN_o])
   >> Rewr
   >> Know
      `halfspace F INTER
       {s |
        ?n.
          FST (prob_while_cut ($< 0) random_lurch n
               (if FST (sdest s) then 2 else 0) (SND (sdest s))) = 0} =
       halfspace F INTER
       ({s | ?n. FST (prob_while_cut ($< 0) random_lurch n 0 s) = 0} o stl)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER, IN_HALFSPACE, GSPECIFICATION, sdest_def,
                         IN_o])
   >> Rewr
   >> SIMP_TAC std_ss [PROB_BERN_STL_HALFSPACE, EVENTS_BERN_RANDOM_LURCHES]
   >> ONCE_REWRITE_TAC [RANDOM_LURCHES_MULTIPLICATIVE]
   >> ASM_SIMP_TAC bool_ss [pow, TWO, POW_1]
   >> RW_TAC real_ss []);

val RANDOM_LURCHES_PARITY = store_thm
  ("RANDOM_LURCHES_PARITY",
   ``!n k. !*s.
       EVEN (SND (FST (prob_while_cost ($< 0) random_lurch (n, k) s))) =
       EVEN (n + k)``,
   RW_TAC std_ss [prob_while_cost_def]
   >> MP_TAC
      (Q.SPECL
       [`\x:num#num. EVEN (SND x) = EVEN (n + k)`, `$< (0:num) o FST`,
        `prob_cost SUC random_lurch`, `(n,k):num#num`]
       (INST_TYPE [alpha |-> ``:num#num``] STRONG_PROB_WHILE))
   >> BETA_TAC
   >> DISCH_THEN MATCH_MP_TAC
   >> RW_TAC std_ss [INDEP_FN_PROB_COST, PROB_TERMINATES_COST,
                     INDEP_FN_RANDOM_LURCH, PROB_TERMINATES_RANDOM_WALK]
   >> HO_MATCH_MP_TAC UNIVERSAL_PROBABLY
   >> Q.SPEC_TAC (`n`, `n`)
   >> Q.SPEC_TAC (`k`, `k`)
   >> Know `!n : num. ~(0 < n) = (n = 0)` >- DECIDE_TAC
   >> STRIP_TAC
   >> Induct_on `n'`
   >- RW_TAC std_ss [prob_while_cut_def, UNIT_DEF, o_THM, ADD_CLAUSES]
   >> BasicProvers.NORM_TAC std_ss
      [prob_while_cut_def, UNIT_DEF, o_THM, random_lurch_def,
       BIND_DEF, UNCURRY, prob_cost_def] >|
   [Q.PAT_X_ASSUM `0 < n` MP_TAC
    >> POP_ASSUM_LIST K_TAC
    >> RW_TAC arith_ss [GSYM ADD1, ADD_CLAUSES, EVEN],
    Q.PAT_X_ASSUM `0 < n` MP_TAC
    >> POP_ASSUM_LIST K_TAC
    >> RW_TAC arith_ss [ADD1],
    POP_ASSUM MP_TAC
    >> RW_TAC arith_ss []]);

val INDEP_FN_RANDOM_WALK = store_thm
  ("INDEP_FN_RANDOM_WALK",
   ``!n k. random_walk n k IN indep_fn``,
   RW_TAC std_ss [random_walk_def]
   >> MATCH_MP_TAC INDEP_FN_BIND
   >> RW_TAC std_ss [INDEP_FN_UNIT]
   >> MATCH_MP_TAC INDEP_FN_PROB_WHILE_COST
   >> RW_TAC std_ss [INDEP_FN_RANDOM_LURCH, PROB_TERMINATES_RANDOM_WALK]);

val RANDOM_WALK = store_thm
  ("RANDOM_WALK",
   ``!n.
       (random_walk 0 k = UNIT k) /\
       (random_walk (SUC n) k =
        BIND sdest (\b. random_walk (if b then SUC (SUC n) else n) (SUC k)))``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [random_walk_def, prob_while_cost_def]
   >- RW_TAC arith_ss [prob_cost_def, PROB_WHILE_ADVANCE,
                       INDEP_FN_PROB_COST, PROB_TERMINATES_COST,
                       PROB_TERMINATES_RANDOM_WALK, INDEP_FN_RANDOM_LURCH,
                       o_THM, BIND_LEFT_UNIT]
   >> CONV_TAC
      (LAND_CONV
       (SIMP_CONV arith_ss
        [prob_cost_def, PROB_WHILE_ADVANCE,
         INDEP_FN_PROB_COST, PROB_TERMINATES_COST,
         PROB_TERMINATES_RANDOM_WALK, INDEP_FN_RANDOM_LURCH,
         o_THM, BIND_LEFT_UNIT]))
   >> RW_TAC arith_ss [BIND_DEF, UNIT_DEF, UNCURRY, o_THM, random_lurch_def,
                       ADD1]);

val RANDOM_WALK_ML = store_thm
  ("RANDOM_WALK_ML",
   ``!n k.
       random_walk n k =
       if n = 0 then UNIT k
       else coin_flip (random_walk (n + 1) (k + 1))
                      (random_walk (n - 1) (k + 1))``,
   Cases
   >> RW_TAC (arith_ss ++ boolSimps.COND_elim_ss)
      [RANDOM_WALK, ADD1, coin_flip_def]);

val RANDOM_WALK_PARITY = store_thm
  ("RANDOM_WALK_PARITY",
   ``!n k. !*s. EVEN (FST (random_walk n k s)) = EVEN (n + k)``,
   RW_TAC std_ss [random_walk_def]
   >> Suff
      `!s.
         FST
         (BIND
          (prob_while_cost ($< 0) random_lurch (n,k)) (\x. UNIT (SND x)) s) =
         SND (FST (prob_while_cost ($< 0) random_lurch (n, k) s))`
   >- RW_TAC std_ss [RANDOM_LURCHES_PARITY]
   >> RW_TAC std_ss [BIND_DEF, UNIT_DEF, UNCURRY, o_THM]);

val _ = export_theory ();
