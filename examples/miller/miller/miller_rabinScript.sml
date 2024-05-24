open HolKernel Parse boolLib bossLib;

open listTheory subtypeTools
     res_quanTools res_quanTheory pred_setTheory extra_pred_setTheory
     arithContext ho_proverTools extra_listTheory subtypeTheory
     listContext arithmeticTheory groupTheory hurdUtils
     groupContext extra_numTheory gcdTheory dividesTheory
     extra_arithTheory finite_groupTheory finite_groupContext
     abelian_groupTheory num_polyTheory extra_binomialTheory
     binomialTheory summationTheory pred_setContext mult_groupTheory
     extra_realTheory realTheory realLib seqTheory
     state_transformerTheory combinTheory;

open util_probTheory real_probabilityTheory probTheory prob_uniformTheory;

val _ = new_theory "miller_rabin";
val _ = ParseExtras.temp_loose_equality()

val EXISTS_DEF = boolTheory.EXISTS_DEF;
val REVERSE = Tactical.REVERSE;
val std_ss' = std_ss ++ boolSimps.ETA_ss;

(* ------------------------------------------------------------------------- *)
(* Some standard tools.                                                      *)
(* ------------------------------------------------------------------------- *)

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;

val std_pc = precontext_mergel [arith_pc, list_pc, pred_set_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;
val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS finite_group_c;

val Strip = S_TAC;
val Simplify = R_TAC;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val (factor_twos_def, factor_twos_ind) = Defn.tprove
  let val d = Hol_defn "factor_twos"
        `factor_twos n =
         if 0 < n /\ EVEN n then
           let (r, s) = factor_twos (n DIV 2) in (SUC r, s)
         else (0, n)`
      val g = `measure (\x. x)`
  in (d, WF_REL_TAC g)
  end;

val _ = save_thm ("factor_twos_def", factor_twos_def);
val _ = save_thm ("factor_twos_ind", factor_twos_ind);

val (modexp_def, modexp_ind) = Defn.tprove
  let val d = Hol_defn "modexp"
        `modexp n a b = if b = 0 then 1
                        else let r = modexp n a (b DIV 2)
                             in let r2 = (r * r) MOD n
                             in if EVEN b then r2 else (r2 * a) MOD n`
      val g = `measure (\(x,y,z). z)`
  in (d, WF_REL_TAC g >> RW_TAC arith_ss [])
  end;

val _ = save_thm ("modexp_def", modexp_def);
val _ = save_thm ("modexp_ind", modexp_ind);

val witness_tail_def = Define `(witness_tail n a 0 = ~(a = 1))
  /\ (witness_tail n a (SUC r)
      = let a2 = (a * a) MOD n
        in if a2 = 1 then ~(a = 1) /\ ~(a = n - 1)
           else witness_tail n a2 r)`;

val witness_def = Define `witness n a
  = let (r, s) = factor_twos (n - 1)
    in witness_tail n (modexp n a s) r`;

val miller_rabin_1_def = Define
  `miller_rabin_1 n s =
     if n = 2 then (T, s)
     else if (n = 1) \/ EVEN n then (F, s)
     else
       let (a, s') = prob_uniform_cut (2 * log2 (n - 1)) (n - 2) s
       in (~witness n (a + 2), s')`;

val miller_rabin_def = Define `miller_rabin n t = many (miller_rabin_1 n) t`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val FACTOR_TWOS_CORRECT = store_thm
  ("FACTOR_TWOS_CORRECT",
   ``!n r s.
       0 < n ==> ((factor_twos n = (r, s)) = ODD s /\ (2 EXP r * s = n))``,
   recInduct factor_twos_ind
   >> S_TAC
   >> ONCE_REWRITE_TAC [factor_twos_def]
   >> RW_TAC std_ss [EXP, MULT_CLAUSES, LET_DEF] >|
   [AR_TAC []
    >> Cases_on `r`
    >- (RW_TAC arith_ss [GSYM EVEN_ODD, EXP] >> PROVE_TAC [])
    >> Q.PAT_X_ASSUM `!r. P r` (MP_TAC o Q.SPECL [`n'`, `s`])
    >> Know `0 < n DIV 2`
    >- (Suff `~(n DIV 2 = 0)` >- DECIDE_TAC
        >> R_TAC []
        >> Suff `0 < n /\ ~(n = 1)` >- DECIDE_TAC
        >> PROVE_TAC [EVEN_ODD_BASIC])
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> R_TAC []
    >> Cases_on `factor_twos (n DIV 2)`
    >> R_TAC []
    >> Suff `(2 EXP n' * s = n DIV 2) = (2 EXP SUC n' * s = n)`
    >- PROVE_TAC []
    >> Know `divides 2 n`
    >- PROVE_TAC [divides_def, EVEN_EXISTS, MULT_COMM]
    >> R_TAC [DIVIDES_ALT]
    >> DISCH_THEN
       (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV o wrap o
        ONCE_REWRITE_RULE [MULT_COMM] o SYM)
    >> R_TAC [EXP, GSYM MULT_ASSOC],
    Cases_on `r` >- (R_TAC [] >> PROVE_TAC [EVEN_ODD])
    >> R_TAC [EXP, GSYM MULT_ASSOC]
    >> PROVE_TAC [EVEN_EXISTS]]);

val MODEXP_CORRECT = store_thm
  ("MODEXP_CORRECT",
   ``!n a b. 1 < n ==> (modexp n a b = (a EXP b) MOD n)``,
   recInduct modexp_ind
   >> RW_TAC arith_ss []
   >> ONCE_REWRITE_TAC [modexp_def]
   >> Cases_on `b = 0` >- R_TAC [EXP]
   >> AR_TAC []
   >> Know `0 < n` >- DECIDE_TAC
   >> STRIP_TAC
   >> MP_TAC (CONJ (Q.SPEC `n` MOD_MULT1) (Q.SPEC `n` MOD_MULT2))
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN
      (fn th =>
       RW_TAC std_ss [LET_DEF]
       >> CONV_TAC
          (DEPTH_CONV
           (REWR_CONV (CONJUNCT1 th) ORELSEC REWR_CONV (CONJUNCT2 th)))
       >> RW_TAC std_ss [GSYM EXP_ADD]) >|
   [Suff `b DIV 2 + b DIV 2 = b` >- RW_TAC std_ss []
    >> Suff `2 * (b DIV 2) = b` >- DECIDE_TAC
    >> MP_TAC (Q.SPECL [`2`, `b`] DIVISION_ALT)
    >> R_TAC []
    >> Know `b MOD 2 = 0` >- RW_TAC std_ss [MOD_TWO]
    >> RW_TAC arith_ss [],
    Know `!m. m * a = m * a EXP 1` >- R_TAC []
    >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
    >> RW_TAC std_ss [GSYM EXP_ADD]
    >> Suff `b DIV 2 + b DIV 2 + 1 = b` >- RW_TAC std_ss []
    >> Suff `2 * (b DIV 2) + 1 = b` >- DECIDE_TAC
    >> MP_TAC (Q.SPECL [`2`, `b`] DIVISION_ALT)
    >> R_TAC [MOD_TWO]
    >> PROVE_TAC [MULT_COMM]]);

val WITNESS_TAIL_CORRECT = store_thm
  ("WITNESS_TAIL_CORRECT",
   ``!n a r s k.
       ODD s /\ (2 EXP r * s = n - 1) /\ 0 < a /\ a < n /\ k <= r /\
       witness_tail n (a EXP (2 EXP (r - k) * s) MOD n) k ==>
       ~prime n``,
   Induct_on `k` >|
   [Simplify [witness_tail_def]
    >> Strip
    >> Q.PAT_X_ASSUM `~(x = y)` MP_TAC
    >> REWRITE_TAC []
    >> MATCH_MP_TAC FERMAT_LITTLE_PRIME
    >> Simplify []
    >> Suff `0 < a /\ ~(n <= a)` >- PROVE_TAC [DIVIDES_LE]
    >> DECIDE_TAC,
    RW_TAC bool_ss [LET_DEF, witness_tail_def] >|
    [Strip
     >> Q.PAT_X_ASSUM `(x * y) MOD n = 1` MP_TAC
     >> Know `0 < n` >- DECIDE_TAC
     >> RW_TAC std_ss [SQUARE_1_MOD_PRIME, MOD_MOD],
     Know `0 < n` >- DECIDE_TAC
     >> Strip
     >> Q.PAT_X_ASSUM `witness_tail x y z` MP_TAC
     >> Q.PAT_X_ASSUM `~(x = y)` MP_TAC
     >> Know `!x : num. x + x = 2 * x` >- DECIDE_TAC
     >> Know `SUC (r - SUC k) = r - k`
     >- (Q.PAT_X_ASSUM `SUC k <= r` MP_TAC
         >> KILL_TAC
         >> DECIDE_TAC)
     >> RW_TAC std_ss [MOD_MULT1, MOD_MULT2, GSYM EXP_ADD, GSYM EXP, MULT_ASSOC]
     >> Strip
     >> Suff `~prime n` >- PROVE_TAC []
     >> Q.PAT_X_ASSUM `!n a. P n a` MATCH_MP_TAC
     >> Q.EXISTS_TAC `a`
     >> Q.EXISTS_TAC `r`
     >> Q.EXISTS_TAC `s`
     >> RW_TAC std_ss []
     >> Q.PAT_X_ASSUM `SUC k <= r` MP_TAC
     >> KILL_TAC
     >> DECIDE_TAC]]);

val WITNESS_CORRECT = store_thm
  ("WITNESS_CORRECT",
   ``!n a. 0 < a /\ a < n /\ witness n a ==> ~prime n``,
   S_TAC
   >> Q.PAT_X_ASSUM `witness n a` MP_TAC
   >> RW_TAC std_ss [witness_def, LET_DEF]
   >> Cases_on `factor_twos (n - 1)`
   >> Know `0 < n - 1` >- DECIDE_TAC
   >> STRIP_TAC
   >> AR_TAC [FACTOR_TWOS_CORRECT, LET_DEF, MODEXP_CORRECT]
   >> MP_TAC (Q.SPECL [`n`, `a`, `q`, `r`, `q`] WITNESS_TAIL_CORRECT)
   >> Simplify []);

val WITNESS_TAIL_1 = store_thm
  ("WITNESS_TAIL_1",
   ``!n r. 1 < n ==> ~witness_tail n 1 r``,
   Strip
   >> Cases_on `r`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [witness_tail_def]
   >> Simplify []);

val WITNESS_TAIL_LEMMA = store_thm
  ("WITNESS_TAIL_LEMMA",
   ``!n r s a k.
       1 < n /\ (2 EXP r * s = n - 1) /\ SUC k <= r /\
       witness_tail n (a EXP (2 EXP (r - k) * s) MOD n) k ==>
       witness_tail n (a EXP (2 EXP (r - SUC k) * s) MOD n) (SUC k)``,
   Strip
   >> POP_ASSUM MP_TAC
   >> Know `SUC (r - SUC k) = r - k` >- DECIDE_TAC
   >> STRIP_TAC
   >> Know `0 < n` >- DECIDE_TAC
   >> STRIP_TAC
   >> RW_TAC std_ss [GSYM EXP_ADD, MOD_MULT1, MOD_MULT2, MULT_ASSOC,
                     GSYM EXP, GSYM ONE, witness_tail_def,
                     GSYM RIGHT_ADD_DISTRIB, NUM_DOUBLE]
   >> PROVE_TAC [WITNESS_TAIL_1]);

val NONWITNESS_TAIL_LEMMA = store_thm
  ("NONWITNESS_TAIL_LEMMA",
   ``!n r s a k.
       1 < n /\ (2 EXP r * s = n - 1) /\ SUC k <= r /\
       ~witness_tail n (a EXP (2 EXP (r - SUC k) * s) MOD n) (SUC k) ==>
       ~witness_tail n (a EXP (2 EXP (r - k) * s) MOD n) k``,
   PROVE_TAC [WITNESS_TAIL_LEMMA]);

val NONWITNESS_TAIL_1 = store_thm
  ("NONWITNESS_TAIL_1",
   ``!n r s a k.
       1 < n /\ (2 EXP r * s = n - 1) /\ k <= r /\
       ~witness_tail n (a EXP (2 EXP (r - k) * s) MOD n) k ==>
       (a EXP (n - 1) MOD n = 1)``,
   Strip
   >> Induct_on `k` >- Simplify [witness_tail_def]
   >> Strip
   >> Know `k <= r` >- DECIDE_TAC
   >> DISCH_THEN
      (fn th =>
       Q.PAT_X_ASSUM `x ==> y ==> z` (fn th2 => MATCH_MP_TAC (MP th2 th)))
   >> PROVE_TAC [NONWITNESS_TAIL_LEMMA]);

val NONWITNESS_TAIL_2 = store_thm
  ("NONWITNESS_TAIL_2",
   ``!n r s a k j.
       1 < n /\ (2 EXP r * s = n - 1) /\ k <= r /\ r - k <= j /\
       ~witness_tail n (a EXP (2 EXP (r - k) * s) MOD n) k /\
       (a EXP (2 EXP SUC j * s) MOD n = 1) ==>
       (a EXP (2 EXP j * s) MOD n = 1) \/
       (a EXP (2 EXP j * s) MOD n = n - 1)``,
   NTAC 4 GEN_TAC
   >> Induct
   >- (RW_TAC arith_ss [witness_tail_def, LET_DEF]
       >> DISJ1_TAC
       >> Know `j = r + (j - r)` >- DECIDE_TAC
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> REWRITE_TAC [EXP_ADD, MULT_ASSOC]
       >> MATCH_MP_TAC MOD_POWER_EQ_1
       >> PROVE_TAC [])
   >> Strip
   >> Know `r - k <= j \/ (j = r - SUC k)` >- DECIDE_TAC
   >> Strip
   >- (Q.PAT_X_ASSUM `!j. P j` MATCH_MP_TAC
       >> ASM_REWRITE_TAC []
       >> CONJ_TAC >- DECIDE_TAC
       >> PROVE_TAC [NONWITNESS_TAIL_LEMMA])
   >> Q.PAT_X_ASSUM `!j. P j` K_TAC
   >> Q.PAT_X_ASSUM `~x` MP_TAC
   >> RW_TAC std_ss [witness_tail_def, LET_DEF]
   >> POP_ASSUM K_TAC
   >> Suff `F` >- Simplify []
   >> POP_ASSUM MP_TAC
   >> Know `0 < n` >- DECIDE_TAC
   >> RW_TAC std_ss [GSYM EXP_ADD, MOD_MULT1, MOD_MULT2, MULT_ASSOC,
                     GSYM EXP, GSYM ONE, GSYM RIGHT_ADD_DISTRIB, NUM_DOUBLE]);

val WITNESS_1 = store_thm
  ("WITNESS_1",
   ``!n. 1 < n ==> ~witness n 1``,
   RW_TAC std_ss [witness_def, LET_DEF]
   >> Cases_on `factor_twos (n - 1)`
   >> Know `0 < n - 1` >- DECIDE_TAC
   >> Strip
   >> AR_TAC [FACTOR_TWOS_CORRECT, LET_DEF, MODEXP_CORRECT, WITNESS_TAIL_1]);

val NONWITNESS_1 = store_thm
  ("NONWITNESS_1",
   ``!n a.
       1 < n /\ ODD n /\ 0 < a /\ a < n /\ ~witness n a ==>
       (a EXP (n - 1) MOD n = 1)``,
   RW_TAC std_ss [witness_def]
   >> Cases_on `factor_twos (n - 1)`
   >> Know `0 < n - 1` >- DECIDE_TAC
   >> Strip
   >> AR_TAC [FACTOR_TWOS_CORRECT, LET_DEF, MODEXP_CORRECT]
   >> MATCH_MP_TAC NONWITNESS_TAIL_1
   >> Q.EXISTS_TAC `q`
   >> Q.EXISTS_TAC `r`
   >> Q.EXISTS_TAC `q`
   >> RW_TAC arith_ss [EXP]);

val NONWITNESS_2 = store_thm
  ("NONWITNESS_2",
   ``!n a r s j.
       1 < n /\ ODD n /\ 0 < a /\ a < n /\ ~witness n a /\ ODD s /\
       (2 EXP r * s = n - 1) /\ (a EXP (2 EXP SUC j * s) MOD n = 1) ==>
       (a EXP (2 EXP j * s) MOD n = 1) \/
       (a EXP (2 EXP j * s) MOD n = n - 1)``,
   RW_TAC std_ss [witness_def, LET_DEF]
   >> Know `0 < n - 1` >- DECIDE_TAC
   >> Strip
   >> Q.PAT_X_ASSUM `~x` MP_TAC
   >> MP_TAC (Q.SPECL [`n - 1`, `r`, `s`] FACTOR_TWOS_CORRECT)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [MODEXP_CORRECT]
   >> MATCH_MP_TAC NONWITNESS_TAIL_2
   >> Q.EXISTS_TAC `r`
   >> Q.EXISTS_TAC `r`
   >> RW_TAC arith_ss [EXP]);

val NONWITNESS_MULT_GROUP = store_thm
  ("NONWITNESS_MULT_GROUP",
   ``!n a.
       1 < n /\ ODD n /\ 0 < a /\ a < n /\ ~witness n a ==>
       a IN gset (mult_group n)``,
   Strip
   >> MATCH_MP_TAC POWER_ID_IN_MULT_GROUP
   >> Q.EXISTS_TAC `n - 1`
   >> RW_TAC arith_ss [NONWITNESS_1]);

Theorem CARD_WITNESS:
   !n.
       1 < n /\ ODD n /\ ~prime n ==>
       (n - 1) <= 2 * CARD {a | 0 < a /\ a < n /\ witness n a}
Proof
   RW_TAC std_ss [GSPEC_DEST]
   >> Suff `2 * CARD (\a. 0 < a /\ a < n /\ ~witness n a) <= (n - 1)`
   >- (Suff `CARD (\a. 0 < a /\ a < n /\ witness n a) +
             CARD (\a. 0 < a /\ a < n /\ ~witness n a) = n - 1`
       >- DECIDE_TAC
       >> Simplify [CONJ_ASSOC]
       >> Simplify [GSYM INTER_DEF_ALT]
       >> Know `(\a. ~witness n a) = COMPL (witness n)`
       >- (SET_EQ_TAC
           >> RW_TAC bool_ss [IN_COMPL]
           >> Simplify [SPECIFICATION])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> ONCE_REWRITE_TAC [INTER_COMM]
       >> MP_TAC (Q.ISPEC `witness n INTER ($< 0 INTER (\a. a < n))` CARD_UNION)
       >> Simplify [FINITE_INTER, FINITE_LESS]
       >> DISCH_THEN
          (MP_TAC o Q.SPEC `COMPL (witness n) INTER ($< 0 INTER (\a. a < n))`)
       >> Simplify [FINITE_INTER, FINITE_LESS]
       >> DISCH_THEN (REWRITE_TAC o wrap o SYM)
       >> Simplify [COMPL_SPLITS]
       >> Know
          `witness n INTER ($< 0 INTER (\a. a < n)) INTER
           (COMPL (witness n) INTER ($< 0 INTER (\a. a < n))) = {}`
       >- (SET_EQ_TAC
           >> Simplify [IN_INTER, IN_COMPL])
       >> DISCH_THEN (Simplify o wrap)
       >> Simplify [INTER_DEF_ALT]
       >> Know `(\x. 0 < x /\ x < n) = (\x. x < n) DIFF {0}`
       >- (SET_EQ_TAC
           >> Simplify [IN_DIFF]
           >> Simplify [SPECIFICATION]
           >> DECIDE_TAC)
       >> DISCH_THEN (Simplify o wrap)
       >> Simplify [CARD_DIFF, FINITE_LESS]
       >> Know `{0} SUBSET (\x. x < n)`
       >- (Simplify [SUBSET_DEF]
           >> Simplify [SPECIFICATION]
           >> Strip
           >> Suff `~(n = 0)` >- DECIDE_TAC
           >> Strip
           >> AR_TAC [EVEN_ODD_BASIC])
       >> DISCH_THEN (fn th => Simplify [th, SUBSET_INTER2])
       >> Simplify [CARD_LESS])
   >> Suff
      `?H :: psubgroup (mult_group n).
         (\a. 0 < a /\ a < n /\ ~witness n a) SUBSET gset H`
   >- (Q.SPEC_TAC (`(\a. 0 < a /\ a < n /\ ~witness n a)`, `s`)
       >> Strip
       >> MP_TAC (Q_RESQ_HALF_ISPEC `mult_group n` LAGRANGE_PROPER)
       >> R_TAC' [MULT_GROUP_SUBTYPE]
       >> DISCH_THEN (MP_TAC o Q_RESQ_SPEC `H`)
       >> MP_TAC (Q.SPEC `n` MULT_GROUP_SET_CARD)
       >> Suff `CARD s <= CARD (gset H)` >- DECIDE_TAC
       >> MP_TAC (Q.ISPEC `gset H : num -> bool` CARD_SUBSET)
       >> ASSUME_TAC (Q.SPEC `n` MULT_GROUP)
       >> AG_TAC [IN_PSUBGROUP]
       >> G_TAC [])
   >> (REVERSE o Cases_on)
      `!x :: gset (mult_group n).
         gpow (mult_group n) x (n - 1) = gid (mult_group n)`
   >- (Q_RESQ_EXISTS_TAC
       `(gset (mult_group n) INTER
         (\g. gpow (mult_group n) g (n - 1) = gid (mult_group n)),
         gop (mult_group n))`
       >> CONJ_TAC >|
       [R_TAC [IN_PSUBGROUP]
        >> REVERSE CONJ_TAC
        >- (R_TAC [gset_def, PSUBSET_DEF, SUBSET_DEF, IN_INTER]
            >> Strip
            >> Q.PAT_X_ASSUM `~!x :: P. M x` MP_TAC
            >> REWRITE_TAC []
            >> Strip
            >> POP_ASSUM MP_TAC
            >> POP_ASSUM (ONCE_REWRITE_TAC o wrap o SYM)
            >> R_TAC [IN_INTER]
            >> R_TAC [SPECIFICATION])
        >> POP_ASSUM K_TAC
        >> R_TAC [IN_SUBGROUP]
        >> R_TAC [gset_def, gop_def, INTER_SUBSET]
        >> R_TAC [IN_GROUP]
        >> R_TAC [gset_def, gop_def]
        >> REVERSE CONJ_TAC
        >- (Strip >|
            [AR_TAC [IN_INTER]
             >> G_TAC [MULT_GROUP_ASSOC],
             Q_RESQ_EXISTS_TAC `gid (mult_group n)`
             >> ASSUME_TAC (Q.SPEC `n` MULT_GROUP)
             >> RES_TAC
             >> G_TAC' [IN_INTER]
             >> R_TAC [SPECIFICATION]
             >> G_TAC []
             >> Strip
             >> Q_RESQ_EXISTS_TAC `ginv (mult_group n) x`
             >> G_TAC' [IN_INTER]
             >> Simplify [SPECIFICATION]
             >> G_TAC [GSYM GINV_GPOW]
             >> POP_ASSUM MP_TAC
             >> Simplify [IN_INTER]
             >> Simplify [SPECIFICATION]])
        >> Simplify [IN_INTER, IN_FUNSET]
        >> ASSUME_TAC (Q.SPEC `n` MULT_GROUP)
        >> RES_TAC
        >> Strip >- G_TAC' []
        >> Q.PAT_X_ASSUM `x IN (\g. P g)` MP_TAC
        >> Q.PAT_X_ASSUM `x' IN (\g. P g)` MP_TAC
        >> Simplify [SPECIFICATION]
        >> ASSUME_TAC (Q.SPEC `n` MULT_GROUP_ABELIAN)
        >> RES_TAC
        >> G_TAC [ABELIAN_GPOW_GOP],
        Simplify [SUBSET_DEF, gset_def, IN_INTER]
        >> NTAC 2 STRIP_TAC
        >> STRONG_CONJ_TAC
        >- (POP_ASSUM (MP_TAC o REWRITE_RULE [SPECIFICATION])
            >> Simplify [NONWITNESS_MULT_GROUP])
        >> POP_ASSUM MP_TAC
        >> POP_ASSUM K_TAC
        >> Simplify [SPECIFICATION, MULT_GROUP_GPOW, MULT_GROUP_ID]
        >> PROVE_TAC [NONWITNESS_1]])
   >> (REVERSE o Cases_on)
      `?p q. 1 < p /\ 1 < q /\ (p * q = n) /\ (gcd p q = 1)`
   >- (Suff `F` >- Simplify []
       >> MP_TAC (Q.SPEC `n` NUM_DECOMPOSE)
       >> ASM_REWRITE_TAC []
       >> POP_ASSUM K_TAC
       >> Strip
       >> MP_TAC (Q.SPECL [`p`, `a`] MULT_GROUP_PRIME_POWER_CYCLIC)
       >> Know `ODD p`
       >- (Suff `ODD (p EXP a)` >- Simplify [ODD_EXP]
           >> Simplify [])
       >> STRIP_TAC
       >> G_TAC [CYCLIC_ALT, MULT_GROUP_SUBTYPE]
       >> Strip
       >> Q.PAT_X_ASSUM `!x :: P. M x` (MP_TAC o Q_RESQ_SPEC `g`)
       >> G_TAC [GPOW_GID_GORD, MULT_GROUP_SUBTYPE]
       >> Q.PAT_X_ASSUM `xx = n` (AR_TAC o wrap o SYM)
       >> Simplify [MULT_GROUP_SET_PRIME_POWER]
       >> Cases_on `a` >- AR_TAC []
       >> Simplify [SUC_SUB1]
       >> Cases_on `n` >- AR_TAC []
       >> Simplify [EXP, GSYM MULT_ASSOC]
       >> Suff `~divides p (p * (p * p EXP n') - 1)`
       >- PROVE_TAC [DIVIDES_DOWNL]
       >> Q.PAT_X_ASSUM `prime p` MP_TAC
       >> KILL_TAC
       >> STRIP_TAC
       >> Know `1 < p * p EXP n'` >- Simplify []
       >> Q.SPEC_TAC (`p * p EXP n'`, `q`)
       >> NTAC 2 STRIP_TAC
       >> Suff `~divides p 1 /\ 1 <= p * q`
       >- PROVE_TAC [DIVIDES_SUB_2, DIVIDES_UPR]
       >> Simplify [])
   >> Strip
   >> Know `?t u. factor_twos (n - 1) = (t, u)`
   >- (Cases_on `factor_twos (n - 1)`
       >> PROVE_TAC [])
   >> Know `0 < n - 1` >- DECIDE_TAC
   >> Simplify [FACTOR_TWOS_CORRECT]
   >> Strip
   >> Know
      `?m v.
         v IN gset (mult_group n) /\
         (gpow (mult_group n) v (2 EXP (t - m) * u) = n - 1)`
   >- (Q.EXISTS_TAC `t`
       >> Q.EXISTS_TAC `n - 1`
       >> STRONG_CONJ_TAC
       >- Simplify [MINUS_1_IN_MULT_GROUP]
       >> Strip
       >> Simplify []
       >> Know `2 < n` >- PROVE_TAC [ODD_GT_1]
       >> Know `mult_group n IN finite_group` >- Simplify [MULT_GROUP_SUBTYPE]
       >> Strip
       >> MP_TAC (Q.SPEC `u` ODD_EXISTS)
       >> ASM_REWRITE_TAC []
       >> Strip
       >> G_TAC [GPOW]
       >> Suff `gpow (mult_group n) (n - 1) 2 = gid (mult_group n)`
       >- G_TAC []
       >> G_TAC [GPOW_GID_GORD, MULT_GROUP_GORD_MINUS_1])
   >> DISCH_THEN (MP_TAC o HO_MATCH_MP WOP)
   >> Strip
   >> Know `!j x. t - m < j /\ j <= t /\ x IN gset (mult_group n) ==>
              ~(gpow (mult_group n) x (2 EXP j * u) = n - 1)`
   >- (Strip
       >> Q.PAT_X_ASSUM `!j. P j` (MP_TAC o Q.SPEC `t - j`)
       >> Know `t - j < m`
       >- (Q.PAT_X_ASSUM `t - m < j` MP_TAC
           >> Q.PAT_X_ASSUM `j <= t` MP_TAC
           >> KILL_TAC
           >> DECIDE_TAC)
       >> DISCH_THEN (Simplify o wrap)
       >> Know `t - (t - j) = j` >- DECIDE_TAC
       >> DISCH_THEN (Simplify o wrap)
       >> Q.EXISTS_TAC `x`
       >> Simplify [])
   >> POP_ASSUM K_TAC
   >> POP_ASSUM MP_TAC
   >> Know `t - m <= t` >- DECIDE_TAC
   >> Q.SPEC_TAC (`t - m`, `m`)
   >> Strip
   >> Q_RESQ_EXISTS_TAC
      `(gset (mult_group n) INTER
        ((\x. gpow (mult_group n) x (2 EXP m * u) = 1) UNION
         (\x. gpow (mult_group n) x (2 EXP m * u) = n - 1)),
        gop (mult_group n))`
   >> REVERSE CONJ_TAC
   >- (Simplify [gset_def, SUBSET_DEF, IN_INTER, IN_UNION]
       >> STRIP_TAC
       >> DISCH_THEN (MP_TAC o REWRITE_RULE [SPECIFICATION])
       >> Simplify []
       >> STRIP_TAC
       >> STRONG_CONJ_TAC >- PROVE_TAC [NONWITNESS_MULT_GROUP]
       >> Strip
       >> Simplify [SPECIFICATION]
       >> CCONTR_TAC
       >> Suff
          `!i.
             m + i <= t ==>
             ~((gpow (mult_group n) x' (2 EXP (m + i) * u) = 1) \/
               (gpow (mult_group n) x' (2 EXP (m + i) * u) = n - 1))`
       >- (DISCH_THEN (MP_TAC o Q.SPEC `t - m`)
           >> Know `m + (t - m) = t` >- DECIDE_TAC
           >> DISCH_THEN (ASM_REWRITE_TAC o wrap)
           >> Q.PAT_X_ASSUM `!x :: P. M x`
              (ASM_REWRITE_TAC o wrap o Q_RESQ_SPEC `x'`)
           >> Simplify [MULT_GROUP_ID])
       >> Induct >- (RW_TAC std_ss [] >> METIS_TAC [])
       >> REVERSE Strip
       >- (Q.PAT_X_ASSUM `!j. P j` (MP_TAC o Q.SPECL [`m + SUC i`, `x'`])
           >> RW_TAC std_ss []
           >> KILL_TAC
           >> DECIDE_TAC)
       >> Know `m + i <= t`
       >- (Q.PAT_X_ASSUM `f:num <= g` MP_TAC >> KILL_TAC >> DECIDE_TAC)
       >> STRIP_TAC
       >> Q.PAT_X_ASSUM `!j. P j` K_TAC
       >> Q.PAT_X_ASSUM `x ==> y` MP_TAC
       >> ASM_REWRITE_TAC []
       >> Q.PAT_X_ASSUM `xx:num = 1` MP_TAC
       >> Simplify [MULT_GROUP_GPOW, ADD_CLAUSES]
       >> Strip
       >> MATCH_MP_TAC NONWITNESS_2
       >> Q.EXISTS_TAC `t`
       >> ASM_REWRITE_TAC [])
   >> Simplify [IN_PSUBGROUP]
   >> Know `mult_group n IN finite_group` >- Simplify [MULT_GROUP]
   >> STRIP_TAC
   >> STRONG_CONJ_TAC
   >- (MATCH_MP_TAC FINITE_SET_SUBGROUP
       >> RW_TAC std_ss [INTER_SUBSET]
       >- (SET_EQ_TAC
           >> RW_TAC std_ss [NOT_IN_EMPTY]
           >> Q.EXISTS_TAC `v`
           >> RW_TAC std_ss [IN_INTER, IN_UNION]
           >> RW_TAC std_ss [SPECIFICATION])
       >> RW_TAC std_ss [IN_FUNSET, IN_INTER] >- G_TAC' []
       >> RW_TAC std_ss [IN_UNION]
       >> RW_TAC std_ss [SPECIFICATION]
       >> Q.PAT_X_ASSUM `_ IN _ UNION _` MP_TAC
       >> Q.PAT_X_ASSUM `_ IN _ UNION _` MP_TAC
       >> Q.SPEC_TAC (`2 EXP m * u`, `a`)
       >> Know `abelian (mult_group (p * q))` >- PROVE_TAC [MULT_GROUP_ABELIAN]
       >> Strip
       >> G_TAC [ABELIAN_GPOW_GOP]
       >> NTAC 2 (POP_ASSUM MP_TAC)
       >> REWRITE_TAC [IN_UNION]
       >> RW_TAC bool_ss [SPECIFICATION]
       >> RW_TAC bool_ss [MULT_GROUP_OP, LESS_MOD, MINUS_1_SQUARED_MOD]
       >> RW_TAC arith_ss [])
   >> Strip
   >> RW_TAC std_ss [PSUBSET_DEF, gset_def, INTER_SUBSET]
   >> POP_ASSUM K_TAC
   >> Q.PAT_X_ASSUM `!j. P j` K_TAC
   >> Q.PAT_X_ASSUM `x = y` MP_TAC
   >> Q.SPEC_TAC (`2 EXP m * u`, `k`)
   >> Q.PAT_X_ASSUM `m <= t` K_TAC
   >> Q.PAT_X_ASSUM `x = y` K_TAC
   >> Q.PAT_X_ASSUM `0 < p * q - 1` K_TAC
   >> Q.PAT_X_ASSUM `ODD u` K_TAC
   >> Q.PAT_X_ASSUM `!x :: P. M x` K_TAC
   >> Q.PAT_X_ASSUM `~prime (p * q)` K_TAC
   >> AR_TAC [ODD_MULT]
   >> NTAC 2 STRIP_TAC
   >> Suff
      `?w :: gset (mult_group (p * q)).
         ~(gpow (mult_group (p * q)) w k = 1) /\
         ~(gpow (mult_group (p * q)) w k = p * q - 1)`
   >- (RESQ_STRIP_TAC
       >> SET_EQ_TAC
       >> RW_TAC std_ss []
       >> Q.EXISTS_TAC `w`
       >> RW_TAC std_ss [IN_INTER, IN_UNION]
       >> RW_TAC std_ss [SPECIFICATION])
   >> MP_TAC (Q.SPECL [`p`, `q`] CHINESE_REMAINDER_WITNESS)
   >> RW_TAC std_ss [IN_GROUP_ISO]
   >> Know `(v MOD p, 1) IN gset (prod_group (mult_group p) (mult_group q))`
   >- (Simplify [PROD_GROUP_SET, IN_CROSS, MULT_GROUP_1]
       >> MATCH_MP_TAC IN_MULT_GROUP_UP
       >> PROVE_TAC [])
   >> Strip
   >> Know
      `?w.
         w IN gset (mult_group (p * q)) /\ ((w MOD p, w MOD q) = (v MOD p, 1))`
   >- (Q.PAT_X_ASSUM `BIJ f s t` MP_TAC
       >> Simplify [BIJ_ALT_RES]
       >> DISCH_THEN (MP_TAC o Q_RESQ_SPEC `(v MOD p, 1)` o CONJUNCT2)
       >> Simplify [RES_EXISTS_UNIQUE]
       >> Strip
       >> Q.EXISTS_TAC `x`
       >> Simplify [])
   >> Strip
   >> Q_RESQ_EXISTS_TAC `w`
   >> Simplify []
   >> Suff
      `?f.
         f IN group_homo (mult_group (p * q))
              (prod_group (mult_group p) (mult_group q)) /\
         ~(f (gpow (mult_group (p * q)) w k) = f 1) /\
         ~(f (gpow (mult_group (p * q)) w k) = f (p * q - 1))`
   >- PROVE_TAC []
   >> Know `mult_group p IN finite_group` >- Simplify [MULT_GROUP]
   >> Know `mult_group q IN finite_group` >- Simplify [MULT_GROUP]
   >> Strip
   >> (MP_TAC o Q.GEN `f` o
       Q.SPECL [`f`, `mult_group (p * q)`,
                `prod_group (mult_group p) (mult_group q)`, `w`] o
       INST_TYPE [(alpha |-> ``:num``), (beta |-> ``:num # num``)])
      GROUP_HOMO_GPOW
   >> G_TAC' [PROD_GROUP_SUBTYPE]
   >> DISCH_THEN K_TAC
   >> Q.EXISTS_TAC `\x. (x MOD p, x MOD q)`
   >> Simplify []
   >> Q.PAT_X_ASSUM `(v MOD p, 1:num) IN gset x` MP_TAC
   >> G_TAC [PROD_GROUP_GPOW, PROD_GROUP_SET, IN_CROSS]
   >> STRIP_TAC
   >> Know `gpow (mult_group q) 1 k = 1`
   >- (Suff `gpow (mult_group q) (gid (mult_group q)) k = gid (mult_group q)`
       >- Simplify [MULT_GROUP_ID]
       >> G_TAC [])
   >> DISCH_THEN (fn th => Simplify [th, MINUS_1_MULT_MOD])
   >> Know `~(1 = q - 1)`
   >- (Know `2 < q` >- PROVE_TAC [ODD_GT_1]
       >> KILL_TAC
       >> DECIDE_TAC)
   >> DISCH_THEN (Simplify o wrap)
   >> Q.PAT_X_ASSUM `gpow xx v k = yy` MP_TAC
   >> Simplify [MULT_GROUP_GPOW, MULT_GROUP_ID]
   >> Strip
   >> Know `(v EXP k MOD (p * q)) MOD p = (p * q - 1) MOD p`
   >- PROVE_TAC []
   >> REWRITE_TAC []
   >> ONCE_REWRITE_TAC [MULT_COMM]
   >> Simplify [MOD_MULT_MOD, MINUS_1_MULT_MOD]
   >> Suff `2 < p` >- (KILL_TAC >> DECIDE_TAC)
   >> PROVE_TAC [ODD_GT_1]
QED

val MILLER_RABIN_1_PRIME = store_thm
  ("MILLER_RABIN_1_PRIME",
   ``!n s. prime n ==> (FST (miller_rabin_1 n s) = T)``,
   (RW_TAC std_ss [miller_rabin_1_def, LET_DEF]
    >> RW_TAC std_ss []) >|
   [PROVE_TAC [NOT_PRIME_1],
    PROVE_TAC [NOT_PRIME_EVEN],
    Q.PAT_X_ASSUM `~(a \/ b)` MP_TAC
    >> Cases_on `prob_uniform_cut (2 * log2 (n - 1)) (n - 2) s`
    >> RW_TAC std_ss [LET_DEF]
    >> Suff `ODD n /\ 0 < q + 2 /\ q + 2 < n` >- PROVE_TAC [WITNESS_CORRECT]
    >> CONJ_TAC >- PROVE_TAC [EVEN_ODD]
    >> CONJ_TAC >- DECIDE_TAC
    >> Cases_on `n = 0` >- PROVE_TAC [EVEN_ODD_BASIC]
    >> Cases_on `n - 2` >- DECIDE_TAC
    >> Suff `q < SUC n'` >- DECIDE_TAC
    >> PROVE_TAC [pairTheory.FST, PROB_UNIFORM_CUT_RANGE]]);

val MILLER_RABIN_1_COMPOSITE = store_thm
  ("MILLER_RABIN_1_COMPOSITE",
   ``!n. ~prime n ==> 1 / 2 <= prob bern {s | FST (miller_rabin_1 n s) = F}``,
   RW_TAC bool_ss []
   >> PURE_REWRITE_TAC [miller_rabin_1_def]
   >> Cases_on `n = 2` >- PROVE_TAC [PRIME_2]
   >> Cases_on `n = 1`
   >- (RW_TAC std_ss [GUNIV, PROB_BERN_BASIC]
       >> PROVE_TAC [HALF_LT_1, REAL_LT_IMP_LE])
   >> Cases_on `EVEN n`
   >- (RW_TAC std_ss [GUNIV, PROB_BERN_BASIC]
       >> PROVE_TAC [HALF_LT_1, REAL_LT_IMP_LE])
   >> ASM_SIMP_TAC bool_ss []
   >> Know `2 * log2 (0 + (n - 1)) <= 2 * log2 (n - 1)`
   >- RW_TAC arith_ss []
   >> Q.SPEC_TAC (`2 * log2 (n - 1)`, `t`)
   >> REWRITE_TAC [ADD_CLAUSES]
   >> Cases_on `n = 0` >- PROVE_TAC [EVEN_ODD_BASIC]
   >> Know `0 < n - 2` >- DECIDE_TAC
   >> Strip
   >> Know
      `{s |
        ~FST
        (let (a,s') = prob_uniform_cut t (n - 2) s in (~witness n (a + 2),s'))}
       =
       {s |
        FST (prob_uniform_cut t (n - 2) s) IN
        count (n - 2) INTER {a | witness n (a + 2)}}`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_INTER, GSPECIFICATION, IN_COUNT, LET_DEF]
       >> Cases_on `prob_uniform_cut t (n - 2) x`
       >> RW_TAC std_ss [LET_DEF]
       >> Suff `q < n - 2` >- PROVE_TAC []
       >> Cases_on `n - 2` >- DECIDE_TAC
       >> PROVE_TAC [pairTheory.FST, PROB_UNIFORM_CUT_RANGE])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> MP_TAC
      (Q.SPECL [`t`, `n - 2`,
                `count (n - 2) INTER {a | witness n (a + 2)}`]
       PROB_BERN_UNIFORM_CUT_CARD_LOWER_SUC)
   >> Know `n - 2 + 1 = n - 1` >- DECIDE_TAC
   >> Simplify [INTER_SUBSET]
   >> DISCH_THEN K_TAC
   >> Q.SPEC_TAC
      (`prob bern
        {s |
         FST (prob_uniform_cut t (n - 2) s) IN
         count (n - 2) INTER {a | witness n (a + 2)}}`,
       `p`)
   >> Suff
      `(1 :real) / 2 <= & (CARD (count (n - 2) INTER {a | witness n (a + 2)})) *
      (1 / & (n - 1))`
   >- REAL_ARITH_TAC
   >> POP_ASSUM K_TAC
   >> ONCE_REWRITE_TAC [REAL_MUL_SYM]
   >> Know `(0 :real) < &(n - 1)` >- RW_TAC arith_ss [REAL_NZ_IMP_LT]
   >> RW_TAC std_ss [GSYM REAL_INV_1OVER, GSYM REAL_MULT_LE_CANCEL]
   >> ONCE_REWRITE_TAC [REAL_MUL_SYM]
   >> Know `(0 :real) < inv 2`
   >- RW_TAC std_ss [REAL_INV_1OVER, HALF_POS]
   >> RW_TAC std_ss [REAL_MULT_LE_CANCEL, REAL_INV_INV, REAL_MUL, REAL_LE]
   >> MP_TAC (Q.SPEC `n` CARD_WITNESS)
   >> RW_TAC arith_ss [ODD_EVEN]
   >> POP_ASSUM MP_TAC
   >> Suff
      `{a | 0 < a /\ a < n /\ witness n a} =
       IMAGE (\x. x + 2) (count (n - 2) INTER {a | witness n (a + 2)})`
   >- (MP_TAC (Q.ISPECL [`(\x : num. x + 2)`,
                         `count (n - 2) INTER {a | witness n (a + 2)}`,
                         `UNIV : num -> bool`] CARD_IMAGE)
       >> impl_tac
       >- (RW_TAC std_ss [INJ_DEF, IN_UNIV, INTER_FINITE, FINITE_COUNT]
           >> DECIDE_TAC)
       >> RW_TAC std_ss [])
   >> SET_EQ_TAC
   >> RW_TAC std_ss [IN_INTER, IN_IMAGE, GSPECIFICATION, IN_COUNT]
   >> EQ_TAC >| (* 2 sub-goals here *)
   [Strip
    >> Q.EXISTS_TAC `x - 2`
    >> Know `1 < x`
    >- (Suff `~(x = 1)` >- DECIDE_TAC
        >> Suff `1 < n` >- PROVE_TAC [WITNESS_1]
        >> DECIDE_TAC)
    >> STRIP_TAC
    >> CONJ_TAC >- DECIDE_TAC
    >> CONJ_TAC >- DECIDE_TAC
    >> Suff `x - 2 + 2 = x` >- RW_TAC std_ss []
    >> DECIDE_TAC,
    STRIP_TAC
    >> CONJ_TAC >- DECIDE_TAC
    >> CONJ_TAC >- DECIDE_TAC
    >> RW_TAC std_ss [] ]);

val MILLER_RABIN_1_MONAD = store_thm
  ("MILLER_RABIN_1_MONAD",
   ``!n.
       miller_rabin_1 n =
       (if n = 2 then UNIT T
        else if (n = 1) \/ EVEN n then UNIT F
        else BIND (prob_uniform_cut (2 * log2 (n - 1)) (n - 2))
             (\a. UNIT (~witness n (a + 2))))``,
   FUN_EQ_TAC
   >> RW_TAC std_ss [miller_rabin_1_def, BIND_DEF, UNIT_DEF, LET_DEF, o_THM]);

val INDEP_FN_MILLER_RABIN_1 = store_thm
  ("INDEP_FN_MILLER_RABIN_1",
   ``!n. miller_rabin_1 n IN indep_fn``,
   RW_TAC std_ss [MILLER_RABIN_1_MONAD, INDEP_FN_UNIT]
   >> MATCH_MP_TAC INDEP_FN_BIND
   >> Cases_on `n - 2`
   >- (Suff `~(n = 1) ==> (n = 0)` >- PROVE_TAC [EVEN_ODD_BASIC]
       >> Q.PAT_X_ASSUM `~(a \/ b)` K_TAC
       >> DECIDE_TAC)
   >> RW_TAC std_ss [INDEP_FN_PROB_UNIFORM_CUT, INDEP_FN_UNIT]);

val MILLER_RABIN_1_COMPOSITE_UPPER = store_thm
  ("MILLER_RABIN_1_COMPOSITE_UPPER",
   ``!n. ~prime n ==> prob bern {s | FST (miller_rabin_1 n s) = T} <= 1 / 2``,
   Strip
   >> MP_TAC (Q.SPEC `n` MILLER_RABIN_1_COMPOSITE)
   >> ASM_REWRITE_TAC []
   >> Suff
      `prob bern {s | FST (miller_rabin_1 n s)} +
       prob bern {s | ~FST (miller_rabin_1 n s)} = 2 * (1 / 2)`
   >- REAL_ARITH_TAC
   >> RW_TAC std_ss' [HALF_CANCEL, INDEP_FN_PROB_FST_NOT,
                      INDEP_FN_MILLER_RABIN_1]
   >> REAL_ARITH_TAC);

val MILLER_RABIN_PRIME = store_thm
  ("MILLER_RABIN_PRIME",
   ``!n t s. prime n ==> FST (miller_rabin n t s) = T``,
   Induct_on `t` >- RW_TAC std_ss [miller_rabin_def, MANY, UNIT_DEF]
   >> RW_TAC std_ss [miller_rabin_def, MANY, BIND_DEF, o_THM]
   >> Cases_on `miller_rabin_1 n s`
   >> Know `FST (miller_rabin_1 n s) = T`
   >- PROVE_TAC [MILLER_RABIN_1_PRIME]
   >> RW_TAC std_ss [GSYM miller_rabin_def]
   >> PROVE_TAC []);

val INDEP_FN_MILLER_RABIN = store_thm
  ("INDEP_FN_MILLER_RABIN",
   ``!n t. miller_rabin n t IN indep_fn``,
   RW_TAC std_ss [INDEP_FN_MANY, miller_rabin_def,
                  INDEP_FN_MILLER_RABIN_1]);

val MILLER_RABIN_COMPOSITE_UPPER = store_thm
  ("MILLER_RABIN_COMPOSITE_UPPER",
   ``!n t.
       ~prime n ==>
       prob bern {s | FST (miller_rabin n t s) = T} <= (1 / 2) pow t``,
   Strip
   >> RW_TAC std_ss [miller_rabin_def]
   >> Know
      `{s | FST (many (miller_rabin_1 n) t s)} =
       FST o many (miller_rabin_1 n) t`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION]
       >> RW_TAC std_ss [o_THM, SPECIFICATION])
   >> DISCH_THEN
      (fn th => RW_TAC std_ss [th, PROB_BERN_MANY, INDEP_FN_MILLER_RABIN_1])
   >> MATCH_MP_TAC POW_LE
   >> MP_TAC (Q.SPEC `n` MILLER_RABIN_1_COMPOSITE_UPPER)
   >> RW_TAC std_ss [o_DEF, GSPEC_DEST]
   >> MATCH_MP_TAC PROB_POSITIVE
   >> Know `(\x. FST (miller_rabin_1 n x)) = I o FST o miller_rabin_1 n`
   >- (FUN_EQ_TAC
       >> RW_TAC std_ss [o_THM, I_THM])
   >> Rewr
   >> RW_TAC std_ss [INDEP_FN_FST_EVENTS, INDEP_FN_MILLER_RABIN_1,
                     PROB_SPACE_BERN]);

val MILLER_RABIN_COMPOSITE = store_thm
  ("MILLER_RABIN_COMPOSITE",
   ``!n t.
       ~prime n ==>
        1 - (1 / 2) pow t <= prob bern {s | FST (miller_rabin n t s) = F}``,
   Strip
   >> Know
      `{s | FST (miller_rabin n t s) = F} =
       COMPL (I o FST o miller_rabin n t)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [IN_COMPL, GSPECIFICATION]
       >> RW_TAC std_ss [SPECIFICATION, o_THM, I_THM])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [PROB_COMPL_BERN, PROB_SPACE_BERN, INDEP_FN_FST_EVENTS,
                     INDEP_FN_MILLER_RABIN]
   >> MP_TAC (Q.SPECL [`n`, `t`] MILLER_RABIN_COMPOSITE_UPPER)
   >> Know `{s | FST (miller_rabin n t s) = T} = (I o FST o miller_rabin n t)`
   >- (SET_EQ_TAC
       >> RW_TAC std_ss [GSPECIFICATION]
       >> RW_TAC std_ss [SPECIFICATION, o_THM, I_THM])
   >> RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

val MILLER_RABIN_DEDUCE_COMPOSITE = store_thm
  ("MILLER_RABIN_DEDUCE_COMPOSITE",
   ``!n t s s'. (miller_rabin n t s = (F, s')) ==> ~prime n``,
   RW_TAC std_ss []
   >> Suff `~FST (miller_rabin n t s) = T` >- PROVE_TAC [MILLER_RABIN_PRIME]
   >> RW_TAC std_ss []);

val _ = export_theory ();
