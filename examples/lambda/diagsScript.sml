open HolKernel Parse boolLib

open relationTheory bossLib boolSimps

val _ = new_theory "diags"

val eval_def = Define`
  eval (Fa : 'n -> 'a -> 'a -> bool)
       (G : 'n -> ('a + 'b) -> ('a + 'b) -> bool)
       (R : 'n -> 'c -> 'c -> bool) =
    ! (f : 'a -> 'c).
         (!a1 a2 n. Fa n a1 a2 ==> R n (f a1) (f a2)) ==>
         ? (g : 'b -> 'c).
              (!a1 a2 n. G n (INL a1) (INL a2) ==> R n (f a1) (f a2)) /\
              (!a b n. G n (INL a) (INR b) ==> R n (f a) (g b)) /\
              (!a b n. G n (INR b) (INL a) ==> R n (g b) (f a)) /\
              (!b1 b2 n. G n (INR b1) (INR b2) ==> R n (g b1) (g b2))
`;

val diamond_eval = store_thm(
  "diamond_eval",
  ``eval (\i m n. (i = 0) /\ ((m = 0) /\ (n = 1) \/ (m = 0) /\ (n = 2)))
         (\i m n. (i = 0) /\ ((m = INL 1) /\ (n = INR 0) \/
                              (m = INL 2) /\ (n = INR 0)))
         R
     = diamond (R 0)``,
  SRW_TAC [DNF_ss][diamond_def, eval_def, EQ_IMP_THM] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x
                                    else if n = 1 then y
                                    else z`
                   MP_TAC) THEN
    SRW_TAC [DNF_ss][] THEN METIS_TAC [],
    `?u. R 0 (f 1) u /\ R 0 (f 2) u` by METIS_TAC [] THEN
    Q.EXISTS_TAC `K u` THEN SRW_TAC [][]
  ]);

val totality_eval = store_thm(
  "totality_eval",
  ``eval (\i m n. F) (\i m n. (i = 0) /\ (m = (INL 0)) /\ (n = (INL 1)))
         R =
    !x y. R 0 x y``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM] THEN
  FIRST_X_ASSUM (Q.SPEC_THEN `\i. if i = 0 then x else y` MP_TAC) THEN
  SRW_TAC [][]);

val sequentialisation_eval = store_thm(
  "sequentialisation_eval",
  ``eval (\i m n. (i = 0) /\ (m = 0) /\ (n = 1))
         (\i m n. (i = 1) /\ (m = INL 0) /\ (n = INR 0) \/
                  (i = 2) /\ (m = INR 0) /\ (n = INL 1))
         R =
    (!x y. R 0 x y ==> ?z. R 1 x z /\ R 2 z y)``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x else y` MP_TAC) THEN
    SRW_TAC [DNF_ss][] THEN METIS_TAC [],
    `?z. R 1 (f 0) z /\ R 2 z (f 1)` by METIS_TAC [] THEN
    Q.EXISTS_TAC `K z` THEN SRW_TAC [][]
  ]);

val only_black_eq_T = prove(
  ``eval (\i m n. (i = 0) /\ (m = INL 0) /\ (n = INL 0)) (\i m n. F) R' = T``,
  SRW_TAC [DNF_ss][eval_def]);

val relationally_reflected = store_thm(
  "relationally_reflected",
  ``eval (\i m n. (i = 0) /\ (m = 0) /\ (n = 1))
         (\i m n. (i = 1) /\ (m = INR 0) /\ (n = INL 0) \/
                  (i = 1) /\ (m = INR 1) /\ (n = INL 1) \/
                  (i = 2) /\ (m = INR 0) /\ (n = INR 1))
         R =
    (!x y. R 0 x y ==> ?u v. R 1 u x /\ R 1 v y /\ R 2 u v)``,
  SRW_TAC [DNF_ss][eval_def, EQ_IMP_THM] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `\n. if n = 0 then x else y` MP_TAC) THEN
    SRW_TAC [DNF_ss][] THEN METIS_TAC [],
    `?u v. R 1 u (f 0) /\ R 1 v (f 1) /\ R 2 u v` by METIS_TAC [] THEN
    Q.EXISTS_TAC `\n. if n = 0 then u else v` THEN
    SRW_TAC [][]
  ]);

val Rhomo_def = Define`
  Rhomo f R1 R2 = !x y. R1 x y ==> R2 (f x) (f y)
`;

val onto_def = Define`
  onto f = !x. ?y. f y = x
`;

val ARSh_def = Define`
  ARSh f R1 R2 = (!b. ?a. f(a) = b) /\
                 (!x y. R1 x y ==> R2 (f x) (f y))
`;

val ARSh_alt = store_thm(
  "ARSh_alt",
  ``ARSh f R1 R2 = onto f /\ Rhomo f R1 R2``,
  SRW_TAC [][onto_def, Rhomo_def, ARSh_def]);

val full_def = Define`
  full f R1 R2 = !b1 b2. R2 b1 b2 ==>
                         ?a1 a2. R1 a1 a2 /\ (b1 = f a1) /\ (b2 = f a2)
`;

val lrfull_def = Define`
  lrfull f R1 R2 = !x y. R2 (f x) (f y) ==> R1 x y
`;

val ARSh_RTC = store_thm(
  "ARSh_RTC",
  ``ARSh f R1 R2 ==> ARSh f (RTC R1) (RTC R2)``,
  SRW_TAC [][ARSh_def] THEN
  Q_TAC SUFF_TAC `!x y. RTC R1 x y ==> RTC R2 (f x) (f y)`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN METIS_TAC [RTC_RULES]);

val skernel_def = Define`
  skernel s f = !x y. (f x = f y) ==> EQC s x y
`;

val ofree_def = Define`
  ofree s = !x y. EQC s x y ==> RTC s x y
`;

val note_lemma9 = store_thm(
  "note_lemma9",
  ``onto f  /\ skernel s f /\ ofree s ==>
    (full f (RTC (x RUNION s)) (RTC y) =
     lrfull f (RTC (x RUNION s)) (RTC y))``,
  SIMP_TAC (srw_ss()) [onto_def, skernel_def, ofree_def, full_def,
                       lrfull_def] THEN STRIP_TAC THEN EQ_TAC
  THENL [
    STRIP_TAC THEN MAP_EVERY Q.X_GEN_TAC [`a1`, `a2`] THEN STRIP_TAC THEN
    `?a1' a2'. RTC (x RUNION s) a1' a2' /\ (f a1' = f a1) /\ (f a2' = f a2)`
       by METIS_TAC [] THEN
    `RTC s a1 a1' /\ RTC s a2' a2` by METIS_TAC [] THEN
    `RTC (x RUNION s) a1 a1' /\ RTC (x RUNION s) a2' a2`
       by METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE, RUNION_COMM] THEN
    METIS_TAC [RTC_RTC],
    METIS_TAC []
  ]);

val note_prop10_1 = store_thm(
  "note_prop10_1",
  ``onto f /\ skernel s f /\ ofree s /\ full f x y ==>
    full f (RTC (x RUNION s)) (RTC y)``,
  SIMP_TAC (srw_ss()) [full_def, onto_def, ofree_def, skernel_def] THEN
  STRIP_TAC THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN CONJ_TAC THENL [
    METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE, RUNION_COMM],
    REPEAT STRIP_TAC THEN
    `?a0 a1'. x a0 a1' /\ (b1 = f a0) /\ (b1' = f a1')` by METIS_TAC [] THEN
    `RTC s a1' a1` by METIS_TAC [] THEN
    `RTC (x RUNION s) a1' a1`
      by METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE, RUNION_COMM] THEN
    `RTC (x RUNION s) a0 a1'` by METIS_TAC [chap3Theory.RUNION_RTC_MONOTONE,
                                            RTC_RULES] THEN
    METIS_TAC [RTC_RTC]
  ]);

val diagram_preservation = store_thm(
  "diagram_preservation",
  ``!R1 R2 h.
       onto h /\ (!n. Rhomo h (R1 n) (R2 n) /\ lrfull h (R1 n) (R2 n)) ==>
       !Fa G. eval Fa G R1 = eval Fa G R2``,
  SRW_TAC [][EQ_IMP_THM, onto_def, Rhomo_def, lrfull_def, eval_def] THEN
  `?invh. !b. h (invh b) = b` by METIS_TAC [SKOLEM_THM] THENL [
    `!g1 g2 n. Fa n g1 g2 ==> R1 n (invh (f g1)) (invh (f g2))`
        by (REPEAT STRIP_TAC THEN
            `R2 n (f g1) (f g2)` by METIS_TAC [] THEN
            `(f g1 = h (invh (f g1))) /\ (f g2 = h (invh (f g2)))`
                by SRW_TAC [][] THEN
            METIS_TAC []) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC ``(invh : 'c -> 'b) o (f : 'd -> 'c)``) THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `h o g` THEN SRW_TAC [][] THEN METIS_TAC [],

    FIRST_X_ASSUM (MP_TAC o SPEC ``(h : 'b -> 'c) o (f : 'd -> 'b)``) THEN
    SRW_TAC [][] THEN
    Q.EXISTS_TAC `invh o g` THEN SRW_TAC [][]
  ]);

val scollapse_def = Define`
  scollapse s f = !x y. s x y ==> (f x = f y)
`;

val Rhomo_structure_RTC = store_thm(
  "Rhomo_structure_RTC",
  ``Rhomo f R1 R2 /\ scollapse s f ==>
    Rhomo f (RTC (R1 RUNION s)) (RTC R2)``,
  SIMP_TAC (srw_ss()) [Rhomo_def, scollapse_def] THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][RTC_RULES, RUNION] THEN
  METIS_TAC [RTC_RULES]);

val _ = export_theory()
