open HolKernel boolLib Parse bossLib stringTheory arithmeticTheory markerLib;

val _ = new_theory "string_num"
val _ = set_grammar_ancestry ["string"]

val n2s_def = tDefine
 "n2s" `
  n2s n = if n = 0 then ""
          else let r0 = n MOD 256 in
               let r = if r0 = 0 then 256 else r0 in
               let s0 = n2s ((n - r) DIV 256)
               in
                 STRING (CHR (r - 1)) s0`
 (WF_REL_TAC `(<)` THEN REPEAT STRIP_TAC THEN
  Q.MATCH_ABBREV_TAC `M DIV 256 < n` THEN
  Q_TAC SUFF_TAC `M < n` THEN1
        (STRIP_TAC THEN MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
         Q.EXISTS_TAC `n DIV 256` THEN
         SRW_TAC [ARITH_ss][DIV_LESS] THEN
         MATCH_MP_TAC DIV_LE_MONOTONE THEN
         SRW_TAC [ARITH_ss][Abbr`M`]) THEN
  SRW_TAC [ARITH_ss][Abbr`M`]);

val s2n_def = Define`
  (s2n "" = 0) /\
  (s2n (STRING c s) = s2n s * 256 + ORD c + 1)
`;

val s2n_n2s = store_thm(
  "s2n_n2s",
  ``!n. s2n (n2s n) = n``,
  completeInduct_on `n` THEN ONCE_REWRITE_TAC [n2s_def] THEN
  SRW_TAC [][] THEN SRW_TAC [][s2n_def] THEN
  `n MOD 256 < 256` by SRW_TAC [][DIVISION] THEN
  `(n - r) DIV 256 < n`
      by (MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN
          Q.EXISTS_TAC `n DIV 256` THEN
          SRW_TAC [ARITH_ss][DIV_LE_MONOTONE,
                             DIV_LESS]) THEN
  `s2n s0 = (n - r) DIV 256` by (SRW_TAC [][Abbr`s0`]) THEN
  `r - 1 < 256`
     by (SRW_TAC [][Abbr`r`, Abbr`r0`] THEN
         DECIDE_TAC) THEN
  POP_ASSUM (fn th => SRW_TAC [][th]) THEN
  `0 < r` by SRW_TAC [ARITH_ss][Abbr`r`] THEN
  Cases_on `r0 = 0` THENL [
    `?q. n = q * 256`
        by METIS_TAC [DIVISION, ADD_CLAUSES,
                      DECIDE ``0 < 256``] THEN
    `~(q = 0)` by (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    `r = 256` by SRW_TAC [][Abbr`r`] THEN
    RM_ALL_ABBREVS_TAC THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    `q * 256 - 256 = (q - 1) * 256` by DECIDE_TAC THEN
    SRW_TAC [][MULT_DIV] THEN
    DECIDE_TAC,

    Q.UNABBREV_TAC `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    `(n - r0) DIV 256 = n DIV 256`
       by (MATCH_MP_TAC DIV_UNIQUE THEN
           Q.EXISTS_TAC `0` THEN
           SRW_TAC [][Abbr`r0`, SUB_RIGHT_EQ] THEN
           METIS_TAC [DECIDE ``0 < 256``, DIVISION, ADD_COMM]) THEN
    SRW_TAC [ARITH_ss][MULT_DIV, Abbr`r0`] THEN
    METIS_TAC [DECIDE ``0 < 256``, DIVISION, MULT_COMM]
  ]);

val n2s_s2n = store_thm(
  "n2s_s2n",
  ``n2s (s2n s) = s``,
  Induct_on `s` THEN ASM_SIMP_TAC (srw_ss()) [s2n_def, Once n2s_def] THEN
  Q.X_GEN_TAC `c` THEN SRW_TAC [][] THEN
  `r0 = (ORD c + 1) MOD 256`
     by (SRW_TAC [][Abbr`r0`] THEN
         SRW_TAC [][GSYM ADD_ASSOC, MOD_TIMES]) THEN
  RM_ABBREV_TAC "r0" THEN
  Cases_on `r0 = 0` THENL [
    `ORD c < 256` by SRW_TAC [][ORD_BOUND] THEN
    `?q. ORD c + 1 = q * 256`
       by METIS_TAC [DIVISION, ADD_CLAUSES, DECIDE ``0 < 256``] THEN
    `q = 1` by DECIDE_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `ORD c = 255` by DECIDE_TAC THEN
    `c = CHR 255` by METIS_TAC [CHR_ORD] THEN
    SRW_TAC [ARITH_ss][Abbr`r`, Abbr`s0`] THEN
    METIS_TAC [MULT_DIV, MULT_COMM, DECIDE ``0 < 256``],

    Q.UNABBREV_TAC `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    `ORD c + 1 < 256`
        by (SPOSE_NOT_THEN ASSUME_TAC THEN
            Q.SPEC_THEN `c` ASSUME_TAC ORD_BOUND THEN
            `ORD c = 255` by DECIDE_TAC THEN
            FULL_SIMP_TAC (srw_ss()) []) THEN
    FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [DIVISION, CHR_ORD] THEN
    METIS_TAC [MULT_COMM, MULT_DIV, DECIDE ``0 < 256``]
  ])

val n2s_11 = store_thm(
  "n2s_11",
  ``(n2s x = n2s y) = (x = y)``,
  METIS_TAC [s2n_n2s]);
val s2n_11 = store_thm(
  "s2n_11",
  ``(s2n x = s2n y) = (x = y)``,
  METIS_TAC [n2s_s2n]);

val n2s_onto = store_thm(
  "n2s_onto",
  ``!s. ?n. s = n2s n``,
  METIS_TAC [n2s_s2n]);

val s2n_onto = store_thm(
  "s2n_onto",
  ``!n. ?s. n = s2n s``,
  METIS_TAC [s2n_n2s]);


val _ = export_rewrites ["n2s_s2n", "s2n_n2s", "n2s_11", "s2n_11"]

val n2nsum_def = Define`
  n2nsum n = if ODD n then INL (n DIV 2) else INR (n DIV 2)
`;

val nsum2n_def = Define`
  (nsum2n (INL n) = 2 * n + 1) /\
  (nsum2n (INR n) = 2 * n)
`;
val _ = export_rewrites ["nsum2n_def"]

val div_lemma = prove(
  ``(2 * x DIV 2 = x) /\ ((2 * x + 1) DIV 2 = x)``,
  `0 < 2 /\ (1 DIV 2 = 0)` by simp[] >>
  metis_tac[MULT_DIV, ADD_DIV_ADD_DIV, MULT_COMM, ADD_CLAUSES]);

val odd_lemma = prove(
  ``(ODD x ==> (2 * (x DIV 2) + 1 = x)) /\
    (~ODD x ==> (2 * (x DIV 2) = x))``,
  conj_tac
  >- dsimp[ODD_EXISTS, ADD1, div_lemma]
  >- dsimp[GSYM EVEN_ODD, EVEN_EXISTS, div_lemma])

val n2nsum_nsum2n = store_thm(
  "n2nsum_nsum2n[simp]",
  ``n2nsum (nsum2n ns) = ns``,
  Cases_on `ns` >> simp[n2nsum_def, div_lemma, ODD_ADD, ODD_MULT]);

val nsum2n_n2nsum = store_thm(
  "nsum2n_n2nsum[simp]",
  ``nsum2n (n2nsum n) = n``,
  rw[n2nsum_def, odd_lemma]);

val s2ssum_def = Define`
  s2ssum s = SUM_MAP n2s n2s (n2nsum (s2n s))
`;

val ssum2s_def = Define`
  ssum2s sm = n2s (nsum2n (SUM_MAP s2n s2n sm))
`;

val sumpp_compose = prove(
  ``SUM_MAP f g (SUM_MAP a b x) = SUM_MAP (f o a) (g o b) x``,
  Cases_on `x` >> simp[]);

val sumpp_I = prove(
  ``SUM_MAP (\x. x) (\x. x) y = y``,
  Cases_on `y` >> simp[]);

val s2ssum_ssum2s = store_thm(
  "s2ssum_ssum2s[simp]",
  ``s2ssum (ssum2s sm) = sm``,
  simp[s2ssum_def, ssum2s_def, sumpp_compose, combinTheory.o_DEF, sumpp_I]);

val ssum2s_s2ssum = store_thm(
  "ssum2s_s2ssum[simp]",
  ``ssum2s (s2ssum s) = s``,
  simp[s2ssum_def, ssum2s_def, sumpp_compose, combinTheory.o_DEF, sumpp_I]);


val _ = export_theory()
