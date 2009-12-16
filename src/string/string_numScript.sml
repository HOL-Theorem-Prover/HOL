open HolKernel boolLib Parse bossLib stringTheory arithmeticTheory markerLib;

val _ = new_theory "string_num"

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


val _ = export_theory()
