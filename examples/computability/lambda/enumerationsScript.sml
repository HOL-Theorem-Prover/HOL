open HolKernel Parse boolLib bossLib
open pure_dBTheory numpairTheory

val _ = set_trace "Unicode" 1
val _ = new_theory "enumerations"

(* ---------------------------------------------------------------------- 
    A computable bijection between the natural numbers and all dB terms 
   ---------------------------------------------------------------------- *)

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val dBnum_def = Define`
  (dBnum (dV i) = 3 * i) ∧
  (dBnum (dAPP M N) = 3 * (dBnum M ⊗ dBnum N) + 1) ∧
  (dBnum (dABS M) = 3 * dBnum M + 2)
`;

val mod3 = prove(
  ``((3 * n) MOD 3 = 0) ∧ (r < 3 ⇒ ((3 * n + r) MOD 3 = r))``,
  CONJ_TAC THENL [
    ONCE_REWRITE_TAC [arithmeticTheory.MULT_COMM] THEN 
    SRW_TAC [][arithmeticTheory.MOD_EQ_0],
    METIS_TAC [arithmeticTheory.MULT_COMM, arithmeticTheory.MOD_MULT]
  ]);

val div3 = prove(
  ``((3 * n) DIV 3 = n) ∧ (r < 3 ⇒ ((3 * n + r) DIV 3 = n))``,
  CONJ_TAC THENL [
    ONCE_REWRITE_TAC [arithmeticTheory.MULT_COMM] THEN 
    SRW_TAC [][arithmeticTheory.MULT_DIV],
    METIS_TAC [arithmeticTheory.MULT_COMM, arithmeticTheory.DIV_MULT]
  ]);
                   
val mult3_ineqs = prove(
  ``(3 * n ≠ 3 * m + 1) ∧
    (3 * n ≠ 3 * m + 2) ∧
    (3 * n + 1 ≠ 3 * m + 2)``,
  REPEAT STRIP_TAC THEN 
  POP_ASSUM (MP_TAC o Q.AP_TERM `λn. n MOD 3`) THEN 
  SRW_TAC [][mod3]);

val dBnum_11 = Store_thm(
  "dBnum_11",
  ``∀t u. (dBnum t = dBnum u) ⇔ (t = u)``,
  Induct THEN Cases_on `u` THEN 
  SRW_TAC [ARITH_ss][dBnum_def, arithmeticTheory.EQ_MULT_LCANCEL, 
                     mult3_ineqs]);

val numdB_def = TotalDefn.tDefine "numdB" 
  `numdB n = if n MOD 3 = 0 then dV (n DIV 3)
            else if n MOD 3 = 1 then 
              dAPP (numdB (nfst (n DIV 3))) (numdB (nsnd (n DIV 3)))
            else dABS (numdB (n DIV 3))`
  (WF_REL_TAC `$<` THEN REPEAT STRIP_TAC THENL [
    MATCH_MP_TAC arithmeticTheory.DIV_LESS THEN SRW_TAC [][] THEN 
    Q_TAC SUFF_TAC `n ≠ 0` THEN1 DECIDE_TAC THEN STRIP_TAC THEN 
    FULL_SIMP_TAC (srw_ss())[],
    
    Q_TAC SUFF_TAC `n DIV 3 < n` 
      THEN1 (ASSUME_TAC (Q.INST [`n` |-> `n DIV 3`] nfst_le) THEN 
             DECIDE_TAC) THEN 
    MATCH_MP_TAC arithmeticTheory.DIV_LESS THEN SRW_TAC [][] THEN 
    Q_TAC SUFF_TAC `n ≠ 0` THEN1 DECIDE_TAC THEN STRIP_TAC THEN 
    FULL_SIMP_TAC (srw_ss())[],

    Q_TAC SUFF_TAC `n DIV 3 < n` 
      THEN1 (ASSUME_TAC (Q.INST [`n` |-> `n DIV 3`] nsnd_le) THEN 
             DECIDE_TAC) THEN 
    MATCH_MP_TAC arithmeticTheory.DIV_LESS THEN SRW_TAC [][] THEN 
    Q_TAC SUFF_TAC `n ≠ 0` THEN1 DECIDE_TAC THEN STRIP_TAC THEN 
    FULL_SIMP_TAC (srw_ss())[]
  ]);
val numdB_ind = theorem "numdB_ind"

val numdBnum = Store_thm(
  "numdBnum",
  ``∀t. numdB (dBnum t) = t``,
  Induct_on `t` THEN 
  SRW_TAC [][dBnum_def, Once numdB_def, mod3, div3]);

val dBnumdB = Store_thm(
  "dBnumdB",
  ``∀n. dBnum (numdB n) = n``,
  HO_MATCH_MP_TAC numdB_ind THEN REPEAT STRIP_TAC THEN 
  Cases_on `n MOD 3 = 0` THENL [
    SRW_TAC [][Once numdB_def, dBnum_def] THEN 
    METIS_TAC [DECIDE ``0 < 3``, arithmeticTheory.DIVISION,
               arithmeticTheory.MULT_COMM, DECIDE ``x + 0 = x``],
    ALL_TAC 
  ] THEN 
  Cases_on `n MOD 3 = 1` THENL [
    SRW_TAC [][Once numdB_def, dBnum_def] THEN 
    METIS_TAC [DECIDE ``0 < 3``, arithmeticTheory.DIVISION,
               arithmeticTheory.MULT_COMM],
    ALL_TAC
  ] THEN 
  SRW_TAC [][Once numdB_def, dBnum_def] THEN 
  `n MOD 3 < 3` by METIS_TAC [arithmeticTheory.DIVISION, DECIDE ``0 < 3``] THEN
  `n MOD 3 = 2` by DECIDE_TAC THEN 
  METIS_TAC [DECIDE ``0 < 3``, arithmeticTheory.DIVISION,
             arithmeticTheory.MULT_COMM]);

val numdB_11 = Store_thm(
  "numdB_11",
  ``(numdB n = numdB m) ⇔ (n = m)``,
  METIS_TAC [dBnumdB]);

val numdB_onto = store_thm(
  "numdB_onto",
  ``∀t. ∃n. numdB n = t``,
  METIS_TAC [numdBnum]);
val dBnum_onto = store_thm(
  "dBnum_onto",
  ``∀n. ∃t. dBnum t = n``,
  METIS_TAC [dBnumdB]);

val _ = export_theory();

  


    




