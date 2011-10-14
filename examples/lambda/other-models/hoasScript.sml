open HolKernel boolLib bossLib Parse
open termTheory binderLib

val _ = new_theory "hoas"

val notexotic_def = Define`
  notexotic f = ?v t. f = \u. [u/v] t
`;



val lamfn_exists = prove(
  ``?f. !v t. f (LAM v t) = (\u. [u/v] t)``,
  Q.EXISTS_TAC `\t. @f. ?v N. (t = LAM v N) /\ (f = \u. [u/v]N)` THEN
  SRW_TAC [][] THEN SELECT_ELIM_TAC THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) [LAM_eq_thm] THEN
    SRW_TAC [][fresh_tpm_subst, lemma15a]
  ]);

val lamfn_def = new_specification("lamfn_def",
  ["lamfn"], lamfn_exists);

val lamfn_11 = store_thm(
  "lamfn_11",
  ``(lamfn (LAM u M) = lamfn (LAM v N)) ==> (LAM u M = LAM v N)``,
  SRW_TAC [][lamfn_def, FUN_EQ_THM, LAM_eq_thm] THEN
  Cases_on `u = v` THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `VAR v` MP_TAC) THEN SRW_TAC [][],
    `~(u IN FV N)` by
       (FIRST_X_ASSUM (Q.SPEC_THEN `VAR v` MP_TAC) THEN
        SRW_TAC [][] THEN SRW_TAC [][FV_SUB]) THEN
    SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `VAR u` MP_TAC) THEN
    SRW_TAC [][fresh_tpm_subst]
  ]);

val lamfn_inverse = prove(
  ``!f. notexotic f ==> ?M. (lamfn M = f) /\ ?v t. M = LAM v t``,
  SRW_TAC [boolSimps.DNF_ss][notexotic_def, lamfn_def] THEN
  METIS_TAC []);

val HOABS_def = new_specification(
  "HOABS_def",
  ["HOABS"],
  SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] lamfn_inverse);

val lamfn_HOABS = store_thm(
  "lamfn_HOABS",
  ``notexotic f ==> (lamfn (HOABS f) = f)``,
  METIS_TAC [HOABS_def]);

val HOABS_11 = store_thm(
  "HOABS_11",
  ``notexotic f /\ notexotic g ==> ((HOABS f = HOABS g) = (f = g))``,
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `lamfn`) THEN
  SRW_TAC [][HOABS_def]);

val HOABS_LAM = store_thm(
  "HOABS_LAM",
  ``HOABS (\u. [u/v]t) = LAM v t``,
  `notexotic (\u. [u/v]t)` by (SRW_TAC [][notexotic_def] THEN METIS_TAC []) THEN
  `lamfn (HOABS (\u. [u/v]t)) = (\u. [u/v]t)`
     by SRW_TAC [][lamfn_HOABS] THEN
  `lamfn (LAM v t) = (\u. [u/v]t)` by SRW_TAC [][lamfn_def] THEN
  `?u M. HOABS (\u. [u/v]t) = LAM u M` by METIS_TAC [HOABS_def] THEN
  METIS_TAC [lamfn_11]);

val notexotic_ID = store_thm(
  "notexotic_ID",
  ``notexotic (\x. x)``,
  SRW_TAC [][notexotic_def] THEN
  MAP_EVERY Q.EXISTS_TAC [`x`, `VAR x`] THEN
  SRW_TAC [][SUB_THM]);
val notexotic_K = store_thm(
  "notexotic_K",
  ``notexotic (\x. M)``,
  SRW_TAC [][notexotic_def] THEN
  Q_TAC (NEW_TAC "z") `FV M` THEN
  MAP_EVERY Q.EXISTS_TAC [`z`, `M`] THEN SRW_TAC [][lemma14b]);
val notexotic_app = store_thm(
  "notexotic_app",
  ``notexotic f /\ notexotic g ==> notexotic (\x. f x @@ g x)``,
  SRW_TAC [][notexotic_def] THEN SRW_TAC [][] THEN
  Cases_on `v = v'` THENL [
    MAP_EVERY Q.EXISTS_TAC [`v`, `t @@ t'`] THEN
    SRW_TAC [][SUB_THM],
    Q_TAC (NEW_TAC "z") `{v;v'} UNION FV t UNION FV t'` THEN
    MAP_EVERY Q.EXISTS_TAC [`z`, `[VAR z/v]t @@ [VAR z/v']t'`] THEN
    SRW_TAC [][SUB_THM, lemma15a]
  ]);
(*
val notexotic_abs = store_thm(
  "notexotic_abs",
  ``(!x. notexotic (f x)) ==> notexotic (\x. HOABS (f x))``,
  SRW_TAC [][notexotic_def] THEN
  SRW_TAC [][HOABS_LAM]);

val notexotic_example = prove(
  ``notexotic (\y. HOABS (\x. x @@ y))``,
  `!y. notexotic (\x. x @@ y)` by SRW_TAC [][notexotic_app, notexotic_K,
                                             notexotic_ID] THEN
  `!y. ?v t. HOABS (\x. x @@ y) = LAM v t` by METIS_TAC [HOABS_def] THEN
  `?bv bod. !y. HOABS (\x. x @@ y) = LAM (bv y) (bod y)`
     by METIS_TAC [SKOLEM_THM] THEN
  SRW_TAC [][FUN_EQ_THM] THEN

    SRW_TAC [][notexotic_def] THEN


  `!y. lamfn (HOABS (\x. x @@ y)) = (\x. x @@ y)`
         by SRW_TAC [][lamfn_HOABS] THEN
  `!v t. lamfn (LAM v t) = \u. [u/v] t` by SRW_TAC [][lamfn_def] THEN
  `(\x. x @@ y) = \u. [u/v]t` by METIS_TAC [lamfn_11] THEN
  `HOABS (\x. x @@ y) = HOABS (\u. [u/v] t)`
     by (POP_ASSUM (fn th => MP_TAC (Q.AP_TERM `HOABS` th) THEN
                             REWRITE_TAC [])) THEN
  POP_ASSUM SUBST_ALL_TAC THEN

  `HOABS (\x. x @@ y) = LAM x (VAR x @@ y)`
     by SRW_TAC [][GSYM HOABS_LAM, SUB_THM]


open chap3Theory
val beta_lemma = prove(
  ``notexotic f ==> beta (HOABS f @@ M) (f M)``,
  SRW_TAC [][notexotic_def] THEN SRW_TAC [][HOABS_LAM, beta_def] THEN
  METIS_TAC []);
*)

val _ = export_theory();
