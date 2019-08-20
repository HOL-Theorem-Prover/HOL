open HolKernel boolLib Parse

open arithmeticTheory BasicProvers TotalDefn
     numSimps numLib simpLib metisLib

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]
fun fs ths = FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) ths
fun simp ths = ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) ths
val metis_tac = METIS_TAC

val _ = new_theory "numpair"

(* ----------------------------------------------------------------------
    Triangular numbers
   ---------------------------------------------------------------------- *)

Definition tri_def[nocompute,simp]:
  (tri 0 = 0) /\
  (tri (SUC n) = SUC n + tri n)
End

val twotri_formula = store_thm(
  "twotri_formula",
  ``2 * tri n = n * (n + 1)``,
  Induct_on `n` THEN
  SRW_TAC [ARITH_ss][tri_def, MULT_CLAUSES, LEFT_ADD_DISTRIB]);

Theorem tri_formula[compute]:
  tri n = (n * (n + 1)) DIV 2
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC DIV_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][twotri_formula]
QED

val tri_eq_0 = Store_thm(
  "tri_eq_0",
  ``((tri n = 0) <=> (n = 0)) /\ ((0 = tri n) <=> (n = 0))``,
  Cases_on `n` THEN SRW_TAC [ARITH_ss][tri_def]);

val DECIDE_TAC = SRW_TAC [ARITH_ss][]
val tri_LT_I = store_thm(
  "tri_LT_I",
  ``!n m. n < m ==> tri n < tri m``,
  Induct THEN Cases_on `m` THEN SRW_TAC [ARITH_ss][tri_def] THEN
  RES_TAC THEN DECIDE_TAC);

val tri_LT = Store_thm(
  "tri_LT",
  ``!n m. tri n < tri m <=> n < m``,
  SRW_TAC [][EQ_IMP_THM, tri_LT_I] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `(n = m) \/ m < n` by DECIDE_TAC THEN1 FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [prim_recTheory.LESS_REFL, tri_LT_I, LESS_TRANS]);

val tri_11 = Store_thm(
  "tri_11",
  ``!m n. (tri m = tri n) <=> (m = n)``,
  SRW_TAC [][EQ_IMP_THM] THEN
  `m < n \/ n < m \/ (m = n)` by DECIDE_TAC THEN
  METIS_TAC [tri_LT_I, prim_recTheory.LESS_REFL]);

val tri_LE = Store_thm(
  "tri_LE",
  ``!m n. tri m <= tri n <=> m <= n``,
  SRW_TAC [][LESS_OR_EQ]);

val invtri0_def = Define`
  invtri0 n a = if n < a + 1 then (n,a)
                else invtri0 (n - (a + 1)) (a + 1)
`;

val invtri_def = Define`invtri n = SND (invtri0 n 0)`;
val _ = Unicode.unicode_version {tmnm = "invtri",
                                 u = "tri"^UnicodeChars.sup_minus^
                                     UnicodeChars.sup_1}

val invtri0_thm = store_thm(
  "invtri0_thm",
  ``!n a. tri (SND (invtri0 n a)) + FST (invtri0 n a) = n + tri a``,
  HO_MATCH_MP_TAC (theorem "invtri0_ind") THEN SRW_TAC [][] THEN
  Cases_on `n < a + 1` THEN
  ONCE_REWRITE_TAC [invtri0_def] THEN SRW_TAC [ARITH_ss][] THEN
  SRW_TAC [ARITH_ss][GSYM ADD1, tri_def]);

val SND_invtri0 = store_thm(
  "SND_invtri0",
  ``!n a. FST (invtri0 n a) < SUC (SND (invtri0 n a))``,
  HO_MATCH_MP_TAC (theorem "invtri0_ind") THEN SRW_TAC [][] THEN
  Cases_on `n < a + 1` THEN ONCE_REWRITE_TAC [invtri0_def] THEN
  SRW_TAC [ARITH_ss][]);

val invtri_lower = store_thm(
  "invtri_lower",
  ``tri (invtri n) <= n``,
  SRW_TAC [][invtri_def] THEN
  Q.SPECL_THEN [`n`, `0`] MP_TAC invtri0_thm THEN
  SRW_TAC [ARITH_ss][tri_def]);

val invtri_upper = store_thm(
  "invtri_upper",
  ``n < tri (invtri n + 1)``,
  SRW_TAC [][invtri_def, GSYM ADD1, tri_def] THEN
  Q.SPECL_THEN [`n`, `0`] MP_TAC invtri0_thm THEN
  Q.SPECL_THEN [`n`, `0`] MP_TAC SND_invtri0 THEN
  SRW_TAC [ARITH_ss][tri_def]);

val invtri_linverse = Store_thm(
  "invtri_linverse",
  ``invtri (tri n) = n``,
  MAP_EVERY (MP_TAC o Q.INST [`n` |-> `tri n`])
            [invtri_upper, invtri_lower] THEN
  SRW_TAC [ARITH_ss][]);

val invtri_unique = store_thm(
  "invtri_unique",
  ``tri y <= n /\ n < tri (y + 1) ==> (invtri n = y)``,
  STRIP_TAC THEN MAP_EVERY ASSUME_TAC [invtri_lower, invtri_upper] THEN
  `invtri n < y \/ (invtri n = y) \/ y < invtri n` by DECIDE_TAC THENL [
     `invtri n + 1 <= y` by DECIDE_TAC THEN
     `tri (invtri n + 1) <= tri y` by SRW_TAC [][] THEN
     DECIDE_TAC,
     `y + 1 <= invtri n` by DECIDE_TAC THEN
     `tri (y + 1) <= tri (invtri n)` by SRW_TAC [][] THEN
     DECIDE_TAC
  ]);

val invtri_linverse_r = store_thm(
  "invtri_linverse_r",
  ``y <= x ==> (invtri (tri x + y) = x)``,
  STRIP_TAC THEN MATCH_MP_TAC invtri_unique THEN
  SRW_TAC [ARITH_ss][GSYM ADD1, tri_def]);

val tri_le = store_thm(
  "tri_le",
  ``n <= tri n``,
  Induct_on `n` THEN SRW_TAC [][tri_def]);

val invtri_le = store_thm(
  "invtri_le",
  ``invtri n <= n``,
  Q_TAC SUFF_TAC `tri (invtri n) <= tri n` THEN1 SRW_TAC [][] THEN
  METIS_TAC [tri_le, invtri_lower, arithmeticTheory.LESS_EQ_TRANS]);





(* ----------------------------------------------------------------------
    Numeric pair, fst and snd
   ---------------------------------------------------------------------- *)

val npair_def = Define`
  npair m n = tri (m + n) + n
`;

val _ = set_fixity "*," (Infixr 601)
val _ = Unicode.unicode_version {tmnm = "*,", u = UTF8.chr 0x2297 (* \otimes *)}
val _ = overload_on ("*,", ``npair``)
val _ = TeX_notation {TeX = ("\\ensuremath{\\otimes}", 1), hol = "*,"}
val _ = TeX_notation {TeX = ("\\ensuremath{\\otimes}", 1),
                      hol = UTF8.chr 0x2297}


val nfst_def = Define`
  nfst n = tri (invtri n) + invtri n - n
`;

val nsnd_def = Define`
  nsnd n = n - tri (invtri n)
`;

val nfst_npair = Store_thm(
  "nfst_npair",
  ``nfst (x *, y) = x``,
  SRW_TAC [][nfst_def, npair_def] THEN
  SRW_TAC [ARITH_ss][invtri_linverse_r]);

val nsnd_npair = Store_thm(
  "nsnd_npair",
  ``nsnd (x *, y) = y``,
  SRW_TAC [][nsnd_def, npair_def] THEN
  SRW_TAC [ARITH_ss][invtri_linverse_r]);

val npair_cases = store_thm(
  "npair_cases",
  ``!n. ?x y. n = (x *, y)``,
  STRIP_TAC THEN MAP_EVERY Q.EXISTS_TAC [`nfst n`, `nsnd n`] THEN
  SRW_TAC [][nsnd_def, nfst_def, npair_def] THEN
  `n <= tri (invtri n) + invtri n`
     by (ASSUME_TAC invtri_upper THEN
         FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [GSYM ADD1, tri_def]) THEN
  ASSUME_TAC invtri_lower THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []);

val npair = Store_thm(
  "npair",
  ``!n. (nfst n *, nsnd n) = n``,
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC npair_cases THEN
  SRW_TAC [][]);

val npair_11 = Store_thm(
  "npair_11",
  ``(x1 *, y1 = x2 *, y2) <=> (x1 = x2) /\ (y1 = y2)``,
  SRW_TAC [][EQ_IMP_THM] THENL [
    POP_ASSUM (MP_TAC o Q.AP_TERM `nfst`) THEN SRW_TAC [][],
    POP_ASSUM (MP_TAC o Q.AP_TERM `nsnd`) THEN SRW_TAC [][]
  ]);

val nfst_le = store_thm(
  "nfst_le",
  ``nfst n <= n``,
  SRW_TAC [][nfst_def] THEN
  MAP_EVERY ASSUME_TAC [invtri_lower, invtri_le] THEN
  DECIDE_TAC);
val nsnd_le = store_thm("nsnd_le", ``nsnd n <= n``, SRW_TAC [][nsnd_def]);

Theorem npair00[simp]:
  npair 0 0 = 0
Proof
  SIMP_TAC (srw_ss()) [npair_def]
QED

Theorem npair_EQ_0[simp]:
  (npair x y = 0) <=> (x = 0) /\ (y = 0)
Proof
  METIS_TAC[npair00,npair_11]
QED

Theorem nfst0[simp]:
  nfst 0 = 0
Proof
  METIS_TAC[nfst_npair, npair00, npair_11]
QED

Theorem nsnd0[simp]:
  nsnd 0 = 0
Proof
  METIS_TAC[nsnd_npair, npair00, npair_11]
QED

Theorem nfst_le_npair[simp]:
  n <= npair n m
Proof
  `n = nfst (npair n m)` by simp[GSYM nfst_npair] >>
  `nfst (npair n m) <= npair n m` by simp[nfst_le] >> fs[]
QED

Theorem nsnd_le_npair[simp]:
  m <= npair n m
Proof
  `m = nsnd (npair n m)` by simp[GSYM nsnd_npair] >>
  `nsnd (npair n m) <= npair n m` by simp[nsnd_le] >> fs[]
QED

Theorem npair2_lt_E:
  npair n n1 < npair n n2 ==> n1 < n2
Proof
  simp[npair_def] >> strip_tac >> SPOSE_NOT_THEN ASSUME_TAC
  >> `n1 >= n2` by simp[]
  >> `n + n1 >= n + n2` by simp[]
  >> `n + n2 <= n + n1` by simp[]
  >> `tri (n + n2) <= tri (n + n1)` by metis_tac[tri_LE]
  >> `n2 <= n1` by simp[]
  >> `n2 + tri (n + n2) <= n1 + tri (n + n1)` by simp[]
  >> fs[]
QED


Theorem npair2_lt_I:
  n1 < n2 ==> npair n n1 < npair n n2
Proof
  rpt strip_tac >> simp[npair_def] >>
  `n + n1 < n + n2` by simp[] >>
  `tri (n + n1) < tri (n + n2)` by simp[tri_LT] >> simp[]
QED

Theorem npair2_lt[simp]:
  npair n n1 < npair n n2 <=> n1 < n2
Proof
  metis_tac[npair2_lt_E, npair2_lt_I]
QED

val _ = export_theory()
