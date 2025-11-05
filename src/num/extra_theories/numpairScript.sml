Theory numpair[bare]
Ancestors
  arithmetic
Libs
  HolKernel boolLib Parse BasicProvers TotalDefn numSimps numLib
  simpLib metisLib

fun fs ths = FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) ths
fun simp ths = ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) ths
val metis_tac = METIS_TAC

(* ----------------------------------------------------------------------
    Triangular numbers
   ---------------------------------------------------------------------- *)

Definition tri_def[nocompute,simp]:
  (tri 0 = 0) /\
  (tri (SUC n) = SUC n + tri n)
End

Theorem twotri_formula:
    2 * tri n = n * (n + 1)
Proof
  Induct_on `n` THEN
  SRW_TAC [ARITH_ss][tri_def, MULT_CLAUSES, LEFT_ADD_DISTRIB]
QED

Theorem tri_formula[compute]:
  tri n = (n * (n + 1)) DIV 2
Proof
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN MATCH_MP_TAC DIV_UNIQUE THEN
  Q.EXISTS_TAC `0` THEN SRW_TAC [ARITH_ss][twotri_formula]
QED

Theorem tri_eq_0[simp]:
  ((tri n = 0) <=> (n = 0)) /\ ((0 = tri n) <=> (n = 0))
Proof
  Cases_on `n` THEN SRW_TAC [ARITH_ss][tri_def]
QED

val DECIDE_TAC = SRW_TAC [ARITH_ss][]
Theorem tri_LT_I:
    !n m. n < m ==> tri n < tri m
Proof
  Induct THEN Cases_on `m` THEN SRW_TAC [ARITH_ss][tri_def] THEN
  RES_TAC THEN DECIDE_TAC
QED

Theorem tri_LT[simp]:
  !n m. tri n < tri m <=> n < m
Proof
  SRW_TAC [][EQ_IMP_THM, tri_LT_I] THEN
  SPOSE_NOT_THEN ASSUME_TAC THEN
  `(n = m) \/ m < n` by DECIDE_TAC THEN1 FULL_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [prim_recTheory.LESS_REFL, tri_LT_I, LESS_TRANS]
QED

Theorem tri_11[simp]:
  !m n. (tri m = tri n) <=> (m = n)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  `m < n \/ n < m \/ (m = n)` by DECIDE_TAC THEN
  METIS_TAC [tri_LT_I, prim_recTheory.LESS_REFL]
QED

Theorem tri_LE[simp]:
  !m n. tri m <= tri n <=> m <= n
Proof
  SRW_TAC [][LESS_OR_EQ]
QED

Definition invtri0_def:
  invtri0 n a = if n < a + 1 then (n,a)
                else invtri0 (n - (a + 1)) (a + 1)
End

Definition invtri_def:  invtri n = SND (invtri0 n 0)
End
val _ = Unicode.unicode_version {tmnm = "invtri",
                                 u = "tri"^UnicodeChars.sup_minus^
                                     UnicodeChars.sup_1}

Theorem invtri0_thm:
    !n a. tri (SND (invtri0 n a)) + FST (invtri0 n a) = n + tri a
Proof
  HO_MATCH_MP_TAC (theorem "invtri0_ind") THEN SRW_TAC [][] THEN
  Cases_on `n < a + 1` THEN
  ONCE_REWRITE_TAC [invtri0_def] THEN SRW_TAC [ARITH_ss][] THEN
  SRW_TAC [ARITH_ss][GSYM ADD1, tri_def]
QED

Theorem SND_invtri0:
    !n a. FST (invtri0 n a) < SUC (SND (invtri0 n a))
Proof
  HO_MATCH_MP_TAC (theorem "invtri0_ind") THEN SRW_TAC [][] THEN
  Cases_on `n < a + 1` THEN ONCE_REWRITE_TAC [invtri0_def] THEN
  SRW_TAC [ARITH_ss][]
QED

Theorem invtri_lower:
    tri (invtri n) <= n
Proof
  SRW_TAC [][invtri_def] THEN
  Q.SPECL_THEN [`n`, `0`] MP_TAC invtri0_thm THEN
  SRW_TAC [ARITH_ss][tri_def]
QED

Theorem invtri_upper:
    n < tri (invtri n + 1)
Proof
  SRW_TAC [][invtri_def, GSYM ADD1, tri_def] THEN
  Q.SPECL_THEN [`n`, `0`] MP_TAC invtri0_thm THEN
  Q.SPECL_THEN [`n`, `0`] MP_TAC SND_invtri0 THEN
  SRW_TAC [ARITH_ss][tri_def]
QED

Theorem invtri_linverse[simp]:
  invtri (tri n) = n
Proof
  MAP_EVERY (MP_TAC o Q.INST [`n` |-> `tri n`])
            [invtri_upper, invtri_lower] THEN
  SRW_TAC [ARITH_ss][]
QED

Theorem invtri_unique:
    tri y <= n /\ n < tri (y + 1) ==> (invtri n = y)
Proof
  STRIP_TAC THEN MAP_EVERY ASSUME_TAC [invtri_lower, invtri_upper] THEN
  `invtri n < y \/ (invtri n = y) \/ y < invtri n` by DECIDE_TAC THENL [
     `invtri n + 1 <= y` by DECIDE_TAC THEN
     `tri (invtri n + 1) <= tri y` by SRW_TAC [][] THEN
     DECIDE_TAC,
     `y + 1 <= invtri n` by DECIDE_TAC THEN
     `tri (y + 1) <= tri (invtri n)` by SRW_TAC [][] THEN
     DECIDE_TAC
  ]
QED

Theorem invtri_linverse_r:
    y <= x ==> (invtri (tri x + y) = x)
Proof
  STRIP_TAC THEN MATCH_MP_TAC invtri_unique THEN
  SRW_TAC [ARITH_ss][GSYM ADD1, tri_def]
QED

Theorem tri_le:
    n <= tri n
Proof
  Induct_on `n` THEN SRW_TAC [][tri_def]
QED

Theorem invtri_le:
    invtri n <= n
Proof
  Q_TAC SUFF_TAC `tri (invtri n) <= tri n` THEN1 SRW_TAC [][] THEN
  METIS_TAC [tri_le, invtri_lower, arithmeticTheory.LESS_EQ_TRANS]
QED





(* ----------------------------------------------------------------------
    Numeric pair, fst and snd
   ---------------------------------------------------------------------- *)

Definition npair_def:
  npair m n = tri (m + n) + n
End

val _ = set_fixity "*," (Infixr 601)
val _ = Unicode.unicode_version {tmnm = "*,", u = UTF8.chr 0x2297 (* \otimes *)}
Overload "*," = ``npair``
val _ = TeX_notation {TeX = ("\\ensuremath{\\otimes}", 1), hol = "*,"}
val _ = TeX_notation {TeX = ("\\ensuremath{\\otimes}", 1),
                      hol = UTF8.chr 0x2297}


Definition nfst_def:
  nfst n = tri (invtri n) + invtri n - n
End

Definition nsnd_def:
  nsnd n = n - tri (invtri n)
End

Theorem nfst_npair[simp]:
  nfst (x *, y) = x
Proof
  SRW_TAC [][nfst_def, npair_def] THEN
  SRW_TAC [ARITH_ss][invtri_linverse_r]
QED

Theorem nsnd_npair[simp]:
  nsnd (x *, y) = y
Proof
  SRW_TAC [][nsnd_def, npair_def] THEN
  SRW_TAC [ARITH_ss][invtri_linverse_r]
QED

Theorem npair_cases:
    !n. ?x y. n = (x *, y)
Proof
  STRIP_TAC THEN MAP_EVERY Q.EXISTS_TAC [`nfst n`, `nsnd n`] THEN
  SRW_TAC [][nsnd_def, nfst_def, npair_def] THEN
  `n <= tri (invtri n) + invtri n`
     by (ASSUME_TAC invtri_upper THEN
         FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [GSYM ADD1, tri_def]) THEN
  ASSUME_TAC invtri_lower THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
QED

Theorem npair[simp]:
  !n. (nfst n *, nsnd n) = n
Proof
  STRIP_TAC THEN Q.SPEC_THEN `n` STRUCT_CASES_TAC npair_cases THEN
  SRW_TAC [][]
QED

Theorem npair_11[simp]:
  (x1 *, y1 = x2 *, y2) <=> (x1 = x2) /\ (y1 = y2)
Proof
  SRW_TAC [][EQ_IMP_THM] THENL [
    POP_ASSUM (MP_TAC o Q.AP_TERM `nfst`) THEN SRW_TAC [][],
    POP_ASSUM (MP_TAC o Q.AP_TERM `nsnd`) THEN SRW_TAC [][]
  ]
QED

Theorem nfst_le:
    nfst n <= n
Proof
  SRW_TAC [][nfst_def] THEN
  MAP_EVERY ASSUME_TAC [invtri_lower, invtri_le] THEN
  DECIDE_TAC
QED
Theorem nsnd_le:   nsnd n <= n
Proof SRW_TAC [][nsnd_def]
QED

Theorem npair00[simp]:
  npair 0 0 = 0
Proof
  SIMP_TAC (srw_ss()) [npair_def]
QED

Theorem npair_EQ_0[simp]:
  !x y. (npair x y = 0) <=> (x = 0) /\ (y = 0)
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
  !m n. n <= npair n m
Proof
  rpt gen_tac \\
  `n = nfst (npair n m)` by simp[GSYM nfst_npair] >>
  `nfst (npair n m) <= npair n m` by simp[nfst_le] >> fs[]
QED

Theorem nsnd_le_npair[simp]:
  !m n. m <= npair n m
Proof
  rpt gen_tac \\
  `m = nsnd (npair n m)` by simp[GSYM nsnd_npair] >>
  `nsnd (npair n m) <= npair n m` by simp[nsnd_le] >> fs[]
QED

Theorem npair2_lt_E:
  !n n1 n2. npair n n1 < npair n n2 ==> n1 < n2
Proof
  rpt gen_tac
  >> simp[npair_def] >> strip_tac >> SPOSE_NOT_THEN ASSUME_TAC
  >> `n1 >= n2` by simp[]
  >> `n + n1 >= n + n2` by simp[]
  >> `n + n2 <= n + n1` by simp[]
  >> `tri (n + n2) <= tri (n + n1)` by metis_tac[tri_LE]
  >> `n2 <= n1` by simp[]
  >> `n2 + tri (n + n2) <= n1 + tri (n + n1)` by simp[]
  >> fs[]
QED

Theorem npair2_lt_I:
  !n n1 n2. n1 < n2 ==> npair n n1 < npair n n2
Proof
  rpt strip_tac >> simp[npair_def] >>
  `n + n1 < n + n2` by simp[] >>
  `tri (n + n1) < tri (n + n2)` by simp[tri_LT] >> simp[]
QED

Theorem npair2_lt[simp]:
  !n n1 n2. npair n n1 < npair n n2 <=> n1 < n2
Proof
  metis_tac[npair2_lt_E, npair2_lt_I]
QED

(* slightly more general than npair2_lt_I *)
Theorem npairs_lt_I :
  !a b c d. a <= b /\ c < d ==> npair a c < npair b d
Proof
    rpt STRIP_TAC
 >> `(a = b) \/ a < b` by SRW_TAC [ARITH_ss] []
 >- (ASM_REWRITE_TAC [] \\
     MATCH_MP_TAC npair2_lt_I >> simp [])
 >> MATCH_MP_TAC LESS_TRANS
 >> Q.EXISTS_TAC ‘npair a d’
 >> CONJ_TAC >- (MATCH_MP_TAC npair2_lt_I >> ASM_REWRITE_TAC [])
 >> REWRITE_TAC [npair_def]
 >> Q_TAC SUFF_TAC `tri (a + d) < tri (b + d)`
 >- SRW_TAC [ARITH_ss] []
 >> MATCH_MP_TAC tri_LT_I
 >> SRW_TAC [ARITH_ss] []
QED
