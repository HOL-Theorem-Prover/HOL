(* ========================================================================= *)
(* Determinant and trace of a square matrix.                                 *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*        (c) Copyright, Liming Li, Yong Guan and Zhiping Shi 2011           *)
(*                                                                           *)
(*   Ported to HOL4 by Chun Tian, on (July 1, 2023)                          *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory boolTheory
     PairedLambda pred_setLib fcpTheory fcpLib tautLib numLib realTheory
     realLib InductiveDefinition hurdUtils;

open permutationTheory iterateTheory vectorTheory vectorLib matrixTheory;

open Q;

val _ = new_theory "determinant";

Overload PRODUCT[local]  = “iterate$product”
Overload SUM[local]      = “iterate$Sum”
Overload SIGN[local]     = “permutation$sign”
Overload SWAP[local]     = “permutation$swap”
Overload INVERSE[local]  = “permutation$inverse”
Overload PERMUTES[local] = “permutation$permutes”
Overload VSUM[local]     = “vector$vsum”
Overload TRANSP[local]   = “matrix$transp”
Overload MAT[local]      = “matrix$mat”
Overload ROW[local]      = “matrix$row”
Overload ROWS[local]     = “matrix$rows”
Overload COLUMN[local]   = “matrix$column”
Overload COLUMNS[local]  = “matrix$columns”
Overload VECTOR_0[local] = “vector$vec 0”

val SUM_EQ       = iterateTheory.SUM_EQ';
val SUM_EQ_0     = iterateTheory.SUM_EQ_0';
val SUM_ADD      = iterateTheory.SUM_ADD';
val SWAP_DEF     = permutationTheory.swap_def;
val PERMUTES_DEF = permutationTheory.permutes;
val VSUM_DEF     = vectorTheory.vsum_def;
val TRANSP_DEF   = matrixTheory.transp_def;
val MAT_DEF      = matrixTheory.mat_def;
val ROW_DEF      = matrixTheory.row_def;
val ROWS_DEF     = matrixTheory.rows_def;
val COLUMN_DEF   = matrixTheory.column_def;
val COLUMNS_DEF  = matrixTheory.columns_def;
val EQ_IMP       = SPECL [‘a’, ‘b’] boolTheory.EQ_IMPLIES;

(* exceptions from Q *)
val ASSUME = Thm.ASSUME;
val AP_TERM = Thm.AP_TERM;

Theorem LT_REFL :
    !n:num. ~(n < n)
Proof
    rw []
QED

(* prioritize_real() *)
val _ = prefer_real();

(* ------------------------------------------------------------------------- *)
(* Definition of determinant.                                                *)
(* ------------------------------------------------------------------------- *)

Definition det_def :
  det (A:real['N]['N]) =
        SUM { p | p PERMUTES count(dimindex (:'N))}
            (\p. SIGN(p) * (PRODUCT (count(dimindex (:'N))) (\i. A ' i '(p i))))
End

Overload DET[local] = “det”
val DET_DEF = det_def

Definition alg_comp_def :
  (alg_comp:real['N]['N]-> num -> num -> real) A i j =
                DET ((FCP k l. if k = i then (if l = j then &1 else &0) else
                                (if l = j then &0 else A ' k ' l)):real['N]['N])
End

Overload ALG_COMP[local] = “alg_comp”
val ALG_COMP_DEF = alg_comp_def;

(* ------------------------------------------------------------------------- *)
(* A few general lemmas we need below.                                       *)
(* ------------------------------------------------------------------------- *)

Theorem IN_DIMINDEX_SWAP :
   !m n j. m < dimindex(:'N) /\ n < dimindex(:'N) /\ j < dimindex(:'N)
           ==> SWAP(m,n) j < dimindex(:'N)
Proof
  REWRITE_TAC[SWAP_DEF] THEN ARITH_TAC
QED

Theorem FCP_BETA_PERM :
   !g p i. p PERMUTES count(dimindex (:'N)) /\ i < dimindex(:'N)
         ==> (((FCP) g : 'a ** 'N) ' (p i) = g(p i))
Proof
  PROVE_TAC[FCP_BETA, PERMUTES_IN_IMAGE, IN_COUNT]
QED

(* ------------------------------------------------------------------------- *)
(* Basic determinant properties.                                             *)
(* ------------------------------------------------------------------------- *)

Theorem DET_TRANSP :
   !A:real['N]['N]. DET (TRANSP A) = DET A
Proof
    GEN_TAC >> REWRITE_TAC[DET_DEF]
 >> ABBREV_TAC ‘N = dimindex (:'N)’
 >> ABBREV_TAC ‘f = \p. SIGN p * PRODUCT (count N) (\i. TRANSP A ' i ' (p i))’
 >> GEN_REWRITE_TAC LAND_CONV empty_rewrites [SUM_PERMUTATIONS_INVERSE]
 >> MATCH_MP_TAC SUM_EQ
 >> SIMP_TAC bool_ss[FINITE_PERMUTATIONS, FINITE_COUNT, Abbr ‘N’, Abbr ‘f’]
 >> X_GEN_TAC `p:num->num`
 >> CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN DISCH_TAC THEN BINOP_TAC THENL
   [PROVE_TAC[SIGN_INVERSE, PERMUTATION_PERMUTES, FINITE_COUNT],
    ALL_TAC] THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   empty_rewrites [GSYM(MATCH_MP PERMUTES_IMAGE th)]) THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `PRODUCT (count (dimindex(:'N)))
       ((\i. (TRANSP A:real['N]['N]) ' i ' (INVERSE p i)) o p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_IMAGE THEN
    PROVE_TAC[FINITE_COUNT, PERMUTES_INJECTIVE],
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[FINITE_COUNT, IN_COUNT] THEN
    SIMP_TAC bool_ss[TRANSP_DEF, FCP_BETA, o_THM] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
    SIMP_TAC bool_ss[FUN_EQ_THM, I_THM, o_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC bool_ss[FCP_BETA_PERM, FCP_BETA]]
QED

Theorem DET_LOWERTRIANGULAR :
   !A:real['N]['N].
       (!i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ i < j ==> (A ' i ' j = &0))
        ==> (DET(A) = PRODUCT (count (dimindex(:'N))) (\i. A ' i ' i))
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[DET_DEF] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM {I}
     (\p. SIGN p *
          PRODUCT (count (dimindex(:'N)))
                (\i. (A:real['N]['N]) ' i ' (p i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[SUM_SING] THEN BETA_TAC THEN
    REWRITE_TAC[SIGN_I, REAL_MUL_LID, I_THM]] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  SIMP_TAC bool_ss[IN_SING, SUBSET_DEF] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PRODUCT_EQ_0_COUNT, REAL_ENTIRE, SIGN_NZ] THEN
  MP_TAC(SPECL [`p:num->num`, `count (dimindex(:'N))`] PERMUTES_NUMSET_LE) THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT, NOT_LESS]
QED

Theorem DET_UPPERTRIANGULAR :
   !A:real['N]['N].
       (!i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ j < i ==> (A ' i ' j = &0))
        ==> (DET(A) = PRODUCT (count (dimindex(:'N))) (\i. A ' i ' i))
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[DET_DEF] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM {I}
     (\p. SIGN p *
          PRODUCT (count (dimindex(:'N)))
                (\i. (A:real['N]['N]) ' i ' (p i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[SUM_SING] THEN BETA_TAC THEN
    REWRITE_TAC[SIGN_I, REAL_MUL_LID, I_THM]] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  SIMP_TAC bool_ss[IN_SING, SUBSET_DEF] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PRODUCT_EQ_0_COUNT, REAL_ENTIRE, SIGN_NZ] THEN
  MP_TAC(SPECL [`p:num->num`, `count (dimindex(:'N))`] PERMUTES_NUMSET_GE) THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT, NOT_LESS]
QED

Theorem DET_DIAGONAL :
   !A:real['N]['N].
    (!i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j) ==> (A ' i ' j = &0))
        ==> (DET(A) = PRODUCT (count (dimindex(:'N))) (\i. A ' i ' i))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_LOWERTRIANGULAR THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[EQ_LESS_EQ, GSYM NOT_LESS]
QED

Theorem DET_I :
   DET(MAT 1 :real['N]['N]) = &1
Proof
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `PRODUCT(count(dimindex(:'N)))(\i. MAT 1:real['N]['N] ' i ' i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DET_LOWERTRIANGULAR, MATCH_MP_TAC PRODUCT_EQ_1_COUNT] THEN
  SIMP_TAC bool_ss[MAT_DEF, FCP_BETA] THEN PROVE_TAC[EQ_LESS_EQ, NOT_LESS]
QED

Theorem DET_0 :
   DET(MAT 0 :real['N]['N]) = &0
Proof
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `PRODUCT(count(dimindex(:'N)))(\i.MAT 0:real['N]['N] ' i ' i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DET_LOWERTRIANGULAR,
    REWRITE_TAC[PRODUCT_EQ_0_COUNT] THEN EXISTS_TAC `0`] THEN
  SIMP_TAC bool_ss[MAT_DEF, FCP_BETA, DIMINDEX_GE_1, LESS_EQ, GSYM ONE]
QED

Theorem DET_PERMUTE_ROWS :
   !A:real['N]['N] p.
        p PERMUTES (count (dimindex(:'N)))
        ==> (DET(FCP i. A ' (p i)) = SIGN(p) * DET(A))
Proof
  REWRITE_TAC[DET_DEF] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC bool_ss[GSYM SUM_LMUL] THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC LAND_CONV empty_rewrites
    [MATCH_MP SUM_PERMUTATIONS_COMPOSE_R th]) THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `q:num->num` THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN DISCH_TAC THEN BETA_TAC THEN BINOP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    PROVE_TAC[SIGN_COMPOSE, PERMUTATION_PERMUTES, FINITE_COUNT],
    ALL_TAC] THEN
  MP_TAC
  (MATCH_MP PERMUTES_INVERSE (ASSUME ``p PERMUTES (count (dimindex(:'N)))``)) THEN
  DISCH_THEN(fn th => GEN_REWRITE_TAC LAND_CONV empty_rewrites
    [MATCH_MP PRODUCT_PERMUTE_COUNT th]) THEN
  MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_COUNT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  SRW_TAC [FCP_ss][PERMUTES_INVERSE,PERMUTES_IN_COUNT] THEN
  PROVE_TAC[PERMUTES_INVERSES]
QED

Theorem DET_PERMUTE_COLUMNS :
   !A:real['N]['N] p.
        p PERMUTES (count (dimindex(:'N)))
        ==> (DET((FCP i j. A ' i ' (p j)):real['N]['N]) = SIGN(p) * DET(A))
Proof
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) empty_rewrites [GSYM DET_TRANSP] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC
   [GSYM(MATCH_MP DET_PERMUTE_ROWS th)]) THEN
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC bool_ss[CART_EQ, TRANSP_DEF, FCP_BETA, FCP_BETA_PERM]
QED

Theorem DET_IDENTICAL_ROWS :
  !A:real['N]['N] i j.
    i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j) /\ (ROW i A = ROW j A)
                    ==> (DET A = &0)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:real['N]['N]`, `SWAP(i:num,j:num)`] DET_PERMUTE_ROWS) THEN
  ASM_SIMP_TAC bool_ss[PERMUTES_SWAP, IN_COUNT, SIGN_SWAP] THEN
  MATCH_MP_TAC(REAL_ARITH ``(a = b) ==> (b = -&1 * a) ==> (a = &0)``) THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THEN
  SIMP_TAC bool_ss[ROW_DEF, CART_EQ, FCP_BETA] THEN
  REWRITE_TAC[SWAP_DEF] THEN PROVE_TAC[]
QED

Theorem DET_IDENTICAL_COLUMNS :
  !A:real['N]['N] i j.
    i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j) /\ (COLUMN i A = COLUMN j A)
                    ==> (DET A = &0)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DET_TRANSP] THEN
  MATCH_MP_TAC DET_IDENTICAL_ROWS THEN PROVE_TAC[ROW_TRANSP]
QED

Theorem DET_ZERO_ROW :
   !A:real['N]['N] i.
       i < dimindex(:'N) /\ (ROW i A = VECTOR_0)  ==> (DET A = &0)
Proof
  SIMP_TAC bool_ss[DET_DEF, ROW_DEF, CART_EQ, FCP_BETA, VEC_0_COMPONENT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ENTIRE, SIGN_NZ] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC bool_ss[PRODUCT_EQ_0, FINITE_COUNT] THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT]
QED

Theorem DET_ZERO_COLUMN :
   !A:real['N]['N] i.
      i < dimindex(:'N) /\ (COLUMN i A = VECTOR_0)  ==> (DET A = &0)
Proof
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DET_TRANSP] THEN
  MATCH_MP_TAC DET_ZERO_ROW THEN PROVE_TAC[ROW_TRANSP]
QED

Theorem DET_ROW_ADD :
   !a b c k.
          k < dimindex(:'N)
        ==> (DET ((FCP i. if i = k then a + b else c i):real['N]['N]) =
             DET ((FCP i. if i = k then a else c i):real['N]['N]) +
             DET ((FCP i. if i = k then b else c i):real['N]['N]))
Proof
  SIMP_TAC bool_ss[DET_DEF, GSYM SUM_ADD, FINITE_PERMUTATIONS, FINITE_COUNT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `p:num->num` THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  BETA_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `count(dimindex (:'N)) = k INSERT count (dimindex (:'N)) DELETE k`
  SUBST1_TAC THENL [PROVE_TAC[INSERT_DELETE, IN_COUNT], ALL_TAC] THEN
  SIMP_TAC bool_ss[PRODUCT_CLAUSES, FINITE_DELETE, FINITE_COUNT, IN_DELETE] THEN
  MATCH_MP_TAC(prove(
   `(c = a + b) /\ (y = x:real) /\ (z = x) ==> (c * x = a * y + b * z)`,
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  CONJ_TAC THENL
   [SRW_TAC[FCP_ss][FCP_BETA] THEN MATCH_MP_TAC VECTOR_ADD_COMPONENT THEN
    PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT],
    CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    SRW_TAC[FCP_ss][IN_DELETE, FINITE_DELETE, FINITE_COUNT]]
QED

Theorem DET_ROW_MUL :
   !a b c k.
        k < dimindex(:'N)
        ==> (DET((FCP i. if i = k then c * a else b i):real['N]['N]) =
             c * DET((FCP i. if i = k then a else b i):real['N]['N]))
Proof
  SIMP_TAC bool_ss[DET_DEF, GSYM SUM_LMUL,FINITE_PERMUTATIONS, FINITE_COUNT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `p:num->num` THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `count(dimindex (:'N)) = k INSERT count (dimindex (:'N)) DELETE k`
  SUBST1_TAC THENL [PROVE_TAC[INSERT_DELETE, IN_COUNT], ALL_TAC] THEN
  SIMP_TAC bool_ss[PRODUCT_CLAUSES, FINITE_DELETE, FINITE_COUNT, IN_DELETE,
                   REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC(prove(
   `(cp = c * p) /\ (p1 = p2:real) ==> (s * cp * p1 = c * s * p * p2)`,
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  CONJ_TAC THENL
   [SRW_TAC[FCP_ss][] THEN MATCH_MP_TAC VECTOR_MUL_COMPONENT THEN
    PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT],
    MATCH_MP_TAC PRODUCT_EQ THEN
    SRW_TAC[FCP_ss][IN_DELETE, FINITE_DELETE, FINITE_COUNT]]
QED

Theorem DET_ROW_OPERATION :
   !A:real['N]['N] c i j.
        i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j)
        ==> (DET(FCP k. if k = i then ROW i A + c * ROW j A else ROW k A) =
             DET A)
Proof
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC bool_ss[DET_ROW_ADD, DET_ROW_MUL] THEN
  MATCH_MP_TAC(prove(`(a = b) /\ (d = &0) ==> (a + c * d = b)`,
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN SRW_TAC [FCP_ss][] THEN
    COND_CASES_TAC THEN SRW_TAC [FCP_ss][ROW_DEF],
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [`i:num`, `j:num`] THEN
    SRW_TAC [FCP_ss][ROW_DEF]]
QED

Theorem DET_ROW_SPAN :
   !A:real['N]['N] i x.
        i < dimindex(:'N) /\
        x IN span {ROW j A |j < dimindex(:'N) /\ ~(j = i)}
        ==> (DET(FCP k. if k = i then ROW i A + x else ROW k A) = DET A)
Proof
  GEN_TAC THEN GEN_TAC THEN
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  HO_MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN SRW_TAC [FCP_ss][VECTOR_ADD_RID] THEN
    COND_CASES_TAC THEN SRW_TAC [FCP_ss][ROW_DEF],
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[VECTOR_ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
     ``a + c * x + y:real['N] = (a + y) + c * x``] THEN
  ABBREV_TAC `z = ROW i (A:real['N]['N]) + y` THEN
  ASM_SIMP_TAC bool_ss[DET_ROW_MUL, DET_ROW_ADD] THEN
  MATCH_MP_TAC(prove(`(d = &0) ==> (a + c * d = a)`,
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
  MAP_EVERY EXISTS_TAC [`i:num`, `j:num`] THEN
  SRW_TAC[FCP_ss][ROW_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* May as well do this, though it's a bit unsatisfactory since it ignores    *)
(* exact duplicates by considering the rows/columns as a set.                *)
(* ------------------------------------------------------------------------- *)

Theorem DET_DEPENDENT_ROWS :
   !A:real['N]['N]. dependent(ROWS A) ==> (DET A = &0)
Proof
  GEN_TAC THEN
  REWRITE_TAC[dependent_def, ROWS_DEF] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  SIMP_TAC bool_ss[GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `?i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j) /\
          (ROW i (A:real['N]['N]) = ROW j A)`
  THENL [PROVE_TAC[DET_IDENTICAL_ROWS], ALL_TAC] THEN
  MP_TAC(SPECL [`A:real['N]['N]`, `i:num`, `~(ROW i (A:real['N]['N]))`]
    DET_ROW_SPAN) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[IMP_DISJ_THM] THEN DISJ1_TAC THEN MATCH_MP_TAC SPAN_NEG THEN
    PAT_ASSUM `$IN X Y` MP_TAC THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    REWRITE_TAC[SPECIFICATION] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION, IN_DELETE] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[],
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DET_ZERO_ROW THEN
    EXISTS_TAC `i:num` THEN
    SRW_TAC[FCP_ss][ROW_DEF, VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT, VEC_0_COMPONENT]]
QED

Theorem DET_DEPENDENT_COLUMNS :
   !A:real['N]['N]. dependent(COLUMNS A) ==> (DET A = &0)
Proof
  PROVE_TAC[DET_DEPENDENT_ROWS, ROWS_TRANSP, DET_TRANSP]
QED

(* ------------------------------------------------------------------------- *)
(* Multilinearity and the multiplication formula.                            *)
(* ------------------------------------------------------------------------- *)

Theorem DET_LINEAR_ROW_VSUM :
   !a c s k.
         FINITE s /\ k < dimindex(:'N)
         ==> (DET((FCP i. if i = k then VSUM s a else c i):real['N]['N]) =
             SUM s
               (\j. DET((FCP i. if i = k then a(j) else c i):real['N]['N])))
Proof
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES, SUM_CLAUSES, DET_ROW_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_ZERO_ROW THEN EXISTS_TAC `k:num` THEN
  SRW_TAC[FCP_ss][ROW_DEF, VEC_0_COMPONENT]
QED

Theorem BOUNDED_FUNCTIONS_BIJECTIONS_1[local] :
   !p. p IN {(y,g) | y IN s /\
                     g IN {f | (!i. i < k ==> f i IN s) /\
                               (!i. ~(i < k) ==> (f i = i))}}
       ==> (\(y,g) i. if i = k then y else g(i)) p IN
             {f | (!i. i < SUC k ==> f i IN s) /\
                  (!i. ~(i < SUC k) ==> (f i = i))} /\
           ((\h. h(k),(\i. if i = k then i else h(i)))
            ((\(y,g) i. if i = k then y else g(i)) p) = p)
Proof
  SIMP_TAC std_ss[FORALL_PROD] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MAP_EVERY X_GEN_TAC [`y:num`, `h:num->num`] THEN
  REPEAT STRIP_TAC THENL
   [BETA_TAC THEN PROVE_TAC[LT],
    BETA_TAC THEN PROVE_TAC[LT],
    REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN
    PROVE_TAC[prove( `~(k:num < k)`, ARITH_TAC)]]
QED

Theorem BOUNDED_FUNCTIONS_BIJECTIONS_2[local] :
   !h. h IN {f | (!i. i < SUC k ==> f i IN s) /\
                 (!i. ~(i < SUC k) ==> (f i = i))}
       ==> (\h. h(k),(\i. if i = k then i else h(i))) h IN
           {(y,g) | y IN s /\
                     g IN {f | (!i. i < k ==> f i IN s) /\
                               (!i. ~(i < k) ==> (f i = i))}} /\
           ((\(y,g) i. if i = k then y else g(i))
              ((\h. h(k),(\i. if i = k then i else h(i))) h) = h)
Proof
  CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  X_GEN_TAC `h:num->num` THEN REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC[`(h k):num`,`(\i. if i = k then i else h i):num->num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
          [PROVE_TAC[LT],
           BETA_TAC THEN PROVE_TAC[prove(`i < k ==> i< SUC k /\ ~(i = k)`, ARITH_TAC)],
           BETA_TAC THEN PROVE_TAC[prove(`i< SUC k /\ ~(i = k) ==> i < k`, ARITH_TAC)]],
    REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN PROVE_TAC[]]
QED

Theorem FINITE_BOUNDED_FUNCTIONS :
   !s k:num. FINITE s
         ==> FINITE {f | (!i. i < k ==> f(i) IN s) /\
                         (!i. ~(i < k) ==> (f(i) = i))}
Proof
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[prove(`~(i:num < 0)`, ARITH_TAC)] THEN
    SIMP_TAC bool_ss[GSYM FUN_EQ_THM, GSPEC_EQ, FINITE_RULES],
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[AND_IMP_INTRO] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_CROSS) THEN
  DISCH_THEN(MP_TAC o ISPEC `\p:num # (num->num) i. if i = k then FST p else SND p (i)` o
                      MATCH_MP IMAGE_FINITE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION, IN_IMAGE, IN_CROSS] THEN
  X_GEN_TAC `h:num->num` THEN EQ_TAC THENL
   [CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN STRIP_TAC THEN
    ASM_SIMP_TAC bool_ss[] THEN PROVE_TAC[LT],
        ALL_TAC] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN DISCH_TAC THEN EXISTS_TAC
    `(\h. h(k),(\i. if i = k then i else h(i))) h` THEN
  SIMP_TAC bool_ss[FST, SND] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC bool_ss[FUN_EQ_THM] THEN PROVE_TAC[prove( `i:num < k ==> ~(i = k)`, ARITH_TAC),LT]
QED

Theorem DET_LINEAR_ROWS_VSUM_LEMMA :
   !s k a c.
         FINITE s /\ k <= dimindex(:'N)
         ==> (DET((FCP i. if i < k then VSUM s (a i) else c i):real['N]['N]) =
              SUM {f | (!i. i < k ==> f(i) IN s) /\
                       !i. ~(i < k) ==> (f(i) = i)}
                  (\f. DET((FCP i. if i < k then a i (f i) else c i)
                          :real['N]['N])))
Proof
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ZERO_LESS_EQ, LT] THEN
    SIMP_TAC bool_ss[GSYM FUN_EQ_THM, GSPEC_EQ] THEN REWRITE_TAC[SUM_SING],
    ALL_TAC] THEN
  DISCH_TAC THEN PAT_X_ASSUM `$==> X Y` MP_TAC THEN
  ASM_SIMP_TAC bool_ss[prove(`SUC k <= n ==> k <= n`, ARITH_TAC)] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [LT] THEN
  REWRITE_TAC[prove
   (`(if a \/ b then c else d) = (if a then c else if b then c else d)`, PROVE_TAC[])] THEN
  ASM_SIMP_TAC bool_ss[prove(`SUC k <= n ==> k < n`, ARITH_TAC), DET_LINEAR_ROW_VSUM] THEN
  ONCE_REWRITE_TAC[prove(
    `(if a then b else if c then d else e) =
     (if c then (if a then b else d) else (if a then b else e))`, PROVE_TAC[])] THEN
  ASM_SIMP_TAC bool_ss[prove( `i:num < k ==> ~(i = k)`, ARITH_TAC)] THEN
  ASM_SIMP_TAC bool_ss[SUM_SUM_PRODUCT, FINITE_BOUNDED_FUNCTIONS] THEN
  MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\(y:num,g) i. if i = k then y else g(i)` THEN
  EXISTS_TAC `\h. h(k),(\i. if i = k then i else h(i))` THEN
  CONJ_TAC THENL [ACCEPT_TAC BOUNDED_FUNCTIONS_BIJECTIONS_2, ALL_TAC] THEN
  X_GEN_TAC `p:num#(num->num)` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP BOUNDED_FUNCTIONS_BIJECTIONS_1) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`p:num#(num->num)`,`q:num#(num->num)`) THEN
  SIMP_TAC bool_ss[FORALL_PROD] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  MAP_EVERY X_GEN_TAC [`y:num`, `g:num->num`] THEN AP_TERM_TAC THEN
  SRW_TAC[FCP_ss][] THEN REPEAT
  (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  PROVE_TAC[LT, LT_REFL]
QED

Theorem DET_LINEAR_ROWS_VSUM :
   !s k a.
         FINITE s
         ==> (DET((FCP i. VSUM s (a i)):real['N]['N]) =
              SUM {f | (!i. i < dimindex(:'N) ==> f(i) IN s) /\
                      !i. ~(i < dimindex(:'N)) ==> (f(i) = i)}
                 (\f. DET((FCP i. a i (f i)):real['N]['N])))
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:num->bool`, `dimindex(:'N)`] DET_LINEAR_ROWS_VSUM_LEMMA) THEN
  ASM_SIMP_TAC bool_ss[LT_REFL, GSYM NOT_LESS, prove
   (`(FCP i. if i < dimindex(:'N) then x(i) else y(i)):real['N]['N] =
     (FCP i. x(i))`,
    SRW_TAC[FCP_ss][])]
QED

Theorem MATRIX_MUL_VSUM_ALT :
   !A:real['N]['N] B:real['N]['N]. A ** B =
                  FCP i. VSUM (count(dimindex(:'N))) (\k. A ' i ' k * B ' k)
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, VECTOR_MUL_COMPONENT, VSUM_COMPONENT]
QED

Theorem DET_ROWS_MUL :
   !a c. DET((FCP i. c i * a i):real['N]['N]) =
         PRODUCT(count(dimindex(:'N))) (\i. c(i)) *
         DET((FCP i. a(i)):real['N]['N])
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[DET_DEF] THEN
  SIMP_TAC bool_ss[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN
  X_GEN_TAC `p:num->num` THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN DISCH_TAC THEN
  MATCH_MP_TAC(prove
     (`(b:real = c * d) ==> (s * b = c * (s * d))`,
         STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  SIMP_TAC bool_ss[GSYM PRODUCT_MUL_COUNT] THEN
  MATCH_MP_TAC PRODUCT_EQ_COUNT THEN
  SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT, PERMUTES_IN_COUNT]
QED

Theorem DET_MUL :
   !A B:real['N]['N]. DET(A ** B) = DET(A) * DET(B)
Proof
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_VSUM_ALT] THEN
  SIMP_TAC bool_ss[DET_LINEAR_ROWS_VSUM, FINITE_COUNT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM {p | p PERMUTES count(dimindex(:'N))}
            (\f. DET (FCP i. (A:real['N]['N]) ' i ' (f i) * (B:real['N]['N]) ' (f i)))` THEN
  CONJ_TAC THENL
   [SIMP_TAC bool_ss[DET_ROWS_MUL] THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    BETA_TAC THEN REWRITE_TAC[SUBSET_DEF] THEN
        CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN CONJ_TAC THENL
     [PROVE_TAC[PERMUTES_DEF, IN_COUNT], ALL_TAC] THEN
    X_GEN_TAC `f:num->num` THEN REWRITE_TAC[PERMUTES_DEF, IN_COUNT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MP_TAC(ISPECL [`count(dimindex(:'N))`, `f:num->num`]
       SURJECTIVE_IFF_INJECTIVE) THEN
    ASM_SIMP_TAC bool_ss[SUBSET_DEF, IN_COUNT, FINITE_COUNT, FORALL_IN_IMAGE] THEN
    MATCH_MP_TAC(TAUT `(~b ==> c) /\ (b ==> ~a) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL
     [SIMP_TAC bool_ss[NOT_FORALL_THM] THEN
      REPEAT(HO_MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      SRW_TAC[FCP_ss][ROW_DEF, NOT_IMP],
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `!x y. ((f:num->num) x = f y) ==> (x = y)` ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      ASM_CASES_TAC ` x < dimindex(:'N)` THEN
      ASM_CASES_TAC ` y < dimindex(:'N)` THEN
      PROVE_TAC[],
      ALL_TAC] THEN
    PROVE_TAC[],
    ALL_TAC] THEN
  SIMP_TAC bool_ss[DET_DEF, REAL_MUL_SUM, FINITE_PERMUTATIONS, FINITE_COUNT] THEN
  MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN
  X_GEN_TAC `p:num->num` THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN DISCH_TAC THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC RAND_CONV empty_rewrites
    [MATCH_MP SUM_PERMUTATIONS_COMPOSE_R (MATCH_MP PERMUTES_INVERSE th)]) THEN
  MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN
  X_GEN_TAC `q:num->num` THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN ONCE_REWRITE_TAC[prove(
   `(p * x) * (q * y:real) = (p * q) * (x * y)`, REAL_ARITH_TAC)] THEN
  BINOP_TAC THENL
   [SUBGOAL_THEN `SIGN(q o INVERSE p) = SIGN(p:num->num) * SIGN(q:num->num)`
     (fn t => SIMP_TAC bool_ss[REAL_MUL_ASSOC, SIGN_IDEMPOTENT, REAL_MUL_LID, t]) THEN
    PROVE_TAC[SIGN_COMPOSE, PERMUTES_INVERSE, PERMUTATION_PERMUTES,
              FINITE_COUNT, SIGN_INVERSE, REAL_MUL_SYM],
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) empty_rewrites
   [MATCH_MP PRODUCT_PERMUTE_COUNT (ASSUME ``p PERMUTES count(dimindex(:'N))``)] THEN
  SIMP_TAC bool_ss[GSYM PRODUCT_MUL, FINITE_COUNT] THEN
  MATCH_MP_TAC PRODUCT_EQ_COUNT THEN
  SRW_TAC[FCP_ss][o_THM] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(A:real['N]['N]) ' i ' (p i) * (B:real['N]['N]) ' (p i) ' (q i)` THEN CONJ_TAC THENL
   [PROVE_TAC[VECTOR_MUL_COMPONENT, PERMUTES_IN_IMAGE, IN_COUNT],
    PROVE_TAC[PERMUTES_INVERSES]]
QED

(* ------------------------------------------------------------------------- *)
(* Relation to invertibility.                                                *)
(* ------------------------------------------------------------------------- *)

Theorem INVERTIBLE_DET_NZ :
   !A:real['N]['N]. invertible(A) <=> ~(DET A = &0)
Proof
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC bool_ss[INVERTIBLE_RIGHT_INVERSE, GSYM LEFT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM ``DET:real['N]['N]->real``) THEN
    REWRITE_TAC[DET_MUL, DET_I] THEN PROVE_TAC[REAL_ENTIRE, REAL_10],
    ALL_TAC] THEN
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE] THEN
  REWRITE_TAC[MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS] THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`, `i:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A:real['N]['N]`, `i:num`, `~(ROW i (A:real['N]['N]))`]
    DET_ROW_SPAN) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `~(ROW i (A:real['N]['N])) =
       VSUM ((count (dimindex (:'N))) DELETE i) (\j. inv(c i) * c j * ROW j A)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC bool_ss[VSUM_DELETE_CASES, FINITE_COUNT, IN_COUNT, GSYM VECTOR_MUL_ASSOC, VSUM_LMUL] THEN
      ASM_SIMP_TAC bool_ss[VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN VECTOR_ARITH_TAC,
      ALL_TAC] THEN
    SIMP_TAC bool_ss[Once MONO_NOT_EQ] THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_VSUM THEN
    SIMP_TAC bool_ss[FINITE_COUNT, IN_COUNT, FINITE_DELETE, IN_DELETE] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[],
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DET_ZERO_ROW THEN
  EXISTS_TAC `i:num` THEN
  SRW_TAC[FCP_ss][ROW_DEF, VEC_0_COMPONENT, VECTOR_ADD_RINV]
QED

Theorem DET_EQ_0 :
   !A:real['N]['N]. (DET(A) = &0) <=> ~invertible(A)
Proof
  REWRITE_TAC[INVERTIBLE_DET_NZ]
QED

Theorem DET_MATRIX_EQ_0 :
   !f:real['N]->real['N].
        linear f
        ==> ((DET(matrix f) = &0) <=>
             ~(?g. linear g /\ (f o g = I) /\ (g o f = I)))
Proof
  SIMP_TAC bool_ss[DET_EQ_0, MATRIX_INVERTIBLE]
QED

Theorem DET_MATRIX_EQ_0_LEFT :
   !f:real['N]->real['N].
        linear f
        ==> ((DET(matrix f) = &0) <=>
             ~(?g. linear g /\ (g o f = I)))
Proof
   SIMP_TAC bool_ss[DET_MATRIX_EQ_0] THEN PROVE_TAC[LINEAR_INVERSE_LEFT]
QED

Theorem DET_MATRIX_EQ_0_RIGHT :
   !f:real['N]->real['N].
        linear f
        ==> ((DET(matrix f) = &0) <=>
             ~(?g. linear g /\ (f o g = I)))
Proof
   SIMP_TAC bool_ss[DET_MATRIX_EQ_0] THEN PROVE_TAC[LINEAR_INVERSE_LEFT]
QED

(* ------------------------------------------------------------------------- *)
(* Cramer's rule.                                                            *)
(* ------------------------------------------------------------------------- *)

Theorem CRAMER_LEMMA_TRANSP :
   !A:real['N]['N] x:real['N] k.
         k < dimindex(:'N)
        ==> (DET((FCP i. if i = k
                           then VSUM (count (dimindex(:'N))) (\i. (x ' i) * ROW i A)
                           else ROW i A): real['N]['N]) =
            (x ' k) * DET A)
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `count (dimindex(:'N)) = k INSERT ((count (dimindex(:'N))) DELETE k)`
  SUBST1_TAC THENL [PROVE_TAC[INSERT_DELETE, IN_COUNT], ALL_TAC] THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_COUNT, FINITE_DELETE, IN_DELETE] THEN
  REWRITE_TAC[VECTOR_ARITH
   ``(x:real['N] ' k) * ROW k (A:real['N]['N]) + s =
    (x ' k - &1) * ROW k A + (ROW k A + s)``] THEN
  ASM_SIMP_TAC bool_ss[Once DET_ROW_ADD, DET_ROW_MUL] THEN
  MATCH_MP_TAC(prove(`(d:real = d') /\ (e = d') ==> ((c - &1) * d + e = c * d')`,
                                        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN SRW_TAC[FCP_ss][] THEN
    COND_CASES_TAC THEN SRW_TAC[FCP_ss][ROW_DEF],
    MATCH_MP_TAC DET_ROW_SPAN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_VSUM THEN
    REWRITE_TAC[FINITE_COUNT, IN_COUNT, FINITE_DELETE, IN_DELETE] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]]
QED

Theorem CRAMER_LEMMA :
   !A:real['N]['N] x:real['N] k.
        k < dimindex(:'N)
        ==> (DET((FCP i j. if j = k then (A**x) ' i else A ' i ' j):real['N]['N]) =
             x ' k * DET(A))
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MATRIX_MUL_VSUM] THEN
  FIRST_ASSUM(MP_TAC o SYM o SPECL [`TRANSP(A:real['N]['N])`, `x:real['N]`] o
              MATCH_MP CRAMER_LEMMA_TRANSP) THEN
  REWRITE_TAC[DET_TRANSP] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  SRW_TAC[FCP_ss][TRANSP_DEF, MATRIX_MUL_VSUM, ROW_DEF, COLUMN_DEF,
                  COND_COMPONENT, VECTOR_MUL_COMPONENT, VSUM_COMPONENT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_COUNT THEN
  BETA_TAC THEN SRW_TAC[FCP_ss][]
QED

Theorem CRAMER :
   !A:real['N]['N] x b.
        ~(DET(A) = &0)
        ==> ((A ** x = b) <=>
             (x = FCP k.
                   DET((FCP i j. if j = k then b ' i else A ' i ' j):real['N]['N]) /
                   DET(A)))
Proof
  GEN_TAC THEN SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  CONV_TAC SWAP_VARS_CONV THEN GEN_TAC THEN HO_MATCH_MP_TAC(PROVE[]
   ``(?x. p(x)) /\ (!x. p(x) ==> (x = a)) ==> !x. p(x) <=> (x = a)``) THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC `A:real['N]['N]` INVERTIBLE_DET_NZ) THEN
    PROVE_TAC[invertible_def, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC bool_ss[CART_EQ, CRAMER_LEMMA, FCP_BETA, prove(
                `~(z = &0) ==> ((x = y / z) <=> (x * z = y))`,
                STRIP_TAC THEN EQ_TAC THEN RW_TAC bool_ss[real_div] THEN
        RW_TAC bool_ss[GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RINV,REAL_MUL_RID])]]
QED

Theorem LAPLACE_ROW :
   !A:real['N]['N] i.
      i < dimindex (:'N) ==>
          (DET(A) = SUM (count(dimindex (:'N))) (\j. (A ' i ' j ) * (ALG_COMP A i j)))
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ALG_COMP_DEF, DET_DEF] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC bool_ss[FINITE_PERMUTATIONS, FINITE_COUNT, Once SUM_SWAP] THEN
  MATCH_MP_TAC SUM_EQ THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN BETA_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH ``!a b c:real. a * (b * c) = b * (a * c)``] THEN
  SIMP_TAC bool_ss[SUM_LMUL] THEN REWRITE_TAC[SIGN_NZ, REAL_EQ_LMUL] THEN
  X_GEN_TAC `p :num -> num` THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM (count (dimindex (:'N)))
    (\j. if j = p i then PRODUCT (count (dimindex (:'N))) (\i. A ' i ' (p i)) else &0)` THEN
  CONJ_TAC THENL[
    REWRITE_TAC[SUM_DELTA] THEN PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT], ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j` THEN SRW_TAC[FCP_ss][] THENL[
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
    `PRODUCT (count (dimindex (:'N)))(\i'. if i' = i then A ' i' ' (p i') else &1) *
     PRODUCT (count (dimindex (:'N)))
     (\i'.
       ((FCP k l.
          if k = i then
            if l = p i then &1 else &0
          else if l = p i then
            &0
          else
            A ' k ' l):real['N]['N]) ' i' ' (p i'))` THEN
        CONJ_TAC THENL[
          SIMP_TAC bool_ss[GSYM PRODUCT_MUL_COUNT] THEN
      SRW_TAC[FCP_ss][PERMUTES_IN_COUNT] THEN MATCH_MP_TAC PRODUCT_EQ_COUNT THEN
      SRW_TAC[FCP_ss][PERMUTES_IN_COUNT] THEN PROVE_TAC[PERMUTES_INJECTIVE], ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    ASM_SIMP_TAC bool_ss[PRODUCT_DELTA, IN_COUNT], ALL_TAC] THEN
  DISJ2_TAC THEN SIMP_TAC bool_ss[FINITE_COUNT, PRODUCT_EQ_0] THEN
  EXISTS_TAC `i` THEN SRW_TAC[FCP_ss][PERMUTES_IN_COUNT]
QED

Theorem LAPLACE_COLUMN :
   !A:real['N]['N] j.
      j < dimindex (:'N) ==>
          (DET(A) = SUM (count(dimindex (:'N))) (\i. (A ' i ' j ) * (ALG_COMP A i j)))
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `SUM (count (dimindex (:'N))) (\i. (TRANSP A) ' j ' i * ALG_COMP (TRANSP A) j i)` THEN
  CONJ_TAC THENL[ASM_SIMP_TAC bool_ss[GSYM LAPLACE_ROW, DET_TRANSP], ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][TRANSP_DEF, ALG_COMP_DEF] THEN DISJ2_TAC THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites[GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  SRW_TAC[FCP_ss][TRANSP_DEF] THEN PROVE_TAC[]
QED

Definition adjoint_matrix_def :
  (adjoint_matrix:real['N]['N]-> real['N]['N]) A =
                TRANSP(FCP i j. ALG_COMP A i j)
End

Overload ADJOINT_MATRIX[local] = “adjoint_matrix”
val ADJOINT_MATRIX_DEF = adjoint_matrix_def;

Theorem LAPLACE_ROW_COROLLARY :
   !A:real['N]['N].
    !i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j) ==>
        (SUM (count (dimindex(:'N))) (\k. A ' i ' k * ALG_COMP A j k) = &0)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
 `SUM (count (dimindex(:'N)))
        (\k. ((FCP k. if k = j then ROW i A else ROW k A ):real['N]['N])' j ' k *
               ALG_COMP ((FCP k. if k = j then ROW i A else ROW k A ):real['N]['N]) j k)` THEN
  CONJ_TAC THENL[
        MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][ROW_DEF, ALG_COMP_DEF] THEN
        DISJ2_TAC THEN AP_TERM_TAC THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  ASM_SIMP_TAC bool_ss[GSYM LAPLACE_ROW] THEN MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
  MAP_EVERY EXISTS_TAC [`i`, `j`] THEN SRW_TAC[FCP_ss][ROW_DEF]
QED

Theorem LAPLACE_COLUMN_COROLLARY :
   !A:real['N]['N].
    !i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j) ==>
        (SUM (count (dimindex(:'N))) (\k. A ' k ' i * ALG_COMP A k j) = &0)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
 `SUM (count (dimindex(:'N)))
        (\k. ((FCP k l. if l = j then A ' k ' i else A ' k ' l ):real['N]['N])' k ' j *
               ALG_COMP ((FCP k l. if l = j then A ' k ' i else A ' k ' l ):real['N]['N]) k j)` THEN
  CONJ_TAC THENL[
        MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][COLUMN_DEF, ALG_COMP_DEF] THEN
        DISJ2_TAC THEN AP_TERM_TAC THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  ASM_SIMP_TAC bool_ss[GSYM LAPLACE_COLUMN] THEN MATCH_MP_TAC DET_IDENTICAL_COLUMNS THEN
  MAP_EVERY EXISTS_TAC [`i`, `j`] THEN SRW_TAC[FCP_ss][COLUMN_DEF]
QED

Theorem LAPLACE_COROLLARY_LMUL :
   !A:real['N]['N]. A ** ADJOINT_MATRIX A = DET A * MAT 1
Proof
  REWRITE_TAC[matrix_mul_def, ADJOINT_MATRIX_DEF] THEN GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `FCP i j. SUM (count (dimindex (:'N)))(\k. A ' i ' k * ALG_COMP A j k)` THEN
  CONJ_TAC THENL [
    SRW_TAC[FCP_ss][TRANSP_DEF] THEN MATCH_MP_TAC SUM_EQ, ALL_TAC] THEN
  SRW_TAC[FCP_ss][] THEN ASM_CASES_TAC `i = i'` THEN
  ASM_SIMP_TAC bool_ss[GSYM LAPLACE_ROW, LAPLACE_ROW_COROLLARY, MATRIX_CMUL_COMPONENT,
                       MAT_COMPONENT, REAL_MUL_RID, REAL_MUL_RZERO]
QED

Theorem LAPLACE_COROLLARY_RMUL :
   !A:real['N]['N]. ADJOINT_MATRIX A ** A = DET A * MAT 1
Proof
  REWRITE_TAC[matrix_mul_def, ADJOINT_MATRIX_DEF] THEN GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `FCP i j. SUM (count (dimindex (:'N)))(\k. ALG_COMP A k i * A ' k ' j)` THEN
  CONJ_TAC THENL [
    SRW_TAC[FCP_ss][TRANSP_DEF] THEN MATCH_MP_TAC SUM_EQ, ALL_TAC] THEN
  SRW_TAC[FCP_ss][] THEN
  ASM_CASES_TAC `i = i'` THEN
  ASM_SIMP_TAC bool_ss[GSYM LAPLACE_COLUMN, LAPLACE_COLUMN_COROLLARY, MATRIX_CMUL_COMPONENT,
                       MAT_COMPONENT, REAL_MUL_RID, REAL_MUL_RZERO]
QED

Theorem MATRIX_INV_EXPLICIT :
   !A:real['N]['N].
    invertible A ==> (MATRIX_INV A = inv(DET A) * ADJOINT_MATRIX A)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_EQ_LMUL THEN
  EXISTS_TAC `A:real['N]['N]` THEN
  ASM_SIMP_TAC bool_ss[MATRIX_INV, LAPLACE_COROLLARY_LMUL, MATRIX_VECTOR_MUL_ASSOC,
                       MATRIX_MUL_RMUL, MATRIX_CMUL_ASSOC] THEN
  MP_TAC(ISPEC `A:real['N]['N]` INVERTIBLE_DET_NZ) THEN
  ASM_SIMP_TAC bool_ss[REAL_MUL_LINV, MATRIX_CMUL_LID]
QED

val _ = export_theory ();
val _ = html_theory "determinant";
