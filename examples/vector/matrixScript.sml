(* ========================================================================= *)
(* Matrices in Euclidean space, and elementary linear algebra.               *)
(*     (HOL-Light's Multivariate/vectors.ml, Part II)                        *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*       (c) Copyright, Liming Li, Yong Guan and Zhiping Shi [1] 2011        *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(*       (c) Copyright, Andrea Gabrielli, Marco Maggesi 2016-2017            *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory PairedLambda
     pred_setLib fcpTheory fcpLib tautLib numLib listTheory rich_listTheory
     topologyTheory InductiveDefinition;

open realTheory realLib iterateTheory real_sigmaTheory RealArith mesonLib;
open hurdUtils permutesTheory vectorTheory;

val _ = new_theory "matrix";

val bool_ss' = bool_ss -* ["lift_disj_eq", "lift_imp_disj"];

(* ------------------------------------------------------------------------- *)
(* Matrix notation. NB: an MxN matrix is of type real^N^M, not real^M^N.     *)
(* We could define a special type if we're going to use them a lot.          *)
(* ------------------------------------------------------------------------- *)

Definition matrix_cmul_def :
   matrix_cmul:real->real['N]['M]->real['N]['M] c A = FCP i j. c * A ' i ' j
End

Definition matrix_neg_def :
   matrix_neg:real['N]['M]->real['N]['M] A = FCP i j. -(A ' i ' j)
End

Definition matrix_add_def :
   matrix_add:real['N]['M]->real['N]['M]->real['N]['M] A B =
     FCP i j. A ' i ' j + B ' i ' j
End

Definition matrix_sub_def :
   matrix_sub:real['N]['M]->real['N]['M]->real['N]['M] A B =
     FCP i j. A ' i ' j - B ' i ' j
End

(* MxP * PxN = MxN *)
Definition matrix_mul_def :
   matrix_mul:real['P]['M]->real['N]['P]->real['N]['M] A B =
     FCP i j. sum (count(dimindex(:'P))) (\k. A ' i ' k * B ' k ' j)
End

(* MxN * Nx1 = Mx1 *)
Definition matrix_vector_mul_def :
   matrix_vector_mul:real['N]['M]->real['N]->real['M] A x =
     FCP i. sum (count(dimindex(:'N))) (\j. A ' i ' j * x ' j)
End

(* 1xM * MxN = 1xN *)
Definition vector_matrix_mul_def :
   vector_matrix_mul:real['M]->real['N]['M]->real['N] x A =
     FCP j. sum (count(dimindex(:'M))) (\i. A ' i ' j * x ' i)
End

Overload "~"  = “matrix_neg       :real['N]['M]->real['N]['M]”
Overload "+"  = “matrix_add       :real['N]['M]->real['N]['M]->real['N]['M]”
Overload "-"  = “matrix_sub       :real['N]['M]->real['N]['M]->real['N]['M]”
Overload "**" = “matrix_mul       :real['P]['M]->real['N]['P]->real['N]['M]”
Overload "**" = “matrix_vector_mul:real['N]['M]->real['N]->real['M]”
Overload "**" = “vector_matrix_mul:real['M]->real['N]['M]->real['N]”
Overload "*"  = “matrix_cmul      :real->real['N]['M]->real['N]['M]”

(* The ith row of a MxN matrix is a 1xN vector *)
Definition row_def :
   (row:num->real['N]['M]->real['N]) i A = (FCP j. A ' i ' j ):real['N]
End

(* The jth column of a MxN matrix is a Mx1 vector *)
Definition column_def :
   (column:num->real['N]['M]->real['M]) j A = (FCP i. A ' i ' j):real['M]
End

(* transpose operation: MxN -> NxM *)
Definition transp_def :
   (transp:real['N]['M]->real['M]['N]) A = (FCP i j. (A ' j ' i)):real['M]['N]
End

(* MxN diagonal matrix of the same elements. This serves as "matrix constant" *)
Definition mat_def :
   (mat:num->real['N]['M]) k = FCP i j. if i = j then &k else &0
End

(* this is experimental, for user code only (not used in the rest of file) *)
val _ = add_numeral_form (#"m", SOME "mat");

(* The set of all 1xN rows of an MxN matrix *)
Definition rows_def :
   rows (A:real['N]['M]) = {row i A | i < dimindex(:'M)}
End

Definition columns_def :
   columns (A:real['N]['M]) = {column i A | i < dimindex(:'N)}
End

Theorem ROW_FCP :
   !f k. k < dimindex(:'M) ==>
        (row k ((FCP i j. f i j):real['N]['M]) = FCP j. f k j)
Proof
    SRW_TAC [FCP_ss][row_def]
QED

Theorem COLUMN_FCP :
   !f k. k < dimindex (:'N) ==>
        (column k ((FCP i j. f i j):real['N]['M]) = FCP i. f i k)
Proof
    SRW_TAC [FCP_ss][column_def]
QED

Theorem MATRIX_CMUL_COMPONENT :
   !c A:real['N]['M] i j. i < dimindex(:'M) /\ j < dimindex(:'N) ==>
                         ((c * A) ' i ' j = c * A ' i ' j)
Proof
  SRW_TAC[FCP_ss][matrix_cmul_def]
QED

Theorem MATRIX_ADD_COMPONENT :
   !A B:real['N]['M] i j. i < dimindex(:'M) /\ j < dimindex(:'N) ==>
                         ((A + B) ' i ' j = A ' i ' j + B ' i ' j)
Proof
  SRW_TAC[FCP_ss][matrix_add_def]
QED

Theorem MATRIX_SUB_COMPONENT :
   !A B:real['N]['M] i j. i < dimindex(:'M) /\ j < dimindex(:'N) ==>
                         ((A - B) ' i ' j = A ' i ' j - B ' i ' j)
Proof
  SRW_TAC[FCP_ss][matrix_sub_def]
QED

Theorem MATRIX_NEG_COMPONENT :
   !A:real['N]['M] i j. i < dimindex(:'M) /\ j < dimindex(:'N) ==>
                       ((~A) ' i ' j = -A ' i ' j)
Proof
  SRW_TAC[FCP_ss][matrix_neg_def]
QED

Theorem MAT_COMPONENT :
   !n i j. i < dimindex(:'M) /\ j < dimindex(:'N) ==>
          ((mat n:real['N]['M]) ' i ' j = if i = j then &n else &0)
Proof
  SRW_TAC[FCP_ss][mat_def]
QED

Theorem MATRIX_CMUL_ASSOC :
   !a b X:real['N]['M]. a * (b * X) = (a * b) * X
Proof
  SRW_TAC[FCP_ss][matrix_cmul_def, REAL_MUL_ASSOC]
QED

Theorem MATRIX_CMUL_LID :
   !X:real['N]['M]. &1 * X = X
Proof
  SRW_TAC[FCP_ss][matrix_cmul_def, REAL_MUL_LID]
QED

Theorem MATRIX_ADD_SYM :
   !A:real['N]['M] B. A + B = B + A
Proof
  SRW_TAC[FCP_ss][matrix_add_def, REAL_ADD_SYM]
QED

Theorem MATRIX_ADD_ASSOC :
   !A:real['N]['M] B C. A + (B + C) = (A + B) + C
Proof
  SRW_TAC[FCP_ss][matrix_add_def, REAL_ADD_ASSOC]
QED

Theorem MATRIX_ADD_LID :
   !A:real['N]['M]. mat 0 + A = A
Proof
  SRW_TAC[FCP_ss][matrix_add_def, mat_def, COND_ID, REAL_ADD_LID]
QED

Theorem MATRIX_ADD_RID :
   !A:real['N]['M]. A + mat 0 = A
Proof
  SRW_TAC[FCP_ss][matrix_add_def, mat_def, COND_ID, REAL_ADD_LID]
QED

Theorem MATRIX_ADD_LNEG :
   !A:real['N]['M]. ~A + A = mat 0
Proof
  SRW_TAC[FCP_ss][matrix_neg_def, matrix_add_def, mat_def, COND_ID, REAL_ADD_LINV]
QED

Theorem MATRIX_ADD_RNEG :
   !A:real['N]['M]. A + ~A = mat 0
Proof
  SRW_TAC[FCP_ss][matrix_neg_def, matrix_add_def, mat_def, COND_ID, REAL_ADD_RINV]
QED

Theorem MATRIX_SUB :
   !A:real['N]['M] B. A - B = A + ~B
Proof
  SRW_TAC[FCP_ss][matrix_neg_def, matrix_add_def, matrix_sub_def, real_sub]
QED

Theorem MATRIX_SUB_REFL :
   !A:real['N]['M]. A - A = mat 0
Proof
  REWRITE_TAC[MATRIX_SUB, MATRIX_ADD_RNEG]
QED

(* |- !f g s. (!x. x IN s ==> f x = g x) ==> sum s f = sum s g *)
Theorem SUM_EQ[local] = SUM_EQ'

(* |- !f g s. FINITE s ==> sum s (\x. f x + g x) = sum s f + sum s g *)
Theorem SUM_ADD[local] = SUM_ADD'

Theorem MATRIX_ADD_LDISTRIB :
   !A:real['P]['M] B:real['N]['P] C. A ** (B + C) = A ** B + A ** C
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_add_def, GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_EQ THEN
  SRW_TAC[FCP_ss][REAL_ADD_LDISTRIB]
QED

Theorem VECTOR_DOT_FCP2 :
  !f u v. (($FCP f :real['N]) dot v) =
           sum (count (dimindex(:'N))) (\i. f i * (v ' i)) /\
          (u dot ($FCP f :real['N])) =
           sum (count (dimindex(:'N))) (\i. (u ' i) * f i)
Proof
    SRW_TAC [FCP_ss] [dot_def, SUM_EQ]
QED

Theorem MATRIX_MUL_EQ :
    !A:real['P]['M] B:real['N]['P] k:real.
        (FCP i j. sum (count(dimindex(:'P))) (\k. A ' i ' k * B ' k ' j)) =
        (FCP i j. (row i A) dot (column j B)): real['N]['M]
Proof
    SRW_TAC[FCP_ss][dot_def, row_def, column_def] THEN
    MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]
QED

Theorem MATRIX_MUL_ASSOC :
    !(A:real['N]['M]) (B:real['P]['N]) (C:real['Q]['P]).
      (A ** B) ** C = A ** (B ** C)
Proof
    SRW_TAC [FCP_ss][matrix_mul_def, MATRIX_MUL_EQ, ROW_FCP, COLUMN_FCP, VECTOR_DOT_FCP2] THEN
    rename1 ‘j < dimindex(:'Q)’ \\
    SRW_TAC [][dot_def, GSYM SUM_LMUL, GSYM SUM_RMUL] THEN
    SRW_TAC [][Once SUM_SWAP] THEN
    MATCH_MP_TAC SUM_EQ THEN
    Q.X_GEN_TAC ‘k’ >> SRW_TAC [][] THEN
    MATCH_MP_TAC SUM_EQ THEN
    Q.X_GEN_TAC ‘l’ >> SRW_TAC [][] THEN
    SRW_TAC [FCP_ss][row_def, column_def]
QED

Theorem MATRIX_MUL_LMUL :
   !A:real['N]['M] B:real['P]['N] c. (c * A) ** B = c * (A ** B)
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def, MATRIX_CMUL_COMPONENT] THEN
  rename1 ‘j < dimindex(:'P)’ \\
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'N))) (\k. c * (A ' i ' k * B ' k ' j))` THEN
  CONJ_TAC
  >- (MATCH_MP_TAC SUM_EQ THEN
      SRW_TAC[FCP_ss][MATRIX_CMUL_COMPONENT, REAL_MUL_ASSOC]) THEN
  SIMP_TAC bool_ss[SUM_LMUL]
QED

Theorem MATRIX_MUL_RMUL :
   !A:real['N]['M] B:real['P]['N] c. A ** (c * B) = c * (A ** B)
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def, MATRIX_CMUL_COMPONENT] THEN
  rename1 ‘j < dimindex(:'P)’ \\
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'N))) (\k. c * (A ' i ' k * B ' k ' j))` THEN
  CONJ_TAC
  >- (MATCH_MP_TAC SUM_EQ THEN
      SRW_TAC[FCP_ss][MATRIX_CMUL_COMPONENT]) THEN
  SIMP_TAC bool_ss[SUM_LMUL]
QED

Theorem MATRIX_VECTOR_MUL_ASSOC :
   !A:real['N]['M] B:real['P]['N] x:real['P]. A ** B ** x = (A ** B) ** x
Proof
  REPEAT GEN_TAC THEN
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'N)))
    (\j. A ' i ' j *
         sum (count (dimindex (:'P))) (\k. B ' j ' k * x ' k))` THEN
  CONJ_TAC >- (MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'P)))
    (\j. sum (count (dimindex (:'N))) (\k. A ' i ' k * B ' k ' j) * x ' j)` THEN
  reverse CONJ_TAC >- (MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]) THEN
  REWRITE_TAC[GSYM SUM_LMUL, GSYM SUM_RMUL] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  SIMP_TAC bool_ss[Once SUM_SWAP, FINITE_COUNT]
QED

(* NOTE: here ‘mat 1’ must be a NxN square matrix *)
Theorem MATRIX_VECTOR_MUL_LID :
   !x:real['N]. (mat 1 :real['N]['N]) ** x = x
Proof
  REWRITE_TAC[matrix_vector_mul_def,
   GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[EQ_SYM_EQ]
    (SPEC_ALL mat_def)] THEN
  SRW_TAC[FCP_ss][] THEN MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `sum (count (dimindex (:'N)))(\j. (if j = i then 1 else 0) * x ' j)` THEN
  CONJ_TAC >- (MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]) \\
  REWRITE_TAC[COND_RATOR, COND_RAND] THEN
  ASM_SIMP_TAC bool_ss[SUM_DELTA, REAL_MUL_LZERO, IN_COUNT, REAL_MUL_LID]
QED

Theorem MATRIX_VECTOR_MUL_LZERO :
   !x:real['N]. (mat 0 :real['N]['M]) ** x = vec 0
Proof
  SRW_TAC[FCP_ss][mat_def, matrix_vector_mul_def, VEC_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `sum (count (dimindex (:'N))) (\j. 0 * x ' j)` THEN
  CONJ_TAC >- (MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]) \\
  REWRITE_TAC[REAL_MUL_LZERO, SUM_0']
QED

Theorem MATRIX_VECTOR_MUL_RZERO :
   !A:real['N]['M]. A ** (vec 0) = (vec 0)
Proof
  SRW_TAC[FCP_ss][matrix_vector_mul_def, VEC_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `sum (count (dimindex (:'N))) (\j. 0)` THEN
  reverse CONJ_TAC >- REWRITE_TAC[SUM_0'] \\
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][VEC_COMPONENT]
QED

Theorem MATRIX_TRANSP_MUL :
   !A:real['N]['M] B. transp(A ** B) = transp(B) ** transp(A)
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, transp_def] THEN
  MATCH_MP_TAC SUM_EQ THEN
  SRW_TAC[FCP_ss][Once REAL_MUL_SYM]
QED

Theorem MATRIX_EQ :
   !A:real['N]['M] B. (A = B) <=> !x:real['N]. A ** x = B ** x
Proof
  REPEAT GEN_TAC THEN EQ_TAC >- PROVE_TAC[] THEN
  DISCH_THEN(MP_TAC o GEN ``i:num`` o SPEC ``(basis i):real['N]``) THEN
  SIMP_TAC (bool_ss ++ FCP_ss) [CART_EQ, matrix_vector_mul_def, basis_def] THEN
  Q.SUBGOAL_THEN `!i i'.
   (sum (count (dimindex (:'N)))
   (\j. A:real['N]['M] ' i' ' j * (FCP i'. if i' = i then 1 else 0):real['N] ' j) =
        sum (count (dimindex (:'N)))
   (\j. A ' i' ' j * if j = i then 1 else 0))` ASSUME_TAC
   >- (REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]) THEN
  Q.SUBGOAL_THEN `!i i'.
   (sum (count (dimindex (:'N)))
   (\j. B:real['N]['M] ' i' ' j * (FCP i'. if i' = i then 1 else 0):real['N] ' j) =
        sum (count (dimindex (:'N)))
   (\j. B ' i' ' j * if j = i then 1 else 0))` ASSUME_TAC
   >- (REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC bool_ss[SUM_DELTA, COND_RAND, REAL_MUL_RZERO, REAL_MUL_RID, IN_COUNT]
QED

Theorem TRANSP_MAT :
   !n. transp(mat n) = mat n :real['M]['N]
Proof
  SRW_TAC[FCP_ss][transp_def, mat_def, EQ_SYM_EQ]
QED

Theorem TRANSP_TRANSP :
   !A:real['N]['M]. transp(transp A) = A
Proof
  SRW_TAC[FCP_ss][transp_def]
QED

Theorem TRANSP_EQ :
   !A B:real['N]['M]. (transp A = transp B) <=> (A = B)
Proof
  PROVE_TAC[TRANSP_TRANSP]
QED

Theorem ROW_TRANSP :
   !A:real['N]['M] i.
        i < dimindex(:'N) ==> (row i (transp A) = column i A)
Proof
  SRW_TAC[FCP_ss][row_def, column_def, transp_def]
QED

Theorem COLUMN_TRANSP :
   !A:real['N]['M] i.
        i < dimindex(:'M) ==> (column i (transp A) = row i A)
Proof
  SRW_TAC[FCP_ss][row_def, column_def, transp_def]
QED

Theorem ROWS_TRANSP :
   !A:real['N]['M]. rows(transp A) = columns A
Proof
  REWRITE_TAC[rows_def, columns_def, EXTENSION] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[ROW_TRANSP]
QED

Theorem COLUMNS_TRANSP :
   !A:real['N]['M]. columns(transp A) = rows A
Proof
  PROVE_TAC[TRANSP_TRANSP, ROWS_TRANSP]
QED

Theorem VECTOR_MATRIX_MUL_TRANSP :
   !A:real['N]['M] x:real['M]. x ** A = transp A ** x
Proof
  REWRITE_TAC[matrix_vector_mul_def, vector_matrix_mul_def, transp_def] THEN
  SRW_TAC[FCP_ss][] THEN MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN SRW_TAC[FCP_ss][]
QED

Theorem MATRIX_VECTOR_MUL_TRANSP :
   !A:real['N]['M] x:real['N]. A ** x = x ** transp A
Proof
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP, TRANSP_TRANSP]
QED

Theorem MATRIX_MUL_LID :
   !A:real['N]['M]. mat 1 ** A = A
Proof
   REPEAT GEN_TAC THEN SRW_TAC [FCP_ss][matrix_mul_def, mat_def]
   THEN MATCH_MP_TAC EQ_TRANS
   THEN Q.EXISTS_TAC `sum (count (dimindex (:'M)))(\k. if k = i then A ' k ' i' else 0)`
   THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN SRW_TAC [][] THEN SRW_TAC [FCP_ss][],
    ASM_SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT]]
QED

Theorem MATRIX_MUL_RID :
   !A:real['N]['M]. A ** mat 1 = A
Proof
   REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM TRANSP_EQ]
   THEN ONCE_REWRITE_TAC[MATRIX_TRANSP_MUL]
   THEN REWRITE_TAC[TRANSP_MAT]
   THEN MATCH_ACCEPT_TAC MATRIX_MUL_LID
QED

(* ------------------------------------------------------------------------- *)
(* Two sometimes fruitful ways of looking at matrix-vector multiplication.   *)
(* ------------------------------------------------------------------------- *)

Theorem MATRIX_MUL_DOT :
   !A:real['N]['M] x. A ** x = FCP i. A ' i dot x
Proof
  REWRITE_TAC[matrix_vector_mul_def, dot_def] THEN SRW_TAC[FCP_ss][]
QED

Theorem MATRIX_MUL_VSUM :
   !A:real['N]['M] x. A ** x = vsum(count(dimindex(:'N))) (\i. x ' i * column i A)
Proof
  SRW_TAC[FCP_ss][matrix_vector_mul_def, VSUM_COMPONENT, VECTOR_MUL_COMPONENT,
                  column_def, Once REAL_MUL_SYM]
QED

(* ------------------------------------------------------------------------- *)
(* Slightly gruesome lemmas: better to define sums over vectors really...    *)
(* ------------------------------------------------------------------------- *)

Overload SUM[local] = “iterate$Sum”
Overload ADJOINT[local] = “adjoint”

Theorem VECTOR_COMPONENTWISE :
  !x:real['N].
    x = FCP j. SUM(count(dimindex(:'N)))
                     (\i. x ' i * (basis i :real['N]) ' j)
Proof
  SRW_TAC[FCP_ss][basis_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[EQ_SYM_EQ] THEN
  ASM_SIMP_TAC bool_ss[COND_RAND, REAL_MUL_RZERO, SUM_DELTA, IN_COUNT] THEN
  REWRITE_TAC[REAL_MUL_RID]
QED

Theorem LT_REFL[local] = LESS_ANTISYM;

(* vec 0 := |- 0 = FCP i. 0 *)
fun vec (n:int) = SPEC (term_of_int n) vec_def;

Theorem LINEAR_COMPONENTWISE :
   !f:real['M]->real['N].
      linear(f)
      ==> !x j. j < dimindex(:'N)
                ==> (f x ' j =
                     SUM(count(dimindex(:'M))) (\i. x ' i * f(basis i) ' j))
Proof
  REWRITE_TAC[linear_def] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) empty_rewrites
   [VECTOR_COMPONENTWISE] THEN
  Q.SPEC_TAC(`dimindex(:'M)`,`n:num`) THEN
  INDUCT_TAC THEN
  SIMP_TAC std_ss[COUNT_ZERO, COUNT_SUC, FINITE_COUNT, IN_COUNT, SUM_CLAUSES, LT_REFL] THENL
  [ (* goal 1 (of 2) *)
    REWRITE_TAC[GSYM (vec 0)] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) empty_rewrites
     [GSYM VECTOR_MUL_LZERO] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC bool_ss[VEC_COMPONENT],
    (* goal 2 (of 2) *)
    ASSUM_LIST(fn thl => REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC bool_ss[GSYM VECTOR_MUL_COMPONENT,
             ASSUME ``j < dimindex(:'N)``] THEN
    ASSUM_LIST(fn thl => REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC bool_ss[GSYM VECTOR_ADD_COMPONENT,
             ASSUME ``j < dimindex(:'N)``] THEN
    ASSUM_LIST(fn thl => REWRITE_TAC(map GSYM thl)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SRW_TAC [FCP_ss][VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] ]
QED

(* ------------------------------------------------------------------------- *)
(* Inverse matrices (not necessarily square, but it's vacuous otherwise).    *)
(* ------------------------------------------------------------------------- *)

Definition invertible_def :
   invertible(A:real['N]['M]) =
        ?A':real['M]['N]. (A ** A' = mat 1) /\ (A' ** A = mat 1)
End

Definition MATRIX_INV_DEF :
   MATRIX_INV(A:real['N]['M]) =
        @A':real['M]['N]. (A ** A' = mat 1) /\ (A' ** A = mat 1)
End

Theorem MATRIX_INV :
  !A:real['N]['M].
    invertible A ==> (A ** MATRIX_INV A = mat 1) /\ (MATRIX_INV A ** A = mat 1)
Proof
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MATRIX_INV_DEF, invertible_def] THEN
  CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[GSYM invertible_def]
QED

Theorem INVERTIBLE_MATRIX_INV :
   !A:real['N]['N]. invertible A ==> invertible(MATRIX_INV A)
Proof
 METIS_TAC[MATRIX_INV, invertible_def]
QED

Theorem MATRIX_RMUL_EQ :
   !A:real['N]['M] (X Y):real['M]['P]. invertible A ==> ((X = Y) = (X ** A = Y ** A))
Proof
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]
QED

Theorem MATRIX_LMUL_EQ :
   !A:real['N]['M] (X Y):real['P]['N]. invertible A ==> ((X = Y) = (A ** X = A ** Y))
Proof
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]
QED

Theorem MATRIX_RMUL_INV_EQ :
   !A:real['N]['M] (X Y):real['N]['P]. invertible A ==>
      ((X = Y) <=> (X ** MATRIX_INV A = Y ** MATRIX_INV A))
Proof
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]
QED

Theorem MATRIX_LMUL_INV_EQ :
    !A:real['N]['M] (X Y):real['P]['M]. invertible A ==>
       ((X = Y) <=> (MATRIX_INV A ** X = MATRIX_INV A ** Y))
Proof
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]
QED

Theorem MATRIX_EQ_RMUL :
   !(A B C):real['N]['N]. invertible C /\ (A ** C = B ** C) ==> (A = B)
Proof
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_ASSOC]
QED

Theorem MATRIX_EQ_LMUL :
   !(A B C):real['N]['N]. invertible C /\ (C ** A  = C ** B)==> (A = B)
Proof
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]
QED

Theorem MATRIX_INV_INV :
   !(A B):real['N]['N]. invertible A ==>(MATRIX_INV(MATRIX_INV A) = A)
Proof
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, INVERTIBLE_MATRIX_INV, MATRIX_RMUL_INV_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* Correspondence between matrices and linear operators.                     *)
(* ------------------------------------------------------------------------- *)

Definition matrix_def :
   (matrix:(real['M]->real['N])->real['M]['N]) f = FCP i j. f(basis j) ' i
End

Theorem MATRIX_VECTOR_MUL_LINEAR :
   !A:real['N]['M]. linear(\x. A ** x)
Proof
  REWRITE_TAC[linear_def, matrix_vector_mul_def] THEN
  SRW_TAC[FCP_ss][VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_ADD_COUNT, GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN
  SRW_TAC[FCP_ss][VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, IN_COUNT] THEN REAL_ARITH_TAC
QED

Theorem MATRIX_WORKS :
   !f:real['M]->real['N]. linear f ==> !x. matrix f ** x = f(x)
Proof
  REWRITE_TAC[matrix_def, matrix_vector_mul_def] THEN
  SRW_TAC[FCP_ss][] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `SUM (count (dimindex (:'M))) (\j. x ' j * f (basis j) ' i)` THEN
  CONJ_TAC THENL[MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][],
  ASM_SIMP_TAC bool_ss[GSYM LINEAR_COMPONENTWISE]]
QED

Theorem MATRIX_VECTOR_MUL :
   !f:real['M]->real['N]. linear f ==> (f = \x. matrix f ** x)
Proof
  SIMP_TAC bool_ss[FUN_EQ_THM, MATRIX_WORKS]
QED

Theorem MATRIX_OF_MATRIX_VECTOR_MUL :
   !A:real['N]['M]. matrix(\x. A ** x) = A
Proof
  SIMP_TAC bool_ss[MATRIX_EQ, MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS]
QED

Theorem MATRIX_COMPOSE :
   !f g. linear f /\ linear g ==> (matrix(g o f) = matrix g ** matrix f)
Proof
  SIMP_TAC bool_ss[MATRIX_EQ, MATRIX_WORKS, LINEAR_COMPOSE,
           GSYM MATRIX_VECTOR_MUL_ASSOC, o_THM]
QED

Theorem MATRIX_VECTOR_COLUMN :
   !A:real['N]['M] x.
        A ** x = vsum(count(dimindex(:'N))) (\i. x ' i * (transp A) ' i)
Proof
  REWRITE_TAC[matrix_vector_mul_def, transp_def] THEN
  SRW_TAC[FCP_ss][VSUM_COMPONENT, VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][Once REAL_MUL_COMM]
QED

Theorem MATRIX_MUL_COMPONENT :
   !(A:real['N]['N]) (B:real['N]['N]) i. i < dimindex(:'N)
       ==> ((A ** B) ' i = transp B ** A ' i)
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def, vector_matrix_mul_def,transp_def] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][Once REAL_MUL_COMM]
QED

Theorem ADJOINT_MATRIX :
   !A:real['N]['M]. ADJOINT(\x. A ** x) = (\x. transp A ** x)
Proof
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN REPEAT GEN_TAC THEN
  SIMP_TAC bool_ss[transp_def, dot_def, matrix_vector_mul_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
  `SUM (count (dimindex (:'N)))
       (\i. SUM (count (dimindex (:'M)))(\j. A ' j ' i * x ' j) * y ' i)` THEN
  CONJ_TAC THENL[
        MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][] THEN DISJ2_TAC THEN
        MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][],
        ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
  `SUM (count (dimindex (:'M)))
       (\i. x ' i * SUM (count (dimindex (:'N))) (\j. A ' i ' j * y ' j))` THEN
  CONJ_TAC THENL[
        REWRITE_TAC[GSYM SUM_LMUL, GSYM SUM_RMUL] THEN SIMP_TAC bool_ss[Once SUM_SWAP_COUNT] THEN
        MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][] THEN
        MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][] THEN REAL_ARITH_TAC,
        ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]
QED

Theorem MATRIX_ADJOINT :
   !f. linear f ==> (matrix(adjoint f) = transp(matrix f))
Proof
  GEN_TAC THEN DISCH_THEN
   (fn th => GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) empty_rewrites
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
  REWRITE_TAC[ADJOINT_MATRIX, MATRIX_OF_MATRIX_VECTOR_MUL]
QED

Theorem MATRIX_ID :
   matrix(\x. x) = mat 1
Proof
  SIMP_TAC bool_ss[MATRIX_EQ, LINEAR_ID, MATRIX_WORKS, MATRIX_VECTOR_MUL_LID]
QED

Theorem MATRIX_I :
   matrix I = mat 1
Proof
  SIMP_TAC bool_ss[I_DEF, S_DEF, K_DEF, MATRIX_ID]
QED

Theorem LINEAR_EQ_MATRIX :
   !f g. linear f /\ linear g /\ (matrix f = matrix g) ==> (f = g)
Proof
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MATRIX_VECTOR_MUL)) THEN
  ASM_REWRITE_TAC[]
QED

Theorem MATRIX_SELF_ADJOINT :
   !f. linear f ==> ((adjoint f = f) <=> (transp(matrix f) = matrix f))
Proof
  SIMP_TAC bool_ss[GSYM MATRIX_ADJOINT] THEN
  PROVE_TAC[LINEAR_EQ_MATRIX, ADJOINT_LINEAR]
QED

(* ------------------------------------------------------------------------- *)
(* Detailed theorems about left and right invertibility in general case.     *)
(* ------------------------------------------------------------------------- *)

Theorem LEFT_INVERTIBLE_TRANSP :
   !A:real['N]['M].
    (?B:real['N]['M]. B ** transp A = mat 1) <=> (?B:real['M]['N]. A ** B = mat 1)
Proof
  PROVE_TAC[MATRIX_TRANSP_MUL, TRANSP_MAT, TRANSP_TRANSP]
QED

Theorem RIGHT_INVERTIBLE_TRANSP :
   !A:real['N]['M].
    (?B:real['N]['M]. transp A ** B = mat 1) <=> (?B:real['M]['N]. B ** A = mat 1)
Proof
  PROVE_TAC[MATRIX_TRANSP_MUL, TRANSP_MAT, TRANSP_TRANSP]
QED

Theorem MATRIX_LEFT_INVERTIBLE_INJECTIVE :
   !A:real['N]['M].
        (?B:real['M]['N]. B ** A = mat 1) <=>
        !x y:real['N]. (A ** x = A ** y) ==> (x = y)
Proof
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM ``\x:real['M]. (B:real['M]['N]) ** x``) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    DISCH_TAC THEN MP_TAC(Q.ISPEC
     `\x:real['N]. (A:real['N]['M]) ** x` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_SIMP_TAC bool_ss[MATRIX_VECTOR_MUL_LINEAR, FUN_EQ_THM, I_THM, o_THM] THEN
    DISCH_THEN (Q.X_CHOOSE_THEN `g:real['M]->real['N]` STRIP_ASSUME_TAC) THEN
    Q.EXISTS_TAC `matrix(g):real['M]['N]` THEN
    REWRITE_TAC[MATRIX_EQ, MATRIX_VECTOR_MUL_LID] THEN
    PROVE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS]]
QED

Theorem MATRIX_LEFT_INVERTIBLE_KER :
   !A:real['N]['M].
        (?B:real['M]['N]. B ** A = mat 1) <=> !x. (A ** x = (vec 0)) ==> (x = (vec 0))
Proof
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  HO_MATCH_MP_TAC LINEAR_INJECTIVE_0 THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]
QED

Theorem MATRIX_RIGHT_INVERTIBLE_SURJECTIVE :
   !A:real['N]['M].
        (?B:real['M]['N]. A ** B = mat 1) <=> !y. ?x. A ** x = y
Proof
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN Q.X_GEN_TAC `y:real['M]` THEN
    Q.EXISTS_TAC `(B:real['M]['N]) ** (y:real['M])` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    DISCH_TAC THEN MP_TAC (Q.ISPEC
     `\x:real['N]. (A:real['N]['M]) ** x` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    ASM_SIMP_TAC bool_ss[MATRIX_VECTOR_MUL_LINEAR, FUN_EQ_THM, I_THM, o_THM] THEN
    DISCH_THEN (Q.X_CHOOSE_THEN `g:real['M]->real['N]` STRIP_ASSUME_TAC) THEN
    Q.EXISTS_TAC `matrix(g):real['M]['N]` THEN
    REWRITE_TAC[MATRIX_EQ, MATRIX_VECTOR_MUL_LID] THEN
    PROVE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS]]
QED

Theorem MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS :
   !A:real['N]['M]. (?B:real['M]['N]. B ** A = mat 1) <=>
                !c. (vsum(count(dimindex(:'N))) (\i. c(i) * column i A) = (vec 0)) ==>
                    !i. i < dimindex(:'N) ==> (c(i) = &0)
Proof
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_KER, MATRIX_MUL_VSUM] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [Q.X_GEN_TAC `c:num->real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC ``(FCP i. c(i)):real['N]``),
    Q.X_GEN_TAC `x:real['N]` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC ``\i. (x:real['N]) ' i``) THEN BETA_TAC] THEN
  Q.SUBGOAL_THEN `vsum (count (dimindex (:'N))) (\i. (FCP i. c i):real['N] ' i * column i A) =
    vsum (count (dimindex (:'N))) (\i. c i * column i A)` ASSUME_TAC THENL
    [MATCH_MP_TAC VSUM_EQ THEN SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT], ALL_TAC,
     MATCH_MP_TAC VSUM_EQ THEN SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT], ALL_TAC] THEN
  SRW_TAC[FCP_ss][VEC_COMPONENT]
QED

Theorem MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS :
   !A:real['N]['M]. (?B:real['M]['N]. A ** B = mat 1) <=>
                !c. (vsum(count(dimindex(:'M))) (\i. c(i) * row i A) = (vec 0)) ==>
                    !i. i < dimindex(:'M) ==> (c(i) = &0)
Proof
  ONCE_REWRITE_TAC[GSYM LEFT_INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS] THEN
  Q.SUBGOAL_THEN `!A:real['N]['M] c:num->real.
                vsum (count (dimindex (:'M))) (\i. c i * column i (transp A))=
                vsum (count (dimindex (:'M))) (\i. c i * row i A)` ASSUME_TAC THENL
        [REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN SRW_TAC[FCP_ss][COLUMN_TRANSP], ALL_TAC] THEN
  ASM_REWRITE_TAC[]
QED

Theorem MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS :
   !A:real['N]['M]. (?B:real['M]['N]. A ** B = mat 1) <=> (span(columns A) = (UNIV:real['M]->bool))
Proof
  GEN_TAC THEN REWRITE_TAC[MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  REWRITE_TAC[MATRIX_MUL_VSUM, EXTENSION, IN_UNIV] THEN
  AP_TERM_TAC THEN SIMP_TAC bool_ss[FUN_EQ_THM] THEN Q.X_GEN_TAC `y:real['M]` THEN
  EQ_TAC THENL
   [DISCH_THEN (Q.X_CHOOSE_THEN `x:real['N]` (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC SPAN_VSUM THEN SIMP_TAC bool_ss[FINITE_COUNT, IN_COUNT] THEN
    Q.X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    REWRITE_TAC[columns_def] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[],
    ALL_TAC] THEN
  Q.SPEC_TAC(`y:real['M]`,`y:real['M]`) THEN HO_MATCH_MP_TAC SPAN_INDUCT_ALT THEN
  CONJ_TAC THENL
   [Q.EXISTS_TAC `(vec 0) :real['N]` THEN
    MATCH_MP_TAC EQ_TRANS THEN
    Q.EXISTS_TAC `vsum (count (dimindex (:'N))) (\i.(vec 0) :real['M])` THEN
    CONJ_TAC THENL[MATCH_MP_TAC VSUM_EQ, ALL_TAC] THEN
    SRW_TAC[FCP_ss][VEC_COMPONENT, VECTOR_MUL_LZERO, VSUM_0],
    ALL_TAC] THEN
  MAP_EVERY Q.X_GEN_TAC [`c:real`, `y1:real['M]`, `y2:real['M]`] THEN
  REWRITE_TAC[columns_def] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (Q.X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
   (Q.X_CHOOSE_THEN `x:real['N]` (SUBST1_TAC o SYM))) THEN
  Q.EXISTS_TAC `(FCP j. if j = i then c + (x:real['N]) ' i else x ' j):real['N]` THEN
  Q.SUBGOAL_THEN `count (dimindex (:'N)) = i INSERT (count (dimindex (:'N)) DELETE i)`
  SUBST1_TAC THENL [PROVE_TAC[INSERT_DELETE, IN_COUNT], ALL_TAC] THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_DELETE, FINITE_COUNT, IN_DELETE] THEN
  ASM_SIMP_TAC bool_ss[FCP_BETA, VECTOR_ADD_RDISTRIB, VECTOR_ADD_ASSOC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  SIMP_TAC bool_ss[FINITE_DELETE, IN_DELETE, FINITE_COUNT, FCP_BETA, IN_COUNT]
QED

Theorem MATRIX_LEFT_INVERTIBLE_SPAN_ROWS :
   !A:real['N]['M]. (?B:real['M]['N]. B ** A = mat 1) <=> (span(rows A) = (UNIV:real['N]->bool))
Proof
  PROVE_TAC[RIGHT_INVERTIBLE_TRANSP, COLUMNS_TRANSP,
            MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS]
QED

(* ------------------------------------------------------------------------- *)
(* Invertibility of matrices and corresponding linear functions.             *)
(* ------------------------------------------------------------------------- *)

Theorem MATRIX_LEFT_RIGHT_INVERSE :
   !A:real['N]['N] A':real['N]['N]. (A ** A' = mat 1) <=> (A' ** A = mat 1)
Proof
  Q.SUBGOAL_THEN
    `!A:real['N]['N] A':real['N]['N]. (A ** A' = mat 1) ==> (A' ** A = mat 1)`
    (fn th => PROVE_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.ISPEC `\x:real['N]. (A:real['N]['N]) ** x`
    LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  SIMP_TAC bool_ss[MATRIX_VECTOR_MUL_LINEAR] THEN
  Q.SUBGOAL_THEN `!y:real['N]. ?x. (A:real['N]['N]) ** x = y` ASSUME_TAC THENL
   [Q.X_GEN_TAC `x:real['N]` THEN
    Q.EXISTS_TAC `(A':real['N]['N]) ** (x:real['N])` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `f':real['N]->real['N]` STRIP_ASSUME_TAC) THEN
  Q.SUBGOAL_THEN `matrix (f':real['N]->real['N]) ** (A:real['N]['N]) = mat 1`
  MP_TAC THENL
   [ASM_SIMP_TAC bool_ss[MATRIX_EQ, MATRIX_WORKS, GSYM MATRIX_VECTOR_MUL_ASSOC,
                 MATRIX_VECTOR_MUL_LID],
    ALL_TAC] THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o AP_TERM ``(\m:real['N]['N]. m ** (A':real['N]['N]))``) THEN
  SIMP_TAC bool_ss[MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RID, MATRIX_MUL_LID] THEN PROVE_TAC[]
QED

Theorem MATRIX_LEFT_INVERTIBLE :
   !f:real['M]->real['N].
    linear f ==> ((?B:real['N]['M]. B ** matrix f = mat 1) <=>
                  (?g. linear g /\ (g o f = I)))
Proof
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [Q.EXISTS_TAC `\y:real['N]. (B:real['N]['M]) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_SIMP_TAC bool_ss[FUN_EQ_THM, o_THM, I_THM, MATRIX_VECTOR_MUL_ASSOC,
                    MATRIX_VECTOR_MUL_LID],
    Q.EXISTS_TAC `matrix(g:real['N]->real['M])` THEN
    ASM_SIMP_TAC bool_ss[GSYM MATRIX_COMPOSE, MATRIX_I]]
QED

Theorem MATRIX_RIGHT_INVERTIBLE :
   !f:real['M]->real['N].
    linear f ==> ((?B:real['N]['M]. matrix f ** B = mat 1) <=>
                  (?g. linear g /\ (f o g = I)))
Proof
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [Q.EXISTS_TAC `\y:real['N]. (B:real['N]['M]) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fn th => GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_SIMP_TAC bool_ss[FUN_EQ_THM, o_THM, I_THM, MATRIX_VECTOR_MUL_ASSOC,
                    MATRIX_VECTOR_MUL_LID],
    Q.EXISTS_TAC `matrix(g:real['N]->real['M])` THEN
    ASM_SIMP_TAC bool_ss[GSYM MATRIX_COMPOSE, MATRIX_I]]
QED

(* NOTE: the following theorem(s) cannot be parsed in the modern syntax *)
val INVERTIBLE_LEFT_INVERSE = store_thm
  ("INVERTIBLE_LEFT_INVERSE",
   “!A:real['N]['N]. invertible(A) <=> ?B:real['N]['N]. B ** A = mat 1”,
 PROVE_TAC[invertible_def, MATRIX_LEFT_RIGHT_INVERSE]);

val INVERTIBLE_RIGHT_INVERSE = store_thm
  ("INVERTIBLE_RIGHT_INVERSE",
   “!A:real['N]['N]. invertible(A) <=> ?B:real['N]['N]. A ** B = mat 1”,
 PROVE_TAC[invertible_def, MATRIX_LEFT_RIGHT_INVERSE]);

Theorem MATRIX_INVERTIBLE :
   !f:real['N]->real['N].
        linear f
        ==> (invertible(matrix f) <=>
             ?g. linear g /\ (f o g = I) /\ (g o f = I))
Proof
  SIMP_TAC bool_ss[INVERTIBLE_LEFT_INVERSE, MATRIX_LEFT_INVERTIBLE] THEN
  PROVE_TAC[LINEAR_INVERSE_LEFT]
QED

Theorem MATRIX_LINV_UNIQ :
   !A B:real['N]['N]. (A ** B = mat 1) ==> (A = MATRIX_INV B)
Proof
 METIS_TAC[MATRIX_RMUL_EQ, MATRIX_INV, INVERTIBLE_LEFT_INVERSE]
QED

Theorem MATRIX_RINV_UNIQ :
   !(A B):real['N]['N]. (A ** B = mat 1) ==> (B = MATRIX_INV A)
Proof
 METIS_TAC[MATRIX_LINV_UNIQ, MATRIX_INV_INV, INVERTIBLE_LEFT_INVERSE]
QED

val _ = export_theory ();
val _ = html_theory "matrix";

(* References:

  [1] Z. Shi, Y. Guan, X. Li, Formalization of Complex Analysis and Matrix Theory,
      Springer, Singapore, 2020. doi:10.1007/978-981-15-7261-6.
 *)
