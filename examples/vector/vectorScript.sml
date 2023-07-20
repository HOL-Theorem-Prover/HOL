(* ========================================================================= *)
(* Vectors in Euclidean space, and elementary linear algebra.                *)
(*     (HOL-Light's Multivariate/vectors.ml, Part I)                         *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*       (c) Copyright, Liming Li, Yong Guan and Zhiping Shi [1] 2011        *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(*       (c) Copyright, Andrea Gabrielli, Marco Maggesi 2016-2017            *)
(*                                                                           *)
(*   NOTE (TODO): "Linear algebra works over any field." [2]                 *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory PairedLambda
     pred_setLib fcpTheory fcpLib tautLib numLib listTheory rich_listTheory
     topologyTheory InductiveDefinition;

open realTheory realLib iterateTheory real_sigmaTheory RealArith mesonLib;
open hurdUtils cardinalTheory permutationTheory;

val _ = new_theory "vector";

val bool_ss' = bool_ss -* ["lift_disj_eq", "lift_imp_disj"];

(* ------------------------------------------------------------------------- *)
(* Basic componentwise operations on vectors.                                *)
(* ------------------------------------------------------------------------- *)

Definition vector_add_def :
   (vector_add :real['N]->real['N]->real['N]) x y = FCP i. x ' i + y ' i
End

Definition vector_sub_def :
   (vector_sub :real['N]->real['N]->real['N]) x y = FCP i. x ' i - y ' i
End

Definition vector_neg_def :
   (vector_neg :real['N]->real['N]) x = FCP i. ~(x ' i)
End

Overload "+"  = “vector_add :real['N] -> real['N] -> real['N]”
Overload "-"  = “vector_sub :real['N] -> real['N] -> real['N]”
Overload "~"              = “vector_neg :real['N] -> real['N]”
Overload "numeric_negate" = “vector_neg :real['N] -> real['N]”

(* Below are equivalent definitions using advanced concepts in fcpTheory *)
Definition FCP_MAP2 :
   FCP_MAP2 f (x :'a['N]) (y :'b['N]) = FCP_MAP (UNCURRY f) (FCP_ZIP x y)
End

Theorem FCP_MAP2_def : (* was: vector_map2_def *)
   !f x y. FCP_MAP2 f (x :'a['N]) (y :'b['N]) = (FCP i. f (x ' i) (y ' i))
Proof
   SRW_TAC [FCP_ss] [FCP_MAP2, FCP_MAP_def, FCP_ZIP_def, UNCURRY_DEF]
QED

Theorem vector_add_alt :
   !x y. (vector_add :real['N]->real['N]->real['N]) x y = FCP_MAP2 (+) x y
Proof
   rw [FCP_MAP2_def, vector_add_def]
QED

Theorem vector_sub_alt :
   !x y. (vector_sub :real['N]->real['N]->real['N]) x y = FCP_MAP2 (-) x y
Proof
   rw [FCP_MAP2_def, vector_sub_def]
QED

Theorem vector_neg_alt :
   !x. (vector_neg :real['N]->real['N]) x = FCP_MAP (~) x
Proof
   rw [FCP_MAP_def, vector_neg_def]
QED

(* ------------------------------------------------------------------------- *)
(* Also the scalar-vector multiplication.                                    *)
(* ------------------------------------------------------------------------- *)

Definition vector_mul_def :
   (vector_mul :real -> real['N] -> real['N]) c x = FCP i. c * x ' i
End

Overload "*" = “vector_mul :real -> real['N] -> real['N]”

Theorem vector_mul_alt :
    !c x. (vector_mul :real -> real['N] -> real['N]) c x = FCP_MAP ($* c) x
Proof
    rw [FCP_MAP_def, vector_mul_def]
QED

(* ------------------------------------------------------------------------- *)
(* Vectors corresponding to small naturals. Perhaps should overload "&"?     *)
(* ------------------------------------------------------------------------- *)

Definition vec_def :
   (vec :num -> real['N]) n = FCP i. &n
End

(* vec 0 := |- 0 = FCP i. 0 *)
fun vec (n:int) = SPEC (term_of_int n) vec_def;

(* this is experimental, for user code only (not used in the rest of file) *)
val _ = add_numeral_form (#"v", SOME "vec");

(* prioritize_real() *)
val _ = prefer_real();

(* ------------------------------------------------------------------------- *)
(* Dot products.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Infixl 600 is the same as "*", "INTER" and "*_c", etc. *)
val _ = set_fixity "dot"  (Infixl 600); (* was: Infixr 20 (HOL-Light) *)

Overload SUM[local] = “iterate$Sum”; (* see iterateTheory.sum_def *)

(* NOTE: The original definition of ‘dot’ in HOL-Light is

     sum(1..dimindex(:N)) (\i. x$i * y$i)

   It seems that in HOL-Light FCP indexes start from 1 (instead of 0 in HOL4),
   and whenever the original proofs use DIMINDEX_GE_1, in the ported proofs we
   should use DIMINDEX_GT_0 instead. (See, e.g., the proof of VEC_EQ below.)
 *)
Definition dot_def :
   ((x:real['N]) dot (y:real['N])) =
     SUM (count(dimindex(:'N))) (\i. (x ' i) * (y ' i))
End

(* alternative definition using ‘real_sigma$SIGMA’ (REAL_SUM_IMAGE_DEF) *)
Theorem dot_alt :
    !x y. ((x:real['N]) dot (y:real['N])) =
          SIGMA (\i. (x ' i) * (y ' i)) (count (dimindex(:'N)))
Proof
    rw [dot_def, GSYM REAL_SUM_IMAGE_sum]
QED

(* ------------------------------------------------------------------------- *)
(* A naive proof procedure to lift really trivial arithmetic stuff from R.   *)
(* ------------------------------------------------------------------------- *)

Theorem SUM_EQ[local] = iterateTheory.SUM_EQ'

val VECTOR_ARITH_TAC =
    rpt GEN_TAC
 >> SIMP_TAC std_ss [dot_def, GSYM SUM_ADD', GSYM SUM_SUB', FINITE_COUNT,
                     GSYM SUM_LMUL, GSYM SUM_RMUL, GSYM SUM_NEG']
 >> (MATCH_MP_TAC SUM_EQ ORELSE MATCH_MP_TAC SUM_EQ_0' ORELSE
     GEN_REWRITE_TAC ONCE_DEPTH_CONV empty_rewrites [CART_EQ])
 >> SIMP_TAC bool_ss[GSYM FORALL_AND_THM] >> TRY EQ_TAC
 >> TRY(HO_MATCH_MP_TAC MONO_ALL) >> TRY GEN_TAC
 >> REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`,
                TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`]
 >> TRY (MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`))
 >> SRW_TAC[FCP_ss][vector_add_def, vector_sub_def, vector_neg_def,
                    vector_mul_def, vec_def]
 >> TRY (POP_ASSUM MP_TAC)
 >> REAL_ARITH_TAC;

fun VECTOR_ARITH tm = prove(tm,VECTOR_ARITH_TAC);

(* ------------------------------------------------------------------------- *)
(* Obvious "component-pushing".                                              *)
(* ------------------------------------------------------------------------- *)

Theorem VEC_COMPONENT :
   !k i. i < dimindex(:'N) ==> (((vec k):real['N]) ' i = &k)
Proof
   SRW_TAC [FCP_ss][vec_def]
QED

Theorem VEC_0_COMPONENT = Q.SPEC ‘0’ VEC_COMPONENT

Theorem VECTOR_ADD_COMPONENT :
   !x:real['N] y i. i < dimindex (:'N) ==> ((x + y) ' i = (x ' i) + (y ' i))
Proof
   SRW_TAC [FCP_ss][vector_add_def]
QED

Theorem VECTOR_NEG_COMPONENT :
   !x:real['N] i. i < dimindex (:'N) ==> ((~x) ' i = -(x ' i))
Proof
   SRW_TAC [FCP_ss][vector_neg_def]
QED

Theorem VECTOR_SUB_COMPONENT :
   !x:real['N] y i. i < dimindex (:'N) ==> ((x - y) ' i = (x ' i) - (y ' i))
Proof
   SRW_TAC [FCP_ss][vector_sub_def]
QED

Theorem VECTOR_MUL_COMPONENT :
   !x:real['N] c i. i < dimindex (:'N) ==> ((c * x) ' i = c * (x ' i))
Proof
   SRW_TAC [FCP_ss][vector_mul_def]
QED

Theorem COND_COMPONENT[local] :
   (if b then x else y) ' i = if b then x ' i else y ' i
Proof
   PROVE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Some frequently useful arithmetic lemmas over vectors.                    *)
(* ------------------------------------------------------------------------- *)

Theorem VECTOR_ADD_SYM = VECTOR_ARITH ``!x y:real['N]. x + y = y + x``

Theorem VECTOR_ADD_LID = VECTOR_ARITH ``!x:real['N]. (vec 0) + x = x``

Theorem VECTOR_ADD_RID = VECTOR_ARITH ``!x:real['N]. x + (vec 0) = x``

Theorem VECTOR_SUB_REFL = VECTOR_ARITH ``!x:real['N]. x - x = (vec 0)``

Theorem VECTOR_ADD_LINV = VECTOR_ARITH ``!x:real['N]. ~x + x = (vec 0)``

Theorem VECTOR_ADD_RINV = VECTOR_ARITH ``!x:real['N]. x + ~x = (vec 0)``

Theorem VECTOR_SUB_RADD = VECTOR_ARITH ``!x y. x - (x + y) = ~y:real['N]``

Theorem VECTOR_NEG_SUB = VECTOR_ARITH ``!x:real['N] y. ~(x - y) = y - x``

Theorem VECTOR_SUB_EQ = VECTOR_ARITH ``!x y:real['N]. (x - y = (vec 0)) <=> (x = y)``

Theorem VECTOR_MUL_ASSOC = VECTOR_ARITH ``!a b x:real['N]. a * (b * x) = (a * b) * x``

Theorem VECTOR_MUL_LID = VECTOR_ARITH ``!x:real['N]. &1 * x = x``

Theorem VECTOR_MUL_LZERO = VECTOR_ARITH ``!x:real['N]. &0 * x = (vec 0)``

Theorem VECTOR_SUB_ADD = VECTOR_ARITH ``(x - y) + y = x:real['N]``

Theorem VECTOR_SUB_ADD2 = VECTOR_ARITH ``y + (x - y) = x:real['N]``

Theorem VECTOR_ADD_LDISTRIB = VECTOR_ARITH ``c * (x + y:real['N]) = c * x + c * y``

Theorem VECTOR_SUB_LDISTRIB = VECTOR_ARITH ``c * (x - y:real['N]) = c * x - c * y``

Theorem VECTOR_ADD_RDISTRIB = VECTOR_ARITH ``(a + b) * x:real['N] = a * x + b * x``

Theorem VECTOR_SUB_RDISTRIB = VECTOR_ARITH ``(a - b) * x:real['N] = a * x - b * x``

Theorem VECTOR_ADD_SUB = VECTOR_ARITH ``(x + y:real['N]) - x = y``

Theorem VECTOR_EQ_ADDR = VECTOR_ARITH ``(x + y = x:real['N]) <=> (y = (vec 0))``

Theorem VECTOR_EQ_ADDL = VECTOR_ARITH ``(x + y = y:real['N]) <=> (x = (vec 0))``

Theorem VECTOR_SUB = VECTOR_ARITH ``x - y = x + ~(y:real['N])``

Theorem VECTOR_SUB_RZERO = VECTOR_ARITH ``x - (vec 0) = x:real['N]``

Theorem VECTOR_MUL_RZERO = VECTOR_ARITH ``c * (vec 0) = (vec 0):real['N]``

Theorem VECTOR_NEG_MINUS1 = VECTOR_ARITH ``~x = (-(&1)) * x:real['N]``

Theorem VECTOR_ADD_ASSOC = VECTOR_ARITH ``(x:real['N]) + (y + z) = x + y + z``

Theorem VECTOR_SUB_LZERO = VECTOR_ARITH ``(vec 0):real['N] - x = ~x``

Theorem VECTOR_NEG_NEG = VECTOR_ARITH ``~(~(x:real['N])) = x``

Theorem VECTOR_MUL_LNEG = VECTOR_ARITH ``~c * x:real['N] = ~(c * x)``

Theorem VECTOR_MUL_RNEG = VECTOR_ARITH ``c * ~x:real['N] = ~(c * x)``

Theorem VECTOR_NEG_0 = VECTOR_ARITH ``~((vec 0)) = (vec 0):real['N]``

(* new *)
Theorem VECTOR_NEG_EQ_0 = VECTOR_ARITH ``~~x = vec 0 <=> x = (vec 0):real['N]``

(* new *)
Theorem VECTOR_EQ_NEG2 = VECTOR_ARITH ``!x y:real['N]. ~~x = ~~y <=> x = y``

Theorem VECTOR_ADD_AC = VECTOR_ARITH
  ``(m + n = n + m:real['N]) /\
    ((m + n) + p = m + n + p) /\
    (m + n + p = n + m + p)``

val LE_REFL = LESS_EQ_REFL;

(* new *)
Theorem VEC_EQ :
    !m n. (vec m = (vec n):real['N]) <=> (m = n)
Proof
    RW_TAC real_ss [CART_EQ, VEC_COMPONENT]
 >> MESON_TAC[DIMINDEX_GT_0] (* was: DIMINDEX_GE_1 here, see dot_def's NOTES *)
QED

(* ------------------------------------------------------------------------- *)
(* Properties of the dot product.                                            *)
(* ------------------------------------------------------------------------- *)

Theorem DOT_SYM = VECTOR_ARITH ``!x y:real['N]. (x dot y) = (y dot x)``

Theorem DOT_LADD = VECTOR_ARITH ``!x y z:real['N]. ((x + y) dot z) = (x dot z) + (y dot z)``

Theorem DOT_RADD = VECTOR_ARITH ``!x y z:real['N]. (x dot (y + z)) = (x dot y) + (x dot z)``

Theorem DOT_LSUB = VECTOR_ARITH ``!x y z:real['N]. ((x - y) dot z) = (x dot z) - (y dot z)``

Theorem DOT_RSUB = VECTOR_ARITH ``!x y z:real['N]. (x dot (y - z)) = (x dot y) - (x dot z)``

Theorem DOT_LMUL = VECTOR_ARITH ``!c x y:real['N]. ((c * x) dot y) = c * (x dot y)``

Theorem DOT_RMUL = VECTOR_ARITH ``!c x y:real['N]. (x dot (c * y)) = c * (x dot y)``

Theorem DOT_LNEG = VECTOR_ARITH ``!x y:real['N]. ((~x) dot y) = ~(x dot y)``

Theorem DOT_RNEG = VECTOR_ARITH ``!x y:real['N]. (x dot (~y)) = ~(x dot y)``

Theorem DOT_LZERO = VECTOR_ARITH ``!x:real['N]. ((vec 0) dot x) = &0``

Theorem DOT_RZERO = VECTOR_ARITH ``!x:real['N]. (x dot (vec 0)) = &0``

(* ------------------------------------------------------------------------- *)
(* Sums of vectors (per-index summation).                                    *)
(* ------------------------------------------------------------------------- *)

Theorem NEUTRAL_VECTOR_ADD :
    neutral(+) = (vec 0):real['N]
Proof
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  BETA_TAC THEN REWRITE_TAC[VECTOR_EQ_ADDR,VECTOR_EQ_ADDL]
QED

Theorem MONOIDAL_VECTOR_ADD :
    monoidal ((+):real['N]->real['N]->real['N])
Proof
  REWRITE_TAC[monoidal, NEUTRAL_VECTOR_ADD] THEN
  REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC
QED

(* NOTE: previously there was a porting mistake (by wrongly written 'a to 'N).

   Here ‘s’ is an index set ('a), ‘f’ is a set of real['N] vectors indexed by ‘s’.
 *)
Definition vsum_def :
   (vsum:('a->bool)->('a->real['N])->real['N]) s f = FCP i. sum s (\x. f(x) ' i)
End

Theorem vsum_alt :
    !s f. FINITE s ==>
         (vsum:('a->bool)->('a->real['N])->real['N]) s f =
          FCP i. SIGMA (\x. f(x) ' i) s
Proof
    rw [vsum_def, GSYM REAL_SUM_IMAGE_sum]
QED

Theorem VSUM_CLAUSES :
   (!(f:'a->real['N]). vsum {} f = (vec 0)) /\
   (!x (f:'a->real['N]) s. FINITE s
            ==> vsum (x INSERT s) f =
                if x IN s then vsum s f else f(x) + vsum s f)
Proof
  SRW_TAC[FCP_ss][vsum_def, VECTOR_ADD_COMPONENT, SUM_CLAUSES, VEC_COMPONENT]
QED

Theorem VSUM :
   !(f:'a->real['N]) s. FINITE s ==> vsum s f = iterate (+) s f
Proof
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, ITERATE_CLAUSES, MONOIDAL_VECTOR_ADD] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD]
QED

Theorem VSUM_EQ_0 :
   !(f:'a->real['N]) s. (!x:'a. x IN s ==> (f(x) = (vec 0))) ==> (vsum s f = (vec 0))
Proof
  SRW_TAC[FCP_ss][vsum_def, vec_def, SUM_EQ_0']
QED

Theorem VSUM_0 :
   (vsum:('a->bool)->('a->real['N])->real['N]) s (\x. (vec 0)) = (vec 0)
Proof
  SIMP_TAC bool_ss[VSUM_EQ_0]
QED

Theorem VSUM_LMUL :
   !(f:'a->real['N]) c s.  vsum s (\x. c * f(x)) = c * vsum s f
Proof
  SRW_TAC[FCP_ss][vsum_def, VECTOR_MUL_COMPONENT, SUM_LMUL]
QED

Theorem VSUM_RMUL :
   !(c :'a->real) s (v :real['N]). vsum s (\x. c x * v) = (sum s c) * v
Proof
  SRW_TAC[FCP_ss][vsum_def, VECTOR_MUL_COMPONENT, SUM_RMUL]
QED

Theorem VSUM_ADD :
   !(f:'a->real['N]) g s. FINITE s ==> (vsum s (\x. f x + g x) = vsum s f + vsum s g)
Proof
  SRW_TAC[FCP_ss][vsum_def, VECTOR_ADD_COMPONENT, SUM_ADD']
QED

Theorem VSUM_SUB :
   !(f:'a->real['N]) g s. FINITE s ==> (vsum s (\x. f x - g x) = vsum s f - vsum s g)
Proof
  SRW_TAC[FCP_ss][vsum_def, VECTOR_SUB_COMPONENT, SUM_SUB']
QED

(* NOTE: there's no ‘i < dimindex(:'N)’ part in HOL-Light *)
Theorem VSUM_COMPONENT :
   !s f i. i < dimindex(:'N) ==> (vsum s (f:'a->real['N])) ' i = sum s (\x. f(x) ' i)
Proof
  SRW_TAC[FCP_ss][vsum_def]
QED

Theorem VSUM_IMAGE :
   !(f :'a->'b) (g :'b->real['N]) s.
        FINITE s /\ (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (vsum (IMAGE f s) g = vsum s (g o f))
Proof
  SRW_TAC[FCP_ss][vsum_def] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
  ASM_SIMP_TAC bool_ss[o_DEF]
QED

Theorem VSUM_DELETE :
   !(f:'a->real['N]) s a. FINITE s /\ a IN s
           ==> (vsum (s DELETE a) f = vsum s f - f a)
Proof
  SRW_TAC[FCP_ss][vsum_def, SUM_DELETE, VECTOR_SUB_COMPONENT]
QED

Theorem VSUM_NEG :
   !(f:'a->real['N]) s. vsum s (\x. ~f x) = ~vsum s f
Proof
  SRW_TAC[FCP_ss][vsum_def, SUM_NEG', VECTOR_NEG_COMPONENT]
QED

Theorem VSUM_EQ :
   !(f:'a->real['N]) g s. (!x. x IN s ==> (f x = g x)) ==> (vsum s f = vsum s g)
Proof
  SRW_TAC[FCP_ss][vsum_def] THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC bool_ss[]
QED

Theorem VSUM_DELETE_CASES :
   !x (f:'a->real['N]) s.
        FINITE(s:'a->bool)
        ==> (vsum (s DELETE x) f = if x IN s then vsum s f - f x else vsum s f)
Proof
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC bool_ss[Q.prove(`~(x IN s) ==> (s DELETE x = s)`,
                               REWRITE_TAC[DELETE_NON_ELEMENT])] THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
   [MATCH_MP (Q.prove(`x IN s ==> (s = x INSERT (s DELETE x))`,
                      PROVE_TAC[INSERT_DELETE])) th]) THEN
  ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN VECTOR_ARITH_TAC
QED

Theorem VSUM_RESTRICT_SET :
   !P s (f:'a->real['N]).
           vsum {x | x IN s /\ P x} f =
           vsum s (\x. if P x then f x else (vec 0))
Proof
  SRW_TAC[FCP_ss][vsum_def, VEC_COMPONENT, SUM_RESTRICT_SET, COND_COMPONENT]
QED

(* ------------------------------------------------------------------------- *)
(* Basis vectors in coordinate directions.                                   *)
(* ------------------------------------------------------------------------- *)

Definition basis_def :
   basis k = ((FCP i. if i = k then &1 else &0):real['N])
End

Theorem BASIS_INJ :
   !i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ (basis i :real['N] = basis j)
     ==> i = j
Proof
  SRW_TAC[FCP_ss][basis_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``i:num``) THEN
  CONV_TAC CONTRAPOS_CONV THEN ASM_SIMP_TAC bool_ss[REAL_10]
QED

Theorem BASIS_NE :
   !i j. i < dimindex(:'N) /\ j < dimindex(:'N) /\ ~(i = j)
     ==> ~(basis i :real['N] = basis j)
Proof
  PROVE_TAC[BASIS_INJ]
QED

Theorem BASIS_COMPONENT :
   !k i. i < dimindex(:'N)
         ==> ((basis k :real['N]) ' i = if i = k then &1 else &0)
Proof
  SRW_TAC[FCP_ss][basis_def]
QED

Theorem BASIS_EXPANSION :
   !(x:real['N]). vsum (count(dimindex(:'N))) (\i. x ' i * basis i) = x
Proof
  SRW_TAC[FCP_ss][VSUM_COMPONENT, VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT, REAL_MUL_RID]
QED

Theorem BASIS_EXPANSION_UNIQUE :
   !u (x:real['N]).
        (vsum (count(dimindex(:'N))) (\i. f(i) * basis i) = x) <=>
        (!i. i < dimindex(:'N) ==> (f(i) = x ' i))
Proof
  SRW_TAC[FCP_ss][VSUM_COMPONENT, VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
  REWRITE_TAC[COND_RAND, REAL_MUL_RZERO, REAL_MUL_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
                   ONCE_DEPTH_CONV) empty_rewrites[EQ_SYM_EQ] THEN
  SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT]
QED

Theorem DOT_BASIS :
   !x:real['N] i. i < dimindex(:'N) ==> (((basis i) dot x) = x ' i) /\
                                        ((x dot (basis i)) = x ' i)
Proof
  REWRITE_TAC[dot_def, basis_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `sum (count (dimindex (:'N))) (\i'. (if i' = i then 1 else 0) * x ' i')` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC,
   MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  REWRITE_TAC[COND_RATOR, COND_RAND, REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT, REAL_MUL_LID]
QED

Theorem VECTOR_EQ_LDOT :
   !y z:real['N]. (!x. (x dot y) = (x dot z)) <=> (y = z)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC bool_ss[] THEN
  REWRITE_TAC[CART_EQ] THEN PROVE_TAC[DOT_BASIS]
QED

Theorem VECTOR_EQ_RDOT :
   !x y:real['N]. (!z. (x dot z) = (y dot z)) <=> (x = y)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC bool_ss[] THEN
  REWRITE_TAC[CART_EQ] THEN PROVE_TAC[DOT_BASIS]
QED

(* ------------------------------------------------------------------------- *)
(* Linear functions.                                                         *)
(* ------------------------------------------------------------------------- *)

(* cf. ‘real_topology$linear’ (real_topologyTheory.linear) *)
Definition linear_def :
   vec_linear (f:real['M]->real['N]) =
       ((!x y. f(x + y) = f(x) + f(y)) /\
        (!c x. f(c * x) = c * f(x)))
End

Overload linear = “vec_linear :(real['M]->real['N])->bool”

Theorem LINEAR_COMPOSE_CMUL :
   !(f:real['M]->real['N]) c. linear f ==> linear (\x. c * f(x))
Proof
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC
QED

Theorem LINEAR_COMPOSE_NEG :
   !(f:real['M]->real['N]). linear f ==> linear (\x. ~(f(x)))
Proof
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC
QED

Theorem LINEAR_COMPOSE_ADD :
   !(f:real['M]->real['N]) g. linear f /\ linear g ==> linear (\x. f(x) + g(x))
Proof
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC
QED

Theorem LINEAR_COMPOSE_SUB :
   !(f:real['M]->real['N]) g. linear f /\ linear g ==> linear (\x. f(x) - g(x))
Proof
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC
QED

Theorem LINEAR_COMPOSE :
   !(f:real['M]->real['N]) g. linear f /\ linear g ==> linear (g o f)
Proof
  SIMP_TAC bool_ss[linear_def, o_THM]
QED

Theorem LINEAR_ID :
   linear (\x. x:real['N])
Proof
  REWRITE_TAC[linear_def] THEN BETA_TAC THEN REWRITE_TAC[]
QED

Theorem LINEAR_I :
   linear (I :real['N]->real['N])
Proof
  REWRITE_TAC[I_DEF, K_DEF, S_DEF] THEN BETA_TAC THEN BETA_TAC THEN
  REWRITE_TAC[LINEAR_ID]
QED

Theorem LINEAR_ZERO :
   linear ((\x. (vec 0)):real['M]->real['N])
Proof
  REWRITE_TAC[linear_def] THEN CONJ_TAC THEN VECTOR_ARITH_TAC
QED

Theorem LINEAR_NEGATION :
   linear ((~) :real['N]->real['N])
Proof
  REWRITE_TAC[linear_def] THEN VECTOR_ARITH_TAC
QED

Theorem LINEAR_COMPOSE_VSUM :
   !(f :'a->real['M]->real['N]) s.
         FINITE s /\ (!a. a IN s ==> linear(f a))
         ==> linear(\x. vsum s (\a. f a x))
Proof
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES,LINEAR_ZERO] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  HO_MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
  REWRITE_TAC [ETA_AX] THEN PROVE_TAC[]
QED

Theorem LINEAR_VMUL_COMPONENT :
   !(f:real['M]->real['N]) v k.
     linear f /\ k < dimindex(:'N)
     ==> linear (\x. f(x) ' k * v)
Proof
  SIMP_TAC bool_ss[linear_def, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC
QED

Theorem LINEAR_0 :
   !(f:real['M]->real['N]). linear f ==> (f((vec 0)) = (vec 0))
Proof
  PROVE_TAC[VECTOR_MUL_LZERO, linear_def]
QED

Theorem LINEAR_CMUL :
   !(f:real['M]->real['N]) c x. linear f ==> (f(c * x) = c * f(x))
Proof
  SIMP_TAC bool_ss[linear_def]
QED

Theorem LINEAR_NEG :
   !(f:real['M]->real['N]) x. linear f ==> (f(~x) = ~(f x))
Proof
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC bool_ss[LINEAR_CMUL]
QED

Theorem LINEAR_ADD :
   !(f:real['M]->real['N]) x y. linear f ==> (f(x + y) = f(x) + f(y))
Proof
  SIMP_TAC bool_ss[linear_def]
QED

Theorem LINEAR_SUB :
   !(f:real['M]->real['N]) x y. linear f ==> (f(x - y) = f(x) - f(y))
Proof
  SIMP_TAC bool_ss[VECTOR_SUB, LINEAR_ADD, LINEAR_NEG]
QED

Theorem LINEAR_VSUM :
   !(f:real['M]->real['N]) g s. linear f /\ FINITE s ==> (f(vsum s g) = vsum s (f o g))
Proof
  GEN_TAC THEN GEN_TAC THEN
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES] THEN
  FIRST_ASSUM(fn th =>
    SIMP_TAC bool_ss[MATCH_MP LINEAR_0 th, MATCH_MP LINEAR_ADD th, o_THM])
QED

Theorem LINEAR_VSUM_MUL :
   !(f:real['M]->real['N]) s c v.
        linear f /\ FINITE s
        ==> (f(vsum s (\i. c i * v i)) = vsum s (\i. c(i) * f(v i)))
Proof
  SIMP_TAC bool_ss[LINEAR_VSUM, o_DEF, LINEAR_CMUL]
QED

Theorem LINEAR_INJECTIVE_0 :
   !(f:real['M]->real['N]). linear f
       ==> ((!x y. (f(x) = f(y)) ==> (x = y)) <=>
            (!x. (f(x) = (vec 0)) ==> (x = (vec 0))))
Proof
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC bool_ss[GSYM LINEAR_SUB] THEN PROVE_TAC[VECTOR_SUB_RZERO]
QED

Theorem SYMMETRIC_LINEAR_IMAGE :
   !(f:real['M]->real['N]) s. (!x. x IN s ==> ~x IN s) /\ linear f
          ==> !x. x IN (IMAGE f s) ==> ~x IN (IMAGE f s)
Proof
  SIMP_TAC bool_ss[FORALL_IN_IMAGE, GSYM LINEAR_NEG] THEN
  PROVE_TAC[IN_IMAGE]
QED

(* ------------------------------------------------------------------------- *)
(* Bilinear functions.                                                       *)
(* ------------------------------------------------------------------------- *)

(* cf. real_topologyTheory.bilinear *)
Definition bilinear_def :
   vec_bilinear (h:real['M]->real['N]->real['P]) =
     ((!x. linear(\y. h x y)) /\ (!y. linear (\x. h x y)))
End

Overload "bilinear" = “vec_bilinear :(real['M]->real['N]->real['P])->bool”

(* Below are simple bilinear properties directly ported from HOL-Light *)
Theorem BILINEAR_SWAP :
   !(h:real['M]->real['N]->real['P]).
        bilinear(\x y. h y x) <=> bilinear h
Proof
  SIMP_TAC bool_ss[bilinear_def, ETA_AX] THEN METIS_TAC []
QED

Theorem BILINEAR_LADD :
   !(h:real['M]->real['N]->real['P]) x y z.
      bilinear h ==> h (x + y) z = (h x z) + (h y z)
Proof
  SIMP_TAC bool_ss[bilinear_def, linear_def]
QED

Theorem BILINEAR_RADD :
   !(h:real['M]->real['N]->real['P]) x y z.
      bilinear h ==> h x (y + z) = (h x y) + (h x z)
Proof
  SIMP_TAC bool_ss[bilinear_def, linear_def]
QED

Theorem BILINEAR_LMUL :
   !(h:real['M]->real['N]->real['P]) c x y.
      bilinear h ==> h (c * x) y = c * (h x y)
Proof
  SIMP_TAC bool_ss[bilinear_def, linear_def]
QED

Theorem BILINEAR_RMUL :
   !(h:real['M]->real['N]->real['P]) c x y.
      bilinear h ==> h x (c * y) = c * (h x y)
Proof
  SIMP_TAC bool_ss[bilinear_def, linear_def]
QED

Theorem BILINEAR_LNEG :
   !(h:real['M]->real['N]->real['P]) x y. bilinear h ==> h (~x) y = ~(h x y)
Proof
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC bool_ss[BILINEAR_LMUL]
QED

Theorem BILINEAR_RNEG :
   !(h:real['M]->real['N]->real['P]) x y. bilinear h ==> h x (~y) = ~(h x y)
Proof
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC bool_ss[BILINEAR_RMUL]
QED

Theorem BILINEAR_LZERO :
   !(h:real['M]->real['N]->real['P]) x. bilinear h ==> h (vec 0) x = vec 0
Proof
  ONCE_REWRITE_TAC[VECTOR_ARITH ``(x:real['M]) = vec 0 <=> x + x = x``] THEN
  SIMP_TAC bool_ss[GSYM BILINEAR_LADD, VECTOR_ADD_LID]
QED

Theorem BILINEAR_RZERO :
   !(h:real['M]->real['N]->real['P]) x. bilinear h ==> h x (vec 0) = vec 0
Proof
  ONCE_REWRITE_TAC[VECTOR_ARITH ``(x:real['M]) = vec 0 <=> x + x = x``] THEN
  SIMP_TAC bool_ss[GSYM BILINEAR_RADD, VECTOR_ADD_LID]
QED

Theorem BILINEAR_LSUB :
   !(h:real['M]->real['N]->real['P]) x y z.
      bilinear h ==> h (x - y) z = (h x z) - (h y z)
Proof
  SIMP_TAC bool_ss[VECTOR_SUB, BILINEAR_LNEG, BILINEAR_LADD]
QED

Theorem BILINEAR_RSUB :
   !(h:real['M]->real['N]->real['P]) x y z.
      bilinear h ==> h x (y - z) = (h x y) - (h x z)
Proof
  SIMP_TAC bool_ss[VECTOR_SUB, BILINEAR_RNEG, BILINEAR_RADD]
QED

(* ------------------------------------------------------------------------- *)
(* Adjoints.                                                                 *)
(* ------------------------------------------------------------------------- *)

Definition adjoint_def :
   adjoint(f:real['M]->real['N]) = @f'. !x y. (f(x) dot y) = (x dot f'(y))
End

Overload ADJOINT[local] = “adjoint”

Theorem ADJOINT_WORKS :
   !f:real['M]->real['N]. linear f ==> !x y. (f(x) dot y) = (x dot (adjoint f)(y))
Proof
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[adjoint_def] THEN CONV_TAC SELECT_CONV THEN
  SIMP_TAC bool_ss[Once SWAP_FORALL_THM, Once (GSYM SKOLEM_THM)] THEN
  GEN_TAC THEN
  Q.EXISTS_TAC `(FCP i. (f:real['M]->real['N]) (basis i) dot y):real['M]` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV) empty_rewrites[GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC bool_ss[LINEAR_VSUM, FINITE_COUNT] THEN
  REWRITE_TAC[dot_def] THEN MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'N)))
        (\i. sum (count (dimindex (:'M))) (\i'.f (x ' i' * basis i') ' i *  y ' i))` THEN
  CONJ_TAC
  >- (MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][VSUM_COMPONENT, GSYM SUM_RMUL]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'M)))
        (\i. x ' i * sum (count (dimindex (:'N))) (\i'. f (basis i) ' i' * y ' i'))` THEN
  CONJ_TAC
  >- (REWRITE_TAC[GSYM SUM_LMUL] THEN
      SIMP_TAC bool_ss[Once SUM_SWAP, FINITE_COUNT] THEN
      MATCH_MP_TAC SUM_EQ THEN SRW_TAC[][] THEN MATCH_MP_TAC SUM_EQ THEN
      SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT, LINEAR_CMUL, REAL_MUL_ASSOC]) THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]
QED

Theorem ADJOINT_LINEAR :
   !f:real['M]->real['N]. linear f ==> linear(adjoint f)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear_def, GSYM VECTOR_EQ_LDOT] THEN
  ASM_SIMP_TAC bool_ss[DOT_RMUL, DOT_RADD, GSYM ADJOINT_WORKS]
QED

Theorem ADJOINT_CLAUSES :
   !f:real['M]->real['N].
     linear f ==> (!x y. (x dot (adjoint f)(y)) = (f(x) dot y)) /\
                  (!x y. ((adjoint f)(y) dot x) = (y dot f(x)))
Proof
  PROVE_TAC[ADJOINT_WORKS, DOT_SYM]
QED

Theorem ADJOINT_ADJOINT :
   !f:real['M]->real['N]. linear f ==> (adjoint(adjoint f) = f)
Proof
  SIMP_TAC bool_ss[FUN_EQ_THM, GSYM VECTOR_EQ_LDOT, ADJOINT_CLAUSES, ADJOINT_LINEAR]
QED

Theorem ADJOINT_UNIQUE :
   !(f:real['M]->real['N]) f'. linear f /\ (!x y. (f'(x) dot y) = (x dot f(y)))
          ==> (f' = adjoint f)
Proof
  SIMP_TAC bool_ss[FUN_EQ_THM, GSYM VECTOR_EQ_RDOT, ADJOINT_CLAUSES]
QED

(* ------------------------------------------------------------------------- *)
(* A bit of linear algebra.                                                  *)
(* ------------------------------------------------------------------------- *)

(* cf. real_topologyTheory.subspace *)
Definition subspace_def :
   vector_subspace s =
       ((vec 0) IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!c x. x IN s ==> (c * x) IN s))
End

Theorem hull_def = topologyTheory.hull;

(* cf. real_topologyTheory.span *)
Definition span_def :
   vector_span s = (vector_subspace hull s)
End

(* cf. real_topologyTheory.dependent *)
Definition dependent_def :
   vector_dependent s = (?a. a IN s /\ a IN vector_span(s DELETE a))
End

(* cf. real_topologyTheory.independent *)
Definition independent_def :
   vector_independent s = ~(vector_dependent s)
End

Overload subspace    = “vector_subspace”
Overload span        = “vector_span”
Overload dependent   = “vector_dependent”
Overload independent = “vector_independent”

(* ------------------------------------------------------------------------- *)
(* Closure properties of subspaces.                                          *)
(* ------------------------------------------------------------------------- *)

Theorem SUBSPACE_UNIV :
   subspace(UNIV:real['N]->bool)
Proof
  REWRITE_TAC[subspace_def, IN_UNIV]
QED

Theorem SUBSPACE_IMP_NONEMPTY :
   !(s :real['N]->bool). subspace s ==> ~(s = {})
Proof
  REWRITE_TAC[subspace_def] THEN PROVE_TAC[NOT_IN_EMPTY]
QED

Theorem SUBSPACE_0 :
   !(s :real['N]->bool). subspace s ==> (vec 0) IN s
Proof
  SIMP_TAC bool_ss[subspace_def]
QED

Theorem SUBSPACE_ADD :
   !x y (s :real['N]->bool). subspace s /\ x IN s /\ y IN s ==> (x + y) IN s
Proof
  SIMP_TAC bool_ss[subspace_def]
QED

Theorem SUBSPACE_MUL :
   !x c (s :real['N]->bool). subspace s /\ x IN s ==> (c * x) IN s
Proof
  SIMP_TAC bool_ss[subspace_def]
QED

Theorem SUBSPACE_NEG :
   !x (s :real['N]->bool). subspace s /\ x IN s ==> (~x) IN s
Proof
  SIMP_TAC bool_ss[VECTOR_ARITH ``~x:real['N] = -(&1) * x``, SUBSPACE_MUL]
QED

Theorem SUBSPACE_SUB :
   !x y (s :real['N]->bool). subspace s /\ x IN s /\ y IN s ==> (x - y) IN s
Proof
  SIMP_TAC bool_ss[VECTOR_SUB, SUBSPACE_ADD, SUBSPACE_NEG]
QED

Theorem SUBSPACE_VSUM :
   !(s :real['N]->bool) f t. subspace s /\ FINITE t /\ (!x. x IN t ==> f(x) IN s)
           ==> (vsum t f) IN s
Proof
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, SUBSPACE_0, IN_INSERT, SUBSPACE_ADD]
QED

Theorem SUBSPACE_LINEAR_IMAGE :
   !f (s :real['N]->bool). linear f /\ subspace s ==> subspace(IMAGE f s)
Proof
  SIMP_TAC bool_ss[subspace_def, GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
  PROVE_TAC[linear_def, LINEAR_0]
QED

Theorem SUBSPACE_LINEAR_PREIMAGE :
   !f (s :real['N]->bool). linear f /\ subspace s ==> subspace {x | f(x) IN s}
Proof
  SIMP_TAC bool_ss[subspace_def, GSPEC_ETA, IN_ABS] THEN
  PROVE_TAC[linear_def, LINEAR_0]
QED

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

Theorem SPAN_SPAN :
   !(s :real['N]->bool). span(span s) = span s
Proof
  REWRITE_TAC[span_def, HULL_HULL]
QED

Theorem SPAN_MONO :
   !(s :real['N]->bool) t. s SUBSET t ==> span s SUBSET span t
Proof
  REWRITE_TAC[span_def, HULL_MONO]
QED

Theorem SUBSPACE_SPAN :
   !(s :real['N]->bool). subspace(span s)
Proof
  GEN_TAC THEN REWRITE_TAC[span_def] THEN MATCH_MP_TAC P_HULL THEN
  SIMP_TAC bool_ss[subspace_def, IN_BIGINTER]
QED

Theorem SPAN_CLAUSES :
   (!a s. a IN (s :real['N]->bool) ==> a IN span s) /\
   ((vec 0) IN span (s :real['N]->bool)) /\
   (!x y s. x IN span (s :real['N]->bool) /\ y IN span s ==> (x + y) IN span s) /\
   (!x c s. x IN span (s :real['N]->bool) ==> (c * x) IN span s)
Proof
  PROVE_TAC[span_def, HULL_SUBSET, SUBSET_DEF, SUBSPACE_SPAN, subspace_def]
QED

Theorem SPAN_INDUCT :
   !(s :real['N]->bool) h.
       (!x. x IN s ==> x IN h) /\ subspace h ==> !x. x IN span(s) ==> h(x)
Proof
  REWRITE_TAC[span_def] THEN PROVE_TAC[SUBSET_DEF, HULL_MINIMAL, IN_DEF]
QED

Theorem SPAN_EMPTY :
   span ({} :real['N]->bool) = {(vec 0)}
Proof
  REWRITE_TAC[span_def] THEN MATCH_MP_TAC HULL_UNIQUE THEN
  SIMP_TAC bool_ss[subspace_def, SUBSET_DEF, IN_SING, NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC
QED

Theorem INDEPENDENT_EMPTY :
   independent ({} :real['N]->bool)
Proof
  REWRITE_TAC[independent_def, dependent_def, NOT_IN_EMPTY]
QED

Theorem INDEPENDENT_NONZERO :
   !s. independent (s :real['N]->bool) ==> ~((vec 0) IN s)
Proof
  REWRITE_TAC[independent_def, dependent_def] THEN PROVE_TAC[SPAN_CLAUSES]
QED

(* NOTE: this proof is a bit slow *)
Theorem INDEPENDENT_MONO :
   !s t:real['N]->bool. independent t /\ s SUBSET t ==> independent s
Proof
  REWRITE_TAC[independent_def, dependent_def] THEN
  PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_DELETE]
QED

Theorem DEPENDENT_MONO :
   !s t:real['N]->bool. dependent s /\ s SUBSET t ==> dependent t
Proof
  ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> ~r /\ q ==> ~p`] THEN
  REWRITE_TAC[GSYM independent_def, INDEPENDENT_MONO]
QED

Theorem SPAN_SUBSPACE :
   !b s:real['N]->bool. b SUBSET s /\ s SUBSET (span b) /\ subspace s ==> (span b = s)
Proof
  PROVE_TAC[SUBSET_ANTISYM, span_def, HULL_MINIMAL]
QED

Theorem SPAN_INDUCT_ALT :
   !(s :real['N]->bool) h. h((vec 0)) /\
         (!c x y. x IN s /\ h(y) ==> h(c * x + y))
          ==> !x:real['N]. x IN span(s) ==> h(x)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o prove_nonschematic_inductive_relations_exist bool_monoset o concl) THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `g` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN “!x:real['N]. x IN span(s) ==> g(x)”
   (fn th => PROVE_TAC[th]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace_def,SPECIFICATION] THEN
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC bool_ss[Once SWAP_FORALL_THM, RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM HO_MATCH_MP_TAC) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
  PROVE_TAC[IN_DEF, VECTOR_ADD_LID, VECTOR_ADD_ASSOC, VECTOR_ADD_SYM,
                VECTOR_MUL_LID, VECTOR_MUL_RZERO]
QED

(* ------------------------------------------------------------------------- *)
(* Individual closure properties.                                            *)
(* ------------------------------------------------------------------------- *)

Theorem SPAN_SUPERSET :
   !x. x IN (s :real['N]->bool) ==> x IN span s
Proof
  PROVE_TAC[SPAN_CLAUSES]
QED

Theorem SPAN_INC :
   !s. s SUBSET span (s :real['N]->bool)
Proof
  REWRITE_TAC[SUBSET_DEF, SPAN_SUPERSET]
QED

Theorem SPAN_UNION_SUBSET :
   !(s :real['N]->bool) t. span s UNION span t SUBSET span(s UNION t)
Proof
  REWRITE_TAC[span_def, HULL_UNION_SUBSET]
QED

Theorem SPAN_UNIV :
   span(UNIV:real['N]->bool) = (UNIV:real['N]->bool)
Proof
  SIMP_TAC bool_ss[SPAN_INC, (prove(“UNIV SUBSET s ==> (s = UNIV)”, PROVE_TAC[UNIV_SUBSET]))]
QED

Theorem SPAN_0 :
   (vec 0) IN span (s :real['N]->bool)
Proof
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_0]
QED

Theorem SPAN_ADD :
   !x y (s :real['N]->bool). x IN span s /\ y IN span s ==> (x + y) IN span s
Proof
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_ADD]
QED

Theorem SPAN_MUL :
   !x c s. x IN span s ==> (c * x) IN span (s :real['N]->bool)
Proof
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_MUL]
QED

Theorem SPAN_MUL_EQ :
   !x:real['N] c s. ~(c = &0) ==> ((c * x) IN span s <=> x IN span s)
Proof
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC bool_ss[SPAN_MUL] THEN
  Q.SUBGOAL_THEN `(inv(c) * c * x:real['N]) IN span s` MP_TAC THENL
   [ASM_SIMP_TAC bool_ss[GSYM VECTOR_MUL_ASSOC, SPAN_MUL],
    ASM_SIMP_TAC bool_ss[REAL_MUL_LINV, VECTOR_MUL_LID]]
QED

Theorem SPAN_NEG :
   !x s. x IN span s ==> (~x) IN span (s :real['N]->bool)
Proof
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_NEG]
QED

Theorem SPAN_NEG_EQ :
   !x s. ~x IN span s <=> x IN span (s :real['N]->bool)
Proof
  PROVE_TAC[SPAN_NEG, VECTOR_NEG_NEG]
QED

Theorem SPAN_SUB :
   !x y s. x IN span s /\ y IN span s ==> (x - y) IN span (s :real['N]->bool)
Proof
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_SUB]
QED

Theorem SPAN_VSUM :
   !s f t. FINITE t /\ (!x. x IN t ==> f(x) IN span(s))
           ==> (vsum t f) IN span (s :real['N]->bool)
Proof
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_VSUM]
QED

Theorem SPAN_ADD_EQ :
   !(s :real['N]->bool) x y. x IN span s ==> ((x + y) IN span s <=> y IN span s)
Proof
  PROVE_TAC[SPAN_ADD, SPAN_SUB, VECTOR_ARITH ``(x + y) - x:real['N] = y``]
QED

Theorem SPAN_EQ_SELF :
   !s. (span s = s) <=> subspace (s :real['N]->bool)
Proof
  GEN_TAC THEN EQ_TAC THENL [PROVE_TAC[SUBSPACE_SPAN], ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
  ASM_REWRITE_TAC[SUBSET_REFL, SPAN_INC]
QED

Theorem SPAN_SUBSET_SUBSPACE :
   !s t:real['N]->bool. s SUBSET t /\ subspace t ==> span s SUBSET t
Proof
  PROVE_TAC[SPAN_MONO, SPAN_EQ_SELF]
QED

Theorem SUBSPACE_TRANSLATION_SELF :
   !(s :real['N]->bool) a. subspace s /\ a IN s ==> (IMAGE (\x. a + x) s = s)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_SURJ, SURJ_DEF] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I empty_rewrites [GSYM SPAN_EQ_SELF]) THEN
  ASM_SIMP_TAC bool_ss[SPAN_ADD_EQ, SPAN_CLAUSES] THEN
  PROVE_TAC[VECTOR_ARITH ``(a + x:real['N] = y) <=> (x = y - a)``,
            SPAN_SUPERSET,SPAN_SUB, EXISTS_REFL]
QED

Theorem SUBSPACE_TRANSLATION_SELF_EQ :
   !s a:real['N]. subspace s ==> ((IMAGE (\x. a + x) s = s) <=> a IN s)
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC bool_ss[SUBSPACE_TRANSLATION_SELF] THEN
  DISCH_THEN(MP_TAC o AP_TERM ``\s. (a:real['N]) IN s``) THEN
  BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN Q.EXISTS_TAC `(vec 0):real['N]` THEN
  PROVE_TAC[subspace_def, VECTOR_ADD_RID]
QED

Theorem SUBSPACE_SUMS :
   !s t. subspace s /\ subspace t
         ==> subspace {x + y | x IN s /\ y IN t}
Proof
  SIMP_TAC bool_ss[subspace_def, GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REPEAT STRIP_TAC THENL
   [PROVE_TAC[VECTOR_ADD_LID],
    ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[VECTOR_ARITH
     ``(x + y) + (x' + y'):real['N] = (x + x') + (y + y')``] THEN
    PROVE_TAC[],
    ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN PROVE_TAC[]]
QED

Theorem SPAN_UNION :
   !s t. span(s UNION t) = {x + y:real['N] | x IN span s /\ y IN span t}
Proof
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    SIMP_TAC bool_ss[SUBSPACE_SUMS, SUBSPACE_SPAN] THEN
    REWRITE_TAC[SUBSET_DEF, IN_UNION] THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
        Q.X_GEN_TAC `x:real['N]` THEN STRIP_TAC THENL
     [MAP_EVERY Q.EXISTS_TAC [`x:real['N]`, `(vec 0):real['N]`] THEN
      ASM_SIMP_TAC bool_ss[SPAN_SUPERSET, SPAN_0, VECTOR_ADD_RID],
      MAP_EVERY Q.EXISTS_TAC [`(vec 0):real['N]`, `x:real['N]`] THEN
      ASM_SIMP_TAC bool_ss[SPAN_SUPERSET, SPAN_0, VECTOR_ADD_LID]],
    REWRITE_TAC[SUBSET_DEF] THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
        Q.X_GEN_TAC `x:real['N]` THEN SIMP_TAC bool_ss [GSYM LEFT_FORALL_IMP_THM] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_ADD THEN
    PROVE_TAC[SPAN_MONO, SUBSET_UNION, SUBSET_DEF]]
QED

(* ------------------------------------------------------------------------- *)
(* Mapping under linear image.                                               *)
(* ------------------------------------------------------------------------- *)

Theorem SPAN_LINEAR_IMAGE :
   !f:real['M]->real['N] s. linear f ==> (span(IMAGE f s) = IMAGE f (span s))
Proof
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I empty_rewrites[EXTENSION] THEN
  Q.X_GEN_TAC `x:real['N]` THEN
  EQ_TAC THEN Q.SPEC_TAC(`x:real['N]`,`x:real['N]`) THENL
   [ALL_TAC, SIMP_TAC bool_ss[FORALL_IN_IMAGE]] THEN
  HO_MATCH_MP_TAC SPAN_INDUCT THEN
   REWRITE_TAC[Q.prove(`(\x. x IN s) = s`, SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS]),
     Q.prove(`(\x. f x IN span(s)) = {x | f(x) IN span s}`,
             SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS])] THEN
    ASM_SIMP_TAC bool_ss[SUBSPACE_SPAN, SUBSPACE_LINEAR_IMAGE, SUBSPACE_LINEAR_PREIMAGE] THEN
    SIMP_TAC bool_ss[FORALL_IN_IMAGE, GSPEC_ETA, IN_ABS] THEN
    PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF, IN_IMAGE]
QED

(* ------------------------------------------------------------------------- *)
(* The key breakdown property.                                               *)
(* ------------------------------------------------------------------------- *)

Theorem SPAN_BREAKDOWN :
   !b s a:real['N].
      b IN s /\ a IN span s ==> ?k. (a - k * b) IN span(s DELETE b)
Proof
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN HO_MATCH_MP_TAC SPAN_INDUCT THEN
  SIMP_TAC bool_ss[subspace_def, IN_ABS] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN Q.ASM_CASES_TAC `a:real['N] = b`, ALL_TAC] THEN
  PROVE_TAC[SPAN_CLAUSES, IN_DELETE, VECTOR_ARITH
   ``(a - &1 * a = (vec 0)) /\ (a - &0 * b = a) /\
    ((x + y) - (k1 + k2) * b = (x - k1 * b) + (y - k2 * b)) /\
    (c * x - (c * k) * y = c * (x - k * y))``]
QED

Theorem SPAN_BREAKDOWN_EQ :
   !a:real['N] s. (x IN span(a INSERT s) <=> (?k. (x - k * a) IN span s))
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJ(Q.prove(`(a:real['N]) IN (a INSERT s)`, REWRITE_TAC[IN_INSERT]))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_BREAKDOWN) THEN
    HO_MATCH_MP_TAC MONO_EXISTS THEN Q.X_GEN_TAC `k:real` THEN
    Q.SPEC_TAC(`x - k * a:real['N]`,`y:real['N]`) THEN
    REWRITE_TAC[GSYM SUBSET_DEF] THEN MATCH_MP_TAC SPAN_MONO THEN
        REWRITE_TAC[DELETE_INSERT, DELETE_SUBSET],
    DISCH_THEN(Q.X_CHOOSE_TAC `k:real`) THEN
    SUBST1_TAC(VECTOR_ARITH ``x = (x - k * a) + k * a:real['N]``) THEN
    MATCH_MP_TAC SPAN_ADD THEN
    PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_INSERT, SPAN_CLAUSES]]
QED

Theorem SPAN_INSERT_0 :
   !s. span((vec 0) INSERT s) = span (s :real['N]->bool)
Proof
  SIMP_TAC bool_ss[EXTENSION, SPAN_BREAKDOWN_EQ, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO]
QED

Theorem SPAN_SING :
   !(a :real['N]). span {a} = {u * a | u IN (UNIV:real set)}
Proof
  REWRITE_TAC[EXTENSION, SPAN_BREAKDOWN_EQ, SPAN_EMPTY] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC[IN_UNIV, IN_SING, VECTOR_SUB_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* Hence some "reversal" results.                                            *)
(* ------------------------------------------------------------------------- *)

Theorem IN_SPAN_INSERT :
   !a b:real['N] s.
        a IN span(b INSERT s) /\ ~(a IN span s) ==> b IN span(a INSERT s)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [“b:real['N]”, “(b:real['N]) INSERT s”, “a:real['N]”]
    SPAN_BREAKDOWN) THEN ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `k:real` MP_TAC) THEN Q.ASM_CASES_TAC `k = &0` THEN
  ASM_REWRITE_TAC[VECTOR_ARITH ``a - &0 * b:real['N] = a``, DELETE_INSERT] THENL
   [PROVE_TAC[SPAN_MONO, SUBSET_DEF, DELETE_SUBSET], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o Q.SPEC `inv(k)` o MATCH_MP SPAN_MUL) THEN
  ASM_SIMP_TAC bool_ss[VECTOR_SUB_LDISTRIB, VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN
  DISCH_TAC THEN SUBST1_TAC(VECTOR_ARITH
   ``b:real['N] = inv(k) * a - (inv(k) * a - &1 * b)``) THEN
  MATCH_MP_TAC SPAN_SUB THEN
  PROVE_TAC[SPAN_CLAUSES, IN_INSERT, SUBSET_DEF, IN_DELETE, SPAN_MONO]
QED

Theorem IN_SPAN_DELETE :
   !a b (s :real['N]->bool).
         a IN span s /\ ~(a IN span (s DELETE b))
         ==> b IN span (a INSERT (s DELETE b))
Proof
  PROVE_TAC[IN_SPAN_INSERT, SPAN_MONO, SUBSET_DEF, IN_INSERT, IN_DELETE]
QED

Theorem EQ_SPAN_INSERT_EQ :
   !s x y:real['N]. (x - y) IN span s ==> (span(x INSERT s) = span(y INSERT s))
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[SPAN_BREAKDOWN_EQ, EXTENSION] THEN
  PROVE_TAC[SPAN_ADD, SPAN_SUB, SPAN_MUL,
            VECTOR_ARITH ``(z - k * y:real['N]) - k * (x - y) = z - k * x``,
            VECTOR_ARITH ``(z - k * x:real['N]) + k * (x - y) = z - k * y``]
QED

(* ------------------------------------------------------------------------- *)
(* Transitivity property.                                                    *)
(* ------------------------------------------------------------------------- *)

Theorem SPAN_TRANS :
   !x y:real['N] s. x IN span(s) /\ y IN span(x INSERT s) ==> y IN span(s)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.SPECL [`x:real['N]`, `(x:real['N]) INSERT s`, `y:real['N]`]
         SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBST1_TAC(VECTOR_ARITH ``y:real['N] = (y - k * x) + k * x``) THEN
  MATCH_MP_TAC SPAN_ADD THEN ASM_SIMP_TAC bool_ss[SPAN_MUL] THEN
  PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_INSERT, IN_DELETE]
QED

(* ------------------------------------------------------------------------- *)
(* An explicit expansion is sometimes needed.                                *)
(* ------------------------------------------------------------------------- *)

Theorem SPAN_EXPLICIT :
   !(p:real['N] -> bool).
        span p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    (vsum s (\v. u v * v) = y)}
Proof
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  SIMP_TAC bool_ss[SUBSET_DEF, GSPEC_ETA, IN_ABS] THENL
   [ALL_TAC,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SPAN_VSUM THEN ASM_SIMP_TAC bool_ss[BETA_THM] THEN
    PROVE_TAC[SPAN_SUPERSET, SPAN_MUL]] THEN
  HO_MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
   [Q.EXISTS_TAC `{}:real['N]->bool` THEN
    rw [VSUM_CLAUSES, EMPTY_SUBSET, NOT_IN_EMPTY],
    ALL_TAC] THEN
  MAP_EVERY Q.X_GEN_TAC [`c:real`, `x:real['N]`, `y:real['N]`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY Q.X_GEN_TAC [`s:real['N]->bool`, `u:real['N]->real`] THEN
  STRIP_TAC THEN Q.EXISTS_TAC `(x:real['N]) INSERT s` THEN
  Q.EXISTS_TAC `\y. if y = x then (if x IN s then (u:real['N]->real) y + c else c)
                    else u y` THEN
  ASM_SIMP_TAC bool_ss[FINITE_INSERT, IN_INSERT, VSUM_CLAUSES] THEN
  CONJ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (Q.prove(
     `x IN s ==> (s = x INSERT (s DELETE x))`, SIMP_TAC bool_ss[INSERT_DELETE]))) THEN
    ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_INSERT, FINITE_DELETE, IN_DELETE] THEN
    MATCH_MP_TAC(VECTOR_ARITH
      ``(y:real['N] = z) ==> ((c + d) * x + y = d * x + (c * x + z))``),
    AP_TERM_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN BETA_TAC THEN PROVE_TAC[IN_DELETE]
QED

Theorem DEPENDENT_EXPLICIT :
   !p. dependent (p:real['N]-> bool) <=>
                ?s u. FINITE s /\ s SUBSET p /\
                      (?v. v IN s /\ ~(u v = &0)) /\
                      (vsum s (\v. u v * v) = (vec 0))
Proof
  GEN_TAC THEN SIMP_TAC bool_ss[dependent_def, SPAN_EXPLICIT, GSPEC_ETA, IN_ABS] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
  EQ_TAC THEN SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THENL
   [MAP_EVERY Q.X_GEN_TAC [`s:real['N]->bool`,`u:real['N]->real`] THEN
    STRIP_TAC THEN MAP_EVERY Q.EXISTS_TAC
     [`vsum s (\v. u v * v) INSERT s`,
      `\y. if y = vsum s (\v. u v * v) then - &1 else (u:real['N]->real) y`,
      `vsum s (\v. u v * v)`] THEN
    ASM_REWRITE_TAC[IN_INSERT, INSERT_SUBSET, FINITE_INSERT] THEN
    CONJ_TAC THENL [PROVE_TAC[SUBSET_DELETE], ALL_TAC] THEN
    ASM_SIMP_TAC bool_ss[VSUM_CLAUSES] THEN REWRITE_TAC[REAL_10, REAL_NEG_EQ0] THEN
    COND_CASES_TAC THENL [PROVE_TAC[SUBSET_DEF, IN_DELETE], ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH ``(- &1 * a + s = (vec 0)) <=> (a = s)``] THEN
    MATCH_MP_TAC VSUM_EQ THEN BETA_TAC THEN PROVE_TAC[],
    MAP_EVERY Q.X_GEN_TAC [`s:real['N]->bool`, `u:real['N]->real`, `a:real['N]`] THEN
    STRIP_TAC THEN MAP_EVERY Q.EXISTS_TAC
     [`s DELETE (a:real['N])`,
      `\i. -((u:real['N]->real) i) / (u a)`] THEN
    ASM_SIMP_TAC bool_ss[VSUM_DELETE, FINITE_DELETE] THEN
    Q.SUBGOAL_THEN `vsum s (\v. -u v / u a * v) - -u a / u a * a = a` SUBST1_TAC THENL[
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC bool_ss[VECTOR_MUL_LNEG, GSYM VECTOR_MUL_ASSOC, VSUM_LMUL, VSUM_NEG,
                                                 VECTOR_MUL_RNEG, VECTOR_MUL_RZERO] THEN
      ASM_SIMP_TAC bool_ss[VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN VECTOR_ARITH_TAC,
          PROVE_TAC[SUBSET_DEF, SUBSET_DELETE_BOTH]]]
QED

Theorem DEPENDENT_FINITE :
   !s:real['N]->bool.
        FINITE s
        ==> (dependent s <=> ?u. (?v. v IN s /\ ~(u v = &0)) /\
                                 (vsum s (\v. u(v) * v) = (vec 0)))
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[DEPENDENT_EXPLICIT] THEN EQ_TAC THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THENL
   [MAP_EVERY Q.X_GEN_TAC [`t:real['N]->bool`, `u:real['N]->real`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    Q.EXISTS_TAC `\v:real['N]. if v IN t then u(v) else &0` THEN
    BETA_TAC THEN CONJ_TAC THENL [PROVE_TAC[SUBSET_DEF], ALL_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC bool_ss[VECTOR_MUL_LZERO, GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC bool_ss[Q.prove(`t SUBSET s ==> ({x | x IN s /\ x IN t} = t)`,
                                                 REWRITE_TAC[GSYM IN_INTER, GSPEC_ID] THEN
                                                 PROVE_TAC[SUBSET_INTER_ABSORPTION, INTER_COMM])],
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    MAP_EVERY Q.EXISTS_TAC [`s:real['N]->bool`, `u:real['N]->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]
QED

Theorem SPAN_FINITE :
   !s:real['N]->bool.
        FINITE s ==> (span s = {y | ?u. vsum s (\v. u v * v) = y})
Proof
  REPEAT STRIP_TAC THEN SIMP_TAC bool_ss[SPAN_EXPLICIT, EXTENSION, GSPEC_ETA, IN_ABS] THEN
  Q.X_GEN_TAC `y:real['N]` THEN EQ_TAC THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THENL
   [MAP_EVERY Q.X_GEN_TAC [`t:real['N]->bool`, `u:real['N]->real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    Q.EXISTS_TAC `\x:real['N]. if x IN t then u(x) else &0` THEN
    SIMP_TAC bool_ss[COND_RAND, COND_RATOR, VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC bool_ss[GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC bool_ss[Q.prove(`t SUBSET s ==> ({x | x IN s /\ x IN t} = t)`,
                                                 REWRITE_TAC[GSYM IN_INTER, GSPEC_ID] THEN
                                                 PROVE_TAC[SUBSET_INTER_ABSORPTION, INTER_COMM])],
    Q.X_GEN_TAC `u:real['N]->real` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY Q.EXISTS_TAC [`s:real['N]->bool`, `u:real['N]->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]
QED

(* ------------------------------------------------------------------------- *)
(* Standard bases are a spanning set, and obviously finite.                  *)
(* ------------------------------------------------------------------------- *)

Theorem SPAN_STDBASIS :
   span {basis i :real['N] | i < dimindex(:'N)} = UNIV
Proof
  REWRITE_TAC[EXTENSION, IN_UNIV] THEN Q.X_GEN_TAC `x:real['N]` THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites[GSYM BASIS_EXPANSION] THEN
  MATCH_MP_TAC SPAN_VSUM THEN SIMP_TAC bool_ss[FINITE_COUNT, IN_COUNT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[]
QED

Theorem HAS_SIZE_def[local] = HAS_SIZE

Theorem HAS_SIZE_STDBASIS :
   {basis i :real['N] | i < dimindex(:'N)} HAS_SIZE dimindex(:'N)
Proof
  SIMP_TAC bool_ss[Once (Q.prove(`{f x | P x} = IMAGE f {x | P x}`,
                                   REWRITE_TAC[EXTENSION] THEN
                                   CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
                                   SIMP_TAC bool_ss[IN_IMAGE, GSPEC_ETA, IN_ABS, IN_DEF]))] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  REWRITE_TAC[HAS_SIZE_def, GSYM count_def, FINITE_COUNT, CARD_COUNT, IN_COUNT] THEN
  PROVE_TAC[BASIS_INJ]
QED

Theorem FINITE_STDBASIS :
   FINITE {basis i :real['N] |i < dimindex(:'N)}
Proof
  PROVE_TAC[HAS_SIZE_STDBASIS, HAS_SIZE_def]
QED

Theorem CARD_STDBASIS :
   CARD {basis i :real['N] |i < dimindex(:'N)} = dimindex(:'N)
Proof
   PROVE_TAC[HAS_SIZE_STDBASIS, HAS_SIZE_def]
QED

Theorem IN_SPAN_IMAGE_BASIS :
   !x:real['N] s.
        x IN span(IMAGE basis s) <=>
          !i. i < dimindex(:'N) /\ ~(i IN s) ==>(x ' i = &0)
Proof
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [Q.SPEC_TAC(`x:real['N]`,`x:real['N]`) THEN HO_MATCH_MP_TAC SPAN_INDUCT THEN
    SIMP_TAC bool_ss[subspace_def, IN_ABS, VEC_COMPONENT, VECTOR_ADD_COMPONENT,
             VECTOR_MUL_COMPONENT, REAL_MUL_RZERO, REAL_ADD_RID] THEN
    SIMP_TAC bool_ss[FORALL_IN_IMAGE, BASIS_COMPONENT] THEN PROVE_TAC[],
    DISCH_TAC THEN SIMP_TAC bool_ss[SPAN_EXPLICIT, GSPEC_ETA, IN_ABS] THEN
    Q.EXISTS_TAC `(IMAGE basis (count(dimindex(:'N)) INTER s)):real['N]->bool` THEN
    SIMP_TAC bool_ss[IMAGE_FINITE, FINITE_INTER, FINITE_COUNT] THEN
    SIMP_TAC bool_ss[RIGHT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET], ALL_TAC] THEN
    Q.EXISTS_TAC `\v:real['N]. x dot v` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
    REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
     [SIMP_TAC bool_ss[IMAGE_FINITE, FINITE_INTER, FINITE_COUNT] THEN
      REWRITE_TAC[IN_INTER, IN_COUNT] THEN PROVE_TAC[BASIS_INJ],
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_DEF] THEN
    SIMP_TAC bool_ss[CART_EQ, VSUM_COMPONENT, VECTOR_MUL_COMPONENT,
             BASIS_COMPONENT] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[Q.prove(
     `(if x = y then p else q) = (if y = x then p else q)`, PROVE_TAC[])] THEN
    SIMP_TAC bool_ss[SUM_DELTA, REAL_MUL_RZERO, IN_INTER, IN_COUNT, DOT_BASIS] THEN
    PROVE_TAC[REAL_MUL_RID]]
QED

(* ------------------------------------------------------------------------- *)
(* This is useful for building a basis step-by-step.                         *)
(* ------------------------------------------------------------------------- *)

Theorem INDEPENDENT_STDBASIS :
   independent {basis i :real['N] | i < dimindex(:'N)}
Proof
  SIMP_TAC std_ss[
        Once (Q.prove(`{f x | P x} = IMAGE f {x | P x}`,
          REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
      CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  REWRITE_TAC[independent_def, dependent_def] THEN
  SIMP_TAC pure_ss[EXISTS_IN_IMAGE] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  Q.SUBGOAL_THEN
   `IMAGE basis {i | i < dimindex(:'N)} DELETE
           (basis k:real['N]) =
    IMAGE basis ({i | i < dimindex(:'N)} DELETE k)`
  SUBST1_TAC THENL
   [SIMP_TAC bool_ss[EXTENSION, IN_IMAGE, IN_DELETE, GSPEC_ETA, IN_ABS] THEN
    GEN_TAC THEN EQ_TAC THEN PROVE_TAC[BASIS_INJ],
    ALL_TAC] THEN
  REWRITE_TAC[IN_SPAN_IMAGE_BASIS] THEN DISCH_THEN(MP_TAC o SPEC ``k:num``) THEN
  ASM_SIMP_TAC bool_ss[IN_DELETE, BASIS_COMPONENT, REAL_OF_NUM_EQ] THEN ARITH_TAC
QED

Theorem INDEPENDENT_INSERT :
   !a:real['N] s. independent(a INSERT s) <=>
                  if a IN s then independent s
                  else independent s /\ ~(a IN span s)
Proof
  REPEAT GEN_TAC THEN Q.ASM_CASES_TAC `(a:real['N]) IN s` THEN
  ASM_SIMP_TAC bool_ss[Q.prove(`x IN s ==> (x INSERT s = s)`,
        SIMP_TAC bool_ss[INSERT_DEF, EXTENSION, GSPEC_ETA, IN_ABS] THEN PROVE_TAC[])] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [PROVE_TAC[INDEPENDENT_MONO, SUBSET_DEF, IN_INSERT],
      POP_ASSUM MP_TAC THEN REWRITE_TAC[independent_def, dependent_def] THEN
      PROVE_TAC[IN_INSERT, DELETE_INSERT, DELETE_NON_ELEMENT]],
    ALL_TAC] THEN
  SIMP_TAC bool_ss[independent_def, dependent_def] THEN
  STRIP_TAC THEN Q.X_GEN_TAC `b:real['N]` THEN
  REWRITE_TAC[IN_INSERT] THEN Q.ASM_CASES_TAC `b:real['N] = a` THENL[
        ASM_SIMP_TAC bool_ss[DELETE_INSERT] THEN PROVE_TAC[DELETE_NON_ELEMENT],
  ASM_SIMP_TAC bool_ss[DELETE_INSERT] THEN
  PROVE_TAC[IN_SPAN_INSERT, INSERT_DELETE]]
QED

(* ------------------------------------------------------------------------- *)
(* The degenerate case of the Exchange Lemma.                                *)
(* ------------------------------------------------------------------------- *)

Theorem SPANNING_SUBSET_INDEPENDENT :
   !s t:real['N]->bool.
        t SUBSET s /\ independent s /\ s SUBSET span(t) ==> (s = t)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_DEF] THEN
  Q.X_GEN_TAC `a:real['N]` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites [independent_def]) THEN
  SIMP_TAC bool_ss[dependent_def] THEN
  DISCH_THEN(MP_TAC o SPEC ``a:real['N]``) THEN ASM_REWRITE_TAC[] THEN
  PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_DELETE]
QED

(* ------------------------------------------------------------------------- *)
(* The general case of the Exchange Lemma, the key to what follows.          *)
(* ------------------------------------------------------------------------- *)

Theorem EXCHANGE_LEMMA :
   !s t:real['N]->bool.
        FINITE t /\ independent s /\ s SUBSET span t
        ==> ?t'. (t' HAS_SIZE (CARD t)) /\
                 s SUBSET t' /\ t' SUBSET (s UNION t) /\ s SUBSET (span t')
Proof
  Induct_on `CARD(t DIFF s :real['N]->bool)` THEN
  REPEAT GEN_TAC THEN
  Q.ASM_CASES_TAC `(s:real['N]->bool) SUBSET t` THENL
   [PROVE_TAC[HAS_SIZE_def, SUBSET_UNION], ALL_TAC,
    PROVE_TAC[HAS_SIZE_def, SUBSET_UNION], ALL_TAC] THEN
  Q.ASM_CASES_TAC `t SUBSET (s:real['N]->bool)` THENL
   [PROVE_TAC[SPANNING_SUBSET_INDEPENDENT, HAS_SIZE_def], ALL_TAC,
    PROVE_TAC[SPANNING_SUBSET_INDEPENDENT, HAS_SIZE_def], ALL_TAC] THEN
  STRIP_TAC THEN
  Q.PAT_ASSUM `$~ X` (MP_TAC o REWRITE_RULE[SUBSET_DEF]) THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `b:real['N]` STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_X_ASSUM `$= X Y` (MP_TAC o SYM) THENL
  [ASM_SIMP_TAC bool_ss[FINITE_DIFF, CARD_EQ_0] THEN
   PROVE_TAC[IN_DIFF, MEMBER_NOT_EMPTY], ALL_TAC] THEN
  STRIP_TAC THEN
  Q.ASM_CASES_TAC `s SUBSET span(t DELETE (b:real['N]))` THENL
  [ FIRST_X_ASSUM(MP_TAC o
                Q.SPECL [`t DELETE (b:real['N])`, `s:real['N]->bool`]) THEN
    ASM_REWRITE_TAC[Q.prove(`s DELETE a DIFF t = (s DIFF t) DELETE a`,
                SIMP_TAC bool_ss[DELETE_DEF, DIFF_DEF, EXTENSION, GSPEC_ETA, IN_ABS]
                THEN PROVE_TAC[])] THEN
    ASM_SIMP_TAC bool_ss[CARD_DELETE, FINITE_DIFF, IN_DIFF, FINITE_DELETE] THEN
    ASM_REWRITE_TAC[SUC_SUB1] THEN
        DISCH_THEN(Q.X_CHOOSE_THEN `u:real['N]->bool` STRIP_ASSUME_TAC) THEN
    Q.EXISTS_TAC `(b:real['N]) INSERT u` THEN
    ASM_SIMP_TAC bool_ss[SUBSET_INSERT, INSERT_SUBSET, IN_UNION] THEN CONJ_TAC THENL
     [Q.UNDISCH_TAC `(u:real['N]->bool) HAS_SIZE CARD(t:real['N]->bool) - 1` THEN
      SIMP_TAC bool_ss[HAS_SIZE_def, FINITE_RULES, CARD_CLAUSES] THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [PROVE_TAC[SUBSET_DEF, IN_UNION, IN_DELETE], ALL_TAC] THEN
      PROVE_TAC[Q.prove(`~(n = 0) ==> (SUC(n - 1) = n)`, ARITH_TAC),
                    CARD_EQ_0, MEMBER_NOT_EMPTY],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [Q.UNDISCH_TAC `u SUBSET s UNION (t DELETE (b:real['N]))` THEN
            PROVE_TAC[SUBSET_DEF, IN_UNION, IN_DELETE],
      PROVE_TAC[SUBSET_DEF, SPAN_MONO, IN_INSERT]],
    ALL_TAC] THEN
  Q.UNDISCH_TAC `~(s SUBSET span (t DELETE (b:real['N])))` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[SUBSET_DEF] THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `a:real['N]` STRIP_ASSUME_TAC) THEN
  Q.SUBGOAL_THEN `~(a:real['N] = b)` ASSUME_TAC THENL
    [PROVE_TAC[], ALL_TAC] THEN
  Q.SUBGOAL_THEN `~((a:real['N]) IN t)` ASSUME_TAC THENL
   [PROVE_TAC[IN_DELETE, SPAN_CLAUSES], ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o Q.SPECL
   [`(a:real['N]) INSERT (t DELETE b)`, `s:real['N]->bool`]) THEN
  ASM_SIMP_TAC bool_ss[Q.prove(
     `a IN s ==> (((a INSERT (t DELETE b)) DIFF s) = (t DIFF s) DELETE b)`,
          SIMP_TAC bool_ss[DELETE_DEF, DIFF_DEF, EXTENSION, GSPEC_ETA, IN_ABS,
                            IN_INSERT] THEN PROVE_TAC[])] THEN
    ASM_SIMP_TAC bool_ss[CARD_DELETE, FINITE_DELETE, FINITE_DIFF, IN_DIFF] THEN
    ASM_SIMP_TAC bool_ss[SUC_SUB1, FINITE_INSERT, FINITE_DELETE] THEN
  Q.SUBGOAL_THEN `s SUBSET span (a:real['N] INSERT t DELETE b)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_DEF] THEN Q.X_GEN_TAC `x:real['N]` THEN
    DISCH_TAC THEN MATCH_MP_TAC SPAN_TRANS THEN Q.EXISTS_TAC `b:real['N]` THEN
    PROVE_TAC[IN_SPAN_DELETE, SUBSET_DEF, SPAN_MONO,
              Q.prove(`t SUBSET (b INSERT (a INSERT (t DELETE b)))`,
                      REWRITE_TAC[SUBSET_INSERT_DELETE, DELETE_SUBSET])],
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN Q.X_GEN_TAC `u:real['N]->bool` THEN
  ASM_SIMP_TAC bool_ss[HAS_SIZE_def, CARD_CLAUSES, CARD_DELETE, FINITE_DELETE, IN_DELETE,
               Q.prove(`(SUC(n - 1) = n) <=> ~(n = 0)`, ARITH_TAC), CARD_EQ_0] THEN
  ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[INSERT_UNION] THEN
  PROVE_TAC[NOT_IN_EMPTY, UNION_SUBSET, DELETE_SUBSET, SUBSET_TRANS, SUBSET_UNION]
QED

(* ------------------------------------------------------------------------- *)
(* This implies corresponding size bounds.                                   *)
(* ------------------------------------------------------------------------- *)

Theorem INDEPENDENT_SPAN_BOUND :
   !(s :real['N]->bool) t. FINITE t /\ independent s /\ s SUBSET span(t)
         ==> FINITE s /\ CARD(s) <= CARD(t)
Proof
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EXCHANGE_LEMMA) THEN
  PROVE_TAC[HAS_SIZE_def, CARD_SUBSET, SUBSET_FINITE]
QED

Theorem INDEPENDENT_BOUND :
   !s:real['N]->bool.
        independent s ==> FINITE s /\ CARD(s) <= dimindex(:'N)
Proof
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM CARD_STDBASIS] THEN
  MATCH_MP_TAC INDEPENDENT_SPAN_BOUND THEN
  ASM_REWRITE_TAC[FINITE_STDBASIS, SPAN_STDBASIS, SUBSET_UNIV]
QED

Theorem DEPENDENT_BIGGERSET :
   !s:real['N]->bool. (FINITE s ==> CARD(s) > dimindex(:'N)) ==> dependent s
Proof
  MP_TAC INDEPENDENT_BOUND THEN HO_MATCH_MP_TAC MONO_ALL THEN
  PROVE_TAC[GREATER_DEF, NOT_LESS, independent_def]
QED

Theorem INDEPENDENT_IMP_FINITE :
   !s:real['N]->bool. independent s ==> FINITE s
Proof
  SIMP_TAC bool_ss[INDEPENDENT_BOUND]
QED

(* ------------------------------------------------------------------------- *)
(* Explicit formulation of independence.                                     *)
(* ------------------------------------------------------------------------- *)

Theorem INDEPENDENT_EXPLICIT :
   !b:real['N]->bool.
        independent b <=>
            FINITE b /\
            !c. (vsum b (\v. c(v) * v) = (vec 0)) ==> !v. v IN b ==> (c(v) = &0)
Proof
  GEN_TAC THEN
  Q.ASM_CASES_TAC `FINITE(b:real['N]->bool)` THENL
   [ALL_TAC, PROVE_TAC[INDEPENDENT_BOUND]] THEN
  ASM_SIMP_TAC bool_ss' [independent_def, DEPENDENT_FINITE, IMP_DISJ_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [DISJ_COMM] THEN
  EQ_TAC THEN PROVE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* Hence we can create a maximal independent subset.                         *)
(* ------------------------------------------------------------------------- *)

Theorem MAXIMAL_INDEPENDENT_SUBSET_EXTEND :
   !s v:real['N]->bool.
        s SUBSET v /\ independent s
        ==> ?b. s SUBSET b /\ b SUBSET v /\ independent b /\
                v SUBSET (span b)
Proof
  REPEAT GEN_TAC THEN
  Induct_on `dimindex(:'N) - CARD(s:real['N]->bool)` THEN
  REPEAT STRIP_TAC THEN
  Q.ASM_CASES_TAC `v SUBSET (span(s:real['N]->bool))` THENL
   [PROVE_TAC[SUBSET_REFL], ALL_TAC, PROVE_TAC[SUBSET_REFL], ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV empty_rewrites[SUBSET_DEF]) THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `a:real['N]` STRIP_ASSUME_TAC) THENL
   [Q.EXISTS_TAC `(a:real['N]) INSERT s`,
    FIRST_X_ASSUM(MP_TAC o SPEC ``(a:real['N]) INSERT s``)] THEN
  Q.SUBGOAL_THEN `independent ((a:real['N]) INSERT s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INDEPENDENT_INSERT, COND_ID], ALL_TAC,
    ASM_REWRITE_TAC[INDEPENDENT_INSERT, COND_ID], ALL_TAC] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET] THENL
   [CONJ_TAC THENL
    [PROVE_TAC[SUBSET_INSERT, SPAN_SUPERSET, SUBSET_REFL], ALL_TAC] THEN
    Q.PAT_X_ASSUM `$= X Y` (MP_TAC o SYM) THEN
    PROVE_TAC[SUB_EQ_0, AND_IMP_INTRO, CARD_CLAUSES, NOT_LEQ,
            SPAN_SUPERSET, FINITE_INSERT, INDEPENDENT_BOUND], ALL_TAC] THEN
  Q.SUBGOAL_THEN `v' = dimindex (:'N) - CARD ((a:real['N]) INSERT s)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[GSYM SUC_SUB1] THEN
    ASM_SIMP_TAC bool_ss[INDEPENDENT_BOUND, CARD_CLAUSES], ALL_TAC] THEN
  PROVE_TAC[SPAN_SUPERSET, ADD1, SUB_PLUS]
QED

Theorem MAXIMAL_INDEPENDENT_SUBSET :
   !v:real['N]->bool. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b)
Proof
  MP_TAC(SPEC ``EMPTY:real['N]->bool`` MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  REWRITE_TAC[EMPTY_SUBSET, INDEPENDENT_EMPTY]
QED

(* ------------------------------------------------------------------------- *)
(* Notion of dimension.                                                      *)
(* ------------------------------------------------------------------------- *)

Definition dim_def :
   vector_dim (v :real['N] -> bool) =
            @n. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
                   (b HAS_SIZE n)
End

(* cf. real_topologyTheory.dim *)
Overload dim = “vector_dim”

Theorem BASIS_EXISTS :
   !v. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
           (b HAS_SIZE (dim v))
Proof
  GEN_TAC THEN REWRITE_TAC[dim_def] THEN CONV_TAC SELECT_CONV THEN
  PROVE_TAC[MAXIMAL_INDEPENDENT_SUBSET, HAS_SIZE_def, INDEPENDENT_BOUND]
QED

Theorem BASIS_EXISTS_FINITE :
   !v. ?b. FINITE b /\
           b SUBSET v /\
           independent b /\
           v SUBSET (span b) /\
           (b HAS_SIZE (dim v))
Proof
  PROVE_TAC[BASIS_EXISTS, INDEPENDENT_IMP_FINITE]
QED

Theorem BASIS_SUBSPACE_EXISTS :
   !s:real['N]->bool.
        subspace s
        ==> ?b. FINITE b /\
                b SUBSET s /\
                independent b /\
                (span b = s) /\
                (b HAS_SIZE dim s)
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.ISPEC `s:real['N]->bool` BASIS_EXISTS) THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  PROVE_TAC[SPAN_EQ_SELF, SPAN_MONO, INDEPENDENT_IMP_FINITE]
QED

(* ------------------------------------------------------------------------- *)
(* Consequences of independence or spanning for cardinality.                 *)
(* ------------------------------------------------------------------------- *)

Theorem INDEPENDENT_CARD_LE_DIM :
   !v b:real['N]->bool.
        b SUBSET v /\ independent b ==> FINITE b /\ CARD(b) <= dim v
Proof
  PROVE_TAC[BASIS_EXISTS, INDEPENDENT_SPAN_BOUND, HAS_SIZE_def, SUBSET_TRANS]
QED

Theorem SPAN_CARD_GE_DIM :
   !v b:real['N]->bool.
        v SUBSET (span b) /\ FINITE b ==> dim(v) <= CARD(b)
Proof
  PROVE_TAC[BASIS_EXISTS, INDEPENDENT_SPAN_BOUND, HAS_SIZE_def, SUBSET_TRANS]
QED

(* ------------------------------------------------------------------------- *)
(* Converses to those.                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem CARD_GE_DIM_INDEPENDENT :
   !v b:real['N]->bool.
        b SUBSET v /\ independent b /\ dim v <= CARD(b)
        ==> v SUBSET (span b)
Proof
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `!a:real['N]. ~(a IN v /\ ~(a IN span b))` MP_TAC THENL
   [ALL_TAC, PROVE_TAC[SUBSET_DEF]] THEN
  Q.X_GEN_TAC `a:real['N]` THEN STRIP_TAC THEN
  Q.SUBGOAL_THEN `independent((a:real['N]) INSERT b)` ASSUME_TAC THENL
   [PROVE_TAC[INDEPENDENT_INSERT], ALL_TAC] THEN
  MP_TAC(Q.ISPECL [`v:real['N]->bool`, `(a:real['N]) INSERT b`]
                INDEPENDENT_CARD_LE_DIM) THEN
  ASM_SIMP_TAC bool_ss[INSERT_SUBSET, CARD_CLAUSES, INDEPENDENT_BOUND] THEN
  PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF, Q.prove(
    `x <= y ==> ~(SUC y <= x)`, ARITH_TAC)]
QED

Theorem CARD_LE_DIM_SPANNING :
   !v b:real['N]->bool.
        v SUBSET (span b) /\ FINITE b /\ CARD(b) <= dim v
        ==> independent b
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[independent_def, dependent_def] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `a:real['N]` STRIP_ASSUME_TAC) THEN
  Q.SUBGOAL_THEN `dim(v:real['N]->bool) <= CARD(b DELETE (a:real['N]))` MP_TAC THENL
   [ALL_TAC,
    ASM_SIMP_TAC bool_ss[CARD_DELETE] THEN MATCH_MP_TAC
     (Q.prove(`b:num <= n /\ ~(b = 0) ==> ~(n <= b - 1)`, ARITH_TAC)) THEN
    ASM_SIMP_TAC bool_ss[CARD_EQ_0] THEN PROVE_TAC[MEMBER_NOT_EMPTY]] THEN
  MATCH_MP_TAC SPAN_CARD_GE_DIM THEN ASM_SIMP_TAC bool_ss[FINITE_DELETE] THEN
  REWRITE_TAC[SUBSET_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SPAN_TRANS THEN Q.EXISTS_TAC `a:real['N]` THEN
  ASM_SIMP_TAC bool_ss[INSERT_DELETE] THEN
  PROVE_TAC[SUBSET_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* More general size bound lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

Theorem SPANS_IMAGE :
   !f b v. linear f /\ v SUBSET (span b)
           ==> (IMAGE f v) SUBSET span(IMAGE f b)
Proof
  SIMP_TAC bool_ss[SPAN_LINEAR_IMAGE, IMAGE_SUBSET]
QED

(* ------------------------------------------------------------------------- *)
(* Relation between bases and injectivity/surjectivity of map.               *)
(* ------------------------------------------------------------------------- *)

Theorem SPANNING_SURJECTIVE_IMAGE :
   !f:real['M]->real['N] s.
        UNIV SUBSET (span s) /\ linear f /\ (!y. ?x. f(x) = y)
        ==> UNIV SUBSET span(IMAGE f s)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  Q.EXISTS_TAC `IMAGE (f:real['M]->real['N]) UNIV` THEN
  ASM_SIMP_TAC bool_ss[SPANS_IMAGE] THEN
  REWRITE_TAC[SUBSET_DEF, IN_UNIV, IN_IMAGE] THEN PROVE_TAC[]
QED

Theorem INDEPENDENT_INJECTIVE_IMAGE_GEN :
   !f:real['M]->real['N] s.
        independent s /\ linear f /\
        (!x y. x IN span s /\ y IN span s /\ (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)
Proof
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[independent_def, DEPENDENT_EXPLICIT] THEN
  REWRITE_TAC[CONJ_ASSOC, FINITE_SUBSET_IMAGE] THEN
  SIMP_TAC bool_ss[PROVE[]
     ``(?s u. ((?t. p t /\ (s = f t)) /\ q s u) /\ r s u) <=>
      (?t u. p t /\ q (f t) u /\ r (f t) u)``] THEN
  SIMP_TAC bool_ss[EXISTS_IN_IMAGE, GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY Q.X_GEN_TAC [`t:real['M]->bool`, `u:real['N]->real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY Q.EXISTS_TAC
   [`t:real['M]->bool`, `(u:real['N]->real) o (f:real['M]->real['N])`] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_VSUM THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN PROVE_TAC[SUBSET_DEF],
    REWRITE_TAC[SPAN_0],
    ASM_SIMP_TAC bool_ss[LINEAR_VSUM] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP LINEAR_0) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ASM_SIMP_TAC bool_ss[o_DEF, LINEAR_CMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
    PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF]]
QED

Theorem INDEPENDENT_INJECTIVE_IMAGE :
   !f:real['M]->real['N] s.
        independent s /\ linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
  PROVE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* We can extend a linear basis-basis injection to the whole set.            *)
(* ------------------------------------------------------------------------- *)

Theorem LINEAR_INDEP_IMAGE_LEMMA :
   !f b. linear(f:real['M]->real['N]) /\
         FINITE b /\
         independent (IMAGE f b) /\
         (!x y. x IN b /\ y IN b /\ (f x = f y) ==> (x = y))
         ==> !x. x IN span b ==> (f(x) = (vec 0)) ==> (x = (vec 0))
Proof
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) empty_rewrites[AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL [SIMP_TAC bool_ss[IN_SING, SPAN_EMPTY], ALL_TAC] THEN
  Q.X_GEN_TAC `b:real['M]->bool` THEN STRIP_TAC THEN
  Q.X_GEN_TAC `a:real['M]` THEN STRIP_TAC THEN
  Q.PAT_X_ASSUM `$==> X Y` MP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [PROVE_TAC[INDEPENDENT_MONO, IMAGE_CLAUSES, SUBSET_DEF, IN_INSERT],
    ALL_TAC] THEN
  DISCH_TAC THEN STRIP_TAC THEN Q.X_GEN_TAC `x:real['M]` THEN DISCH_TAC THEN
  MP_TAC(Q.ISPECL [`a:real['M]`, `(a:real['M]) INSERT b`, `x:real['M]`]
    SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  SIMP_TAC bool_ss[ASSUME ``~((a:real['M]) IN b)``, Q.prove(
    `~(a IN b) ==> ((a INSERT b) DELETE a = b)`,
        REWRITE_TAC[DELETE_INSERT, DELETE_NON_ELEMENT])] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  Q.SUBGOAL_THEN `(f:real['M]->real['N])(x - k * a) IN span(IMAGE f b)` MP_TAC THENL
   [PROVE_TAC[SPAN_LINEAR_IMAGE, IN_IMAGE], ALL_TAC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH ``(vec 0) - k * x = (-k) * x``] THEN
  Q.ASM_CASES_TAC `k = &0` THENL
   [PROVE_TAC[VECTOR_ARITH ``x:real['N] - &0 * y = x``], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC ``-inv(k)`` o MATCH_MP SPAN_MUL) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC, REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
  SIMP_TAC bool_ss[REAL_NEGNEG, REAL_MUL_LINV, ASSUME ``~(k = &0)``] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites[independent_def]) THEN
  SIMP_TAC bool_ss[dependent_def, NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC ``(f:real['M]->real['N]) a``) THEN
  Q.SUBGOAL_THEN
   `IMAGE (f:real['M]->real['N]) (a INSERT b) DELETE f a =
    IMAGE f ((a INSERT b) DELETE a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_IMAGE, IN_DELETE, IN_INSERT] THEN
    PROVE_TAC[IN_INSERT],
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DELETE_INSERT] THEN
  SIMP_TAC bool_ss[Q.prove(`~(a IN b) ==> (b DELETE a = b)`, REWRITE_TAC[DELETE_NON_ELEMENT]),
           ASSUME ``~(a:real['M] IN b)``] THEN
  SIMP_TAC bool_ss[IMAGE_CLAUSES, IN_INSERT]
QED

(* ------------------------------------------------------------------------- *)
(* We can extend a linear mapping from basis.                                *)
(* ------------------------------------------------------------------------- *)

Theorem LINEAR_INDEPENDENT_EXTEND_LEMMA :
   !f b. FINITE b
         ==> independent b
             ==> ?g:real['M]->real['N].
                        (!x y. x IN span b /\ y IN span b
                                ==> (g(x + y) = g(x) + g(y))) /\
                        (!x c. x IN span b ==> (g(c * x) = c * g(x))) /\
                        (!x. x IN b ==> (g x = f x))
Proof
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY, INDEPENDENT_INSERT] THEN CONJ_TAC THENL
   [STRIP_TAC THEN Q.EXISTS_TAC `(\x. (vec 0)):real['M]->real['N]` THEN
    SIMP_TAC bool_ss[SPAN_EMPTY] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC,
    ALL_TAC] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY Q.X_GEN_TAC [`b:real['M]->bool`, `a:real['M]`] THEN
  DISCH_THEN(fn th => REPEAT STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `h = \z:real['M]. @k. (z - k * a) IN span b` THEN
  Q.SUBGOAL_THEN `!z:real['M]. z IN span(a INSERT b)
                    ==> (z - h(z) * a) IN span(b) /\
                        !k. (z - k * a) IN span(b) ==> (k = h(z))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [Q.UNABBREV_TAC `h` THEN BETA_TAC THEN CONV_TAC SELECT_CONV THEN
      PROVE_TAC[SPAN_BREAKDOWN_EQ],
      ALL_TAC] THEN
    SIMP_TAC bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH ``(z - a * v:real['M]) - (z - b * v) = (b - a) * v``] THEN
    Q.ASM_CASES_TAC `k = (h:real['M]->real) z` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC ``inv(k - (h:real['M]->real) z)`` o
               MATCH_MP SPAN_MUL) THEN
    ASM_SIMP_TAC bool_ss[REAL_MUL_LINV, VECTOR_MUL_ASSOC, REAL_SUB_0] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID],
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO, Once FORALL_AND_THM] THEN
  STRIP_TAC THEN
  Q.EXISTS_TAC `\z:real['M]. h(z) * (f:real['M]->real['N])(a) + g(z - h(z) * a)` THEN
  REPEAT CONJ_TAC THENL (* 3 subgoals *)
  [ (* goal 1 (of 3) *)
    MAP_EVERY Q.X_GEN_TAC [`x:real['M]`, `y:real['M]`] THEN STRIP_TAC THEN
    Q.SUBGOAL_THEN `(h:real['M]->real)(x + y) = h(x) + h(y)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       ``(x + y) - (k + l) * a:real['M] = (x - k * a) + (y - l * a)``] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_ADD THEN ASM_SIMP_TAC bool_ss[],
      ALL_TAC] THEN
    ASM_SIMP_TAC bool_ss[VECTOR_ARITH
       ``(x + y) - (k + l) * a:real['M] = (x - k * a) + (y - l * a)``] THEN
    VECTOR_ARITH_TAC,
    (* goal 2 (of 3) *)
    MAP_EVERY Q.X_GEN_TAC [`x:real['M]`, `c:real`] THEN STRIP_TAC THEN
    Q.SUBGOAL_THEN `(h:real['M]->real)(c * x:real['M]) = c * h(x)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       ``c * x - (c * k) * a:real['M] = c * (x - k * a)``] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN ASM_SIMP_TAC bool_ss[],
      ALL_TAC] THEN
    ASM_SIMP_TAC bool_ss[VECTOR_ARITH
       ``c * x - (c * k) * a:real['M] = c * (x - k * a)``] THEN
    VECTOR_ARITH_TAC,
    (* goal 3 (of 3) *)
    ALL_TAC ] THEN
  Q.X_GEN_TAC `x:real['M]` THEN BETA_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
  [ Q.SUBGOAL_THEN `&1 = h(a:real['M])` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC, ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH ``a - &1 * a = (vec 0)``, SPAN_0] THENL
     [PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF, IN_INSERT], ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o Q.SPECL [`(vec 0):real['M]`, `(vec 0):real['M]`]) THEN
    REWRITE_TAC[SPAN_0, VECTOR_ADD_LID] THEN
    REWRITE_TAC[VECTOR_ARITH ``(a = a + a) <=> (a = (vec 0))``] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC,
    ALL_TAC ] THEN
  Q.SUBGOAL_THEN `&0 = h(x:real['M])` (SUBST1_TAC o SYM) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC, ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LID, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO] THEN
  PROVE_TAC[SUBSET_DEF, IN_INSERT, SPAN_SUPERSET]
QED

Theorem LINEAR_INDEPENDENT_EXTEND :
   !f b. independent b
         ==> ?g:real['M]->real['N]. linear g /\ (!x. x IN b ==> (g x = f x))
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.ISPECL [`b:real['M]->bool`, `(UNIV:real['M]->bool)`]
           MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV, UNIV_SUBSET] THEN
  REWRITE_TAC[EXTENSION, IN_UNIV] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `c:real['M]->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(Q.ISPECL [`f:real['M]->real['N]`, `c:real['M]->bool`]
    LINEAR_INDEPENDENT_EXTEND_LEMMA) THEN
  ASM_SIMP_TAC bool_ss[INDEPENDENT_BOUND, linear_def] THEN
  PROVE_TAC[SUBSET_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Linear functions are equal on a subspace if they are on a spanning set.   *)
(* ------------------------------------------------------------------------- *)

Theorem SUBSPACE_KERNEL :
   !f. linear f ==> subspace {x | f(x) = (vec 0)}
Proof
  SIMP_TAC bool_ss[subspace_def, GSPEC_ETA, IN_ABS] THEN
  SIMP_TAC bool_ss[LINEAR_ADD, LINEAR_CMUL, VECTOR_ADD_LID, VECTOR_MUL_RZERO] THEN
  REWRITE_TAC [LINEAR_0]
QED

(* |- (a <=> b) ==> a ==> b *)
Theorem EQ_IMP[local] = Q.SPECL [‘a’, ‘b’] EQ_IMPLIES

Theorem LINEAR_EQ_0_SPAN :
   !f:real['M]->real['N] b.
        linear f /\ (!x. x IN b ==> (f(x) = (vec 0)))
        ==> !x. x IN span(b) ==> (f(x) = (vec 0))
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC SPAN_INDUCT THEN ASM_SIMP_TAC bool_ss[IN_ABS] THEN
  MP_TAC(Q.ISPEC `f:real['M]->real['N]` SUBSPACE_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS]
QED

Theorem LINEAR_EQ_0 :
   !f b (s :real['N]->bool).
           linear f /\ s SUBSET (span b) /\ (!x. x IN b ==> (f(x) = (vec 0)))
           ==> !x. x IN s ==> (f(x) = (vec 0))
Proof
  PROVE_TAC[LINEAR_EQ_0_SPAN, SUBSET_DEF]
QED

Theorem LINEAR_EQ :
   !f g b (s :real['N]->bool). linear f /\ linear g /\ s SUBSET (span b) /\
             (!x. x IN b ==> (f(x) = g(x)))
              ==> !x. x IN s ==> (f(x) = g(x))
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  STRIP_TAC THEN HO_MATCH_MP_TAC LINEAR_EQ_0 THEN
  METIS_TAC[LINEAR_COMPOSE_SUB]
QED

Theorem LINEAR_EQ_STDBASIS :
   !f:real['M]->real['N] g.
        linear f /\ linear g /\
        (!i. i < dimindex(:'M)
             ==> (f(basis i) = g(basis i)))
        ==> (f = g)
Proof
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `!x. x IN UNIV ==> ((f:real['M]->real['N]) x = g x)`
   (fn th => MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM, IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_EQ THEN
  Q.EXISTS_TAC `{basis i :real['M] | i < dimindex(:'M)}` THEN
  ASM_SIMP_TAC bool_ss[SPAN_STDBASIS, SUBSET_REFL] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[]
QED

(* ------------------------------------------------------------------------- *)
(* An injective map real^N->real^N is also surjective.                       *)
(* ------------------------------------------------------------------------- *)

Theorem LINEAR_INJECTIVE_IMP_SURJECTIVE :
   !f:real['N]->real['N].
        linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> !y. ?x. f(x) = y
Proof
  REPEAT STRIP_TAC THEN
  MP_TAC(Q.ISPEC `(UNIV:real['N]->bool)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV, HAS_SIZE_def] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `b:real['N]->bool` STRIP_ASSUME_TAC) THEN
  Q.SUBGOAL_THEN `UNIV SUBSET span(IMAGE (f:real['N]->real['N]) b)` MP_TAC THENL
   [MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    PROVE_TAC[INDEPENDENT_INJECTIVE_IMAGE, LESS_EQ_REFL,
              SUBSET_UNIV, CARD_IMAGE_INJ],
    ASM_SIMP_TAC bool_ss[SPAN_LINEAR_IMAGE] THEN
    PROVE_TAC[SUBSET_DEF, IN_IMAGE, IN_UNIV]]
QED

(* ------------------------------------------------------------------------- *)
(* And vice versa.                                                           *)
(* ------------------------------------------------------------------------- *)

Theorem LINEAR_SURJECTIVE_IMP_INJECTIVE :
   !f:real['N]->real['N].
        linear f /\ (!y. ?x. f(x) = y)
        ==> !x y. (f(x) = f(y)) ==> (x = y)
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(Q.ISPEC `(UNIV:real['N]->bool)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV, HAS_SIZE_def] THEN
  DISCH_THEN(Q.X_CHOOSE_THEN `b:real['N]->bool` STRIP_ASSUME_TAC) THEN
  Q.SUBGOAL_THEN
   `!x. x IN span b ==> ((f:real['N]->real['N]) x = (vec 0)) ==> (x = (vec 0))`
   (fn th => PROVE_TAC[th, LINEAR_INJECTIVE_0, SUBSET_DEF, IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_INDEP_IMAGE_LEMMA THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN
    Q.EXISTS_TAC `(UNIV:real['N]->bool)` THEN
    ASM_SIMP_TAC bool_ss[IMAGE_FINITE, SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SUBSET_DEF, IN_UNIV, IN_IMAGE] THEN
    PROVE_TAC[CARD_IMAGE_LE, SUBSET_DEF, IN_UNIV],
    ALL_TAC] THEN
  Q.SUBGOAL_THEN `dim(UNIV:real['N]->bool) <= CARD(IMAGE (f:real['N]->real['N]) b)`
  MP_TAC THENL
   [MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_SIMP_TAC bool_ss[SPAN_LINEAR_IMAGE, IMAGE_FINITE] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    Q.EXISTS_TAC `IMAGE (f:real['N]->real['N]) UNIV` THEN
    ASM_SIMP_TAC bool_ss[IMAGE_SUBSET] THEN
    ASM_REWRITE_TAC[SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN PROVE_TAC[],
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o Q.ISPEC `f:real['N]->real['N]` o
                MATCH_MP CARD_IMAGE_LE) THEN
  ASM_REWRITE_TAC[AND_IMP_INTRO] THEN DISCH_TAC THEN
  MP_TAC(Q.ISPECL
   [`b:real['N]->bool`, `IMAGE (f:real['N]->real['N]) b`, `f:real['N]->real['N]`]
   SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC bool_ss[IMAGE_FINITE, INDEPENDENT_BOUND, SUBSET_REFL, LESS_EQUAL_ANTISYM] THEN
  SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN PROVE_TAC[]
QED

Theorem LINEAR_SURJECTIVE_IFF_INJECTIVE :
   !f:real['N]->real['N].
      linear f ==> ((!y. ?x. f x = y) <=> (!x y. (f x = f y) ==> (x = y)))
Proof
  PROVE_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE,
            LINEAR_SURJECTIVE_IMP_INJECTIVE]
QED

(* ------------------------------------------------------------------------- *)
(* Hence either is enough for isomorphism.                                   *)
(* ------------------------------------------------------------------------- *)

(* cf. permutationTheory.INVERSE_UNIQUE_o *)
Theorem LEFT_RIGHT_INVERSE_EQ :
   !f:'a->'a g h. (f o g = I) /\ (g o h = I) ==> (f = h)
Proof
  PROVE_TAC[o_ASSOC, I_o_ID]
QED

Theorem ISOMORPHISM_EXPAND :
   !f g. (f o g = I) /\ (g o f = I) <=> (!x. f(g x) = x) /\ (!x. g(f x) = x)
Proof
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM]
QED

Theorem LINEAR_INJECTIVE_LEFT_INVERSE :
   !f:real['M]->real['N].
        linear f /\ (!x y. (f x = f y) ==> (x = y))
        ==> ?g. linear g /\ (g o f = I)
Proof
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE] THEN REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN
   `?h. linear(h:real['N]->real['M]) /\
        !x. x IN IMAGE (f:real['M]->real['N])
               {basis i | i < dimindex(:'M)} ==> (h x = g x)`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE THEN
    PROVE_TAC[INJECTIVE_LEFT_INVERSE, INDEPENDENT_STDBASIS],
    HO_MATCH_MP_TAC MONO_EXISTS THEN Q.X_GEN_TAC `h:real['N]->real['M]` THEN
    ASM_SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN
        CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC bool_ss[I_THM, LINEAR_COMPOSE, o_THM] THEN
    SIMP_TAC bool_ss[I_DEF, K_DEF, S_DEF, LINEAR_ID] THEN
        PROVE_TAC[]]
QED

Theorem LINEAR_SURJECTIVE_RIGHT_INVERSE :
   !f:real['M]->real['N].
        linear f /\ (!y. ?x. f x = y) ==> ?g. linear g /\ (f o g = I)
Proof
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE] THEN REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN
   `?h. linear(h:real['N]->real['M]) /\
        !x. x IN {basis i | i < dimindex(:'N)} ==> (h x = g x)`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS],
    HO_MATCH_MP_TAC MONO_EXISTS THEN Q.X_GEN_TAC `h:real['N]->real['M]` THEN
    ASM_SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN
        CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC bool_ss[I_THM, LINEAR_COMPOSE, o_THM] THEN
    SIMP_TAC bool_ss[I_DEF, K_DEF, S_DEF, LINEAR_ID] THEN
        PROVE_TAC[]]
QED

Theorem LINEAR_INJECTIVE_ISOMORPHISM :
   !f:real['N]->real['N].
        linear f /\ (!x y. (f x = f y) ==> (x = y))
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)
Proof
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(Q.ISPEC `f:real['N]->real['N]` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(Q.ISPEC `f:real['N]->real['N]` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(Q.ISPEC `f:real['N]->real['N]` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  ASM_SIMP_TAC bool_ss[] THEN PROVE_TAC[LEFT_RIGHT_INVERSE_EQ]
QED

Theorem LINEAR_SURJECTIVE_ISOMORPHISM :
   !f:real['N]->real['N].
        linear f /\ (!y. ?x. f x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)
Proof
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(Q.ISPEC `f:real['N]->real['N]` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(Q.ISPEC `f:real['N]->real['N]` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(Q.ISPEC `f:real['N]->real['N]` LINEAR_SURJECTIVE_IMP_INJECTIVE) THEN
  ASM_SIMP_TAC bool_ss[] THEN PROVE_TAC[LEFT_RIGHT_INVERSE_EQ]
QED

(* ------------------------------------------------------------------------- *)
(* Left and right inverses are the same for R^N->R^N.                        *)
(* ------------------------------------------------------------------------- *)

Theorem LINEAR_INVERSE_LEFT :
   !f:real['N]->real['N] f'.
        linear f /\ linear f' ==> ((f o f' = I) <=> (f' o f = I))
Proof
  Q.SUBGOAL_THEN
   `!f:real['N]->real['N] f'.
        linear f /\ linear f' /\ (f o f' = I) ==> (f' o f = I)`
   (fn th => PROVE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(Q.ISPEC `f:real['N]->real['N]` LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  PROVE_TAC[]
QED


val _ = export_theory ();
val _ = html_theory "vector";

(* References:

  [1] Z. Shi, Y. Guan, X. Li, Formalization of Complex Analysis and Matrix Theory,
      Springer, Singapore, 2020. doi:10.1007/978-981-15-7261-6.
  [2] D. Cox, J. Little, D. O'Shea, Ideals, Varieties, and Algorithms, Third,
      Springer Science & Business Media, 2013. doi:10.1007/978-1-4757-2693-0.
 *)
