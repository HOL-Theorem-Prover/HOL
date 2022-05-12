(* ========================================================================= *)
(* Real vectors in Euclidean space, and elementary linear algebra.           *)
(*     (HOL-Light's Multivariate/vectors.ml)                                 *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*       (c) Copyright, Liming Li, Yong Guan and Zhiping Shi 2011            *)
(*               (c) Copyright, Marco Maggesi 2014                           *)
(*       (c) Copyright, Andrea Gabrielli, Marco Maggesi 2016-2017            *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory PairedLambda
     pred_setLib fcpTheory fcpLib tautLib numLib listTheory rich_listTheory;

open realTheory realLib iterateTheory real_sigmaTheory RealArith mesonLib;

open hurdUtils permutationTheory;

val _ = new_theory "vector";

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

(* this is experimental, for user code only (not used in the rest of file) *)
val _ = add_numeral_form (#"v", SOME "vec");

(* prioritize_real() *)
val _ = prefer_real();

(* ------------------------------------------------------------------------- *)
(* Dot products.                                                             *)
(* ------------------------------------------------------------------------- *)

(* Infixl 600 is the same as "*", "INTER" and "*_c", etc. *)
val _ = set_fixity "dot"  (Infixl 600); (* was: Infixr 20 (HOL-Light) *)

(* This definition is based on ‘iterate$sum’ (iterateTheory.sum_def).

   NOTE: The original definition of ‘dot’ in HOL-Light is

     sum(1..dimindex(:N)) (\i. x$i * y$i)

   It seems that in HOL-Light FCP indexes start from 1 (instead of 0 in HOL4),
   and whenever the original proofs use DIMINDEX_GE_1, in the ported proofs we
   should use DIMINDEX_GT_0 instead. (See, e.g., the proof of VEC_EQ below.)
 *)
Definition dot_def :
   ((x:real['N]) dot (y:real['N])) =
     sum (count(dimindex(:'N))) (\i. (x ' i) * (y ' i))
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

val VECTOR_ARITH_TAC =
    rpt GEN_TAC
 >> SIMP_TAC std_ss [dot_def, GSYM SUM_ADD', GSYM SUM_SUB', FINITE_COUNT,
                     GSYM SUM_LMUL, GSYM SUM_RMUL, GSYM SUM_NEG']
 >> (MATCH_MP_TAC SUM_EQ' ORELSE MATCH_MP_TAC SUM_EQ_0' ORELSE
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
  MATCH_MP_TAC SUM_EQ' THEN ASM_SIMP_TAC bool_ss[]
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
  [MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][], ALL_TAC,
   MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
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

Overload "linear" = “vec_linear :(real['M]->real['N])->bool”

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
  >- (MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][VSUM_COMPONENT, GSYM SUM_RMUL]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'M)))
        (\i. x ' i * sum (count (dimindex (:'N))) (\i'. f (basis i) ' i' * y ' i'))` THEN
  CONJ_TAC
  >- (REWRITE_TAC[GSYM SUM_LMUL] THEN
      SIMP_TAC bool_ss[Once SUM_SWAP, FINITE_COUNT] THEN
      MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[][] THEN MATCH_MP_TAC SUM_EQ' THEN
      SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT, LINEAR_CMUL, REAL_MUL_ASSOC]) THEN
  MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]
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

Theorem MATRIX_ADD_LDISTRIB :
   !A:real['P]['M] B:real['N]['P] C. A ** (B + C) = A ** B + A ** C
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_add_def, GSYM SUM_ADD'] THEN
  MATCH_MP_TAC SUM_EQ' THEN
  SRW_TAC[FCP_ss][REAL_ADD_LDISTRIB]
QED

Theorem VECTOR_DOT_FCP2 :
  !f u v. (($FCP f :real['N]) dot v) =
           sum (count (dimindex(:'N))) (\i. f i * (v ' i)) /\
          (u dot ($FCP f :real['N])) =
           sum (count (dimindex(:'N))) (\i. (u ' i) * f i)
Proof
    SRW_TAC [FCP_ss] [dot_def, SUM_EQ']
QED

Theorem MATRIX_MUL_EQ :
    !A:real['P]['M] B:real['N]['P] k:real.
        (FCP i j. sum (count(dimindex(:'P))) (\k. A ' i ' k * B ' k ' j)) =
        (FCP i j. (row i A) dot (column j B)): real['N]['M]
Proof
    SRW_TAC[FCP_ss][dot_def, row_def, column_def] THEN
    MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]
QED

Theorem MATRIX_MUL_ASSOC :
    !(A:real['N]['M]) (B:real['P]['N]) (C:real['Q]['P]).
      (A ** B) ** C = A ** (B ** C)
Proof
    SRW_TAC [FCP_ss][matrix_mul_def, MATRIX_MUL_EQ, ROW_FCP, COLUMN_FCP, VECTOR_DOT_FCP2] THEN
    rename1 ‘j < dimindex(:'Q)’ \\
    SRW_TAC [][dot_def, GSYM SUM_LMUL, GSYM SUM_RMUL] THEN
    SRW_TAC [][Once SUM_SWAP] THEN
    MATCH_MP_TAC SUM_EQ' THEN
    Q.X_GEN_TAC ‘k’ >> SRW_TAC [][] THEN
    MATCH_MP_TAC SUM_EQ' THEN
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
  >- (MATCH_MP_TAC SUM_EQ' THEN
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
  >- (MATCH_MP_TAC SUM_EQ' THEN
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
  CONJ_TAC >- (MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC
   `sum (count (dimindex (:'P)))
    (\j. sum (count (dimindex (:'N))) (\k. A ' i ' k * B ' k ' j) * x ' j)` THEN
  reverse CONJ_TAC >- (MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]) THEN
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
  CONJ_TAC >- (MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]) \\
  REWRITE_TAC[COND_RATOR, COND_RAND] THEN
  ASM_SIMP_TAC bool_ss[SUM_DELTA, REAL_MUL_LZERO, IN_COUNT, REAL_MUL_LID]
QED

Theorem MATRIX_VECTOR_MUL_LZERO :
   !x:real['N]. (mat 0 :real['N]['M]) ** x = vec 0
Proof
  SRW_TAC[FCP_ss][mat_def, matrix_vector_mul_def, VEC_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `sum (count (dimindex (:'N))) (\j. 0 * x ' j)` THEN
  CONJ_TAC >- (MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]) \\
  REWRITE_TAC[REAL_MUL_LZERO, SUM_0']
QED

Theorem MATRIX_VECTOR_MUL_RZERO :
   !A:real['N]['M]. A ** (vec 0) = (vec 0)
Proof
  SRW_TAC[FCP_ss][matrix_vector_mul_def, VEC_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  Q.EXISTS_TAC `sum (count (dimindex (:'N))) (\j. 0)` THEN
  reverse CONJ_TAC >- REWRITE_TAC[SUM_0'] \\
  MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][VEC_COMPONENT]
QED

Theorem MATRIX_TRANSP_MUL :
   !A:real['N]['M] B. transp(A ** B) = transp(B) ** transp(A)
Proof
  SRW_TAC[FCP_ss][matrix_mul_def, transp_def] THEN
  MATCH_MP_TAC SUM_EQ' THEN
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
   >- (REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]) THEN
  Q.SUBGOAL_THEN `!i i'.
   (sum (count (dimindex (:'N)))
   (\j. B:real['N]['M] ' i' ' j * (FCP i'. if i' = i then 1 else 0):real['N] ' j) =
        sum (count (dimindex (:'N)))
   (\j. B ' i' ' j * if j = i then 1 else 0))` ASSUME_TAC
   >- (REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ' THEN SRW_TAC[FCP_ss][]) THEN
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
  SRW_TAC[FCP_ss][] THEN MATCH_MP_TAC SUM_EQ' THEN BETA_TAC THEN SRW_TAC[FCP_ss][]
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
   [MATCH_MP_TAC SUM_EQ' THEN SRW_TAC [][] THEN SRW_TAC [FCP_ss][],
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

val _ = export_theory ();
val _ = html_theory "vector";
