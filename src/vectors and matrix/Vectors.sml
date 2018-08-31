(* ==================================================================   
TITLE: Developing the theory of vectors and matrix
 It is translated from the corresponding code file of Harrision in Hol-Light.	            
AUTHORS  : (Copyright) Liming Li, Yong Guan and Zhiping Shi
             Beijing Engineering Research Center of High Reliable      
             Emmbedded System, Capital Normal University, China 
DATE  : 2011.08.2   

 ================================================================== *)
(* ------------------------------------------------------------------------- *)
(* Basic componentwise operations on vectors.                                *)
(* ------------------------------------------------------------------------- *)

val vec_map_def  = Define`
  vec_map f (v:real['a]) = (FCP i. f (v ' i)):real['a]`;

val vec_map2_def = Define`
  vec_map2 f (v1:real['a]) (v2:real['a]) =
  (FCP i. f (v1 ' i) (v2 ' i)):real['a]`;

val vec_neg_def = Define `vec_neg = vec_map(~)`;

val vec_sub_def  = Define `vec_sub = vec_map2 (-)`;

val vec_add_def  = Define `vec_add = vec_map2 (+)`;

val _ = overload_on ("+", ``vec_add :real['a] -> real['a] -> real['a]``);
val _ = overload_on ("-", ``vec_sub :real['a] -> real['a] -> real['a]``);
val _ = overload_on ("~", ``vec_neg :real['a] -> real['a]``);

(* ------------------------------------------------------------------------- *)
(* Also the scalar-vector multiplication.                                    *)
(* ------------------------------------------------------------------------- *)

val vec_mul_def = Define `vec_mul n = vec_map (\v. n * v)`;
val _ = overload_on ("*", ``vec_mul:real -> real['a] -> real['a]``);
(* ------------------------------------------------------------------------- *)
(* Vectors corresponding to small naturals. Perhaps should overload "&"?     *)
(* ------------------------------------------------------------------------- *)

val VECTOR_0 = Define `VECTOR_0 = FCP i. &0`;

(* ------------------------------------------------------------------------- *)
(* Dot products.                                                             *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "dot"  (Infixl 20);
val dot_def = Define`
    ((x:real['a]) dot (y:real['a])) = 
    SUM (count(dimindex(:'a))) (\i. (x ' i ) * (y ' i))`;

(* ------------------------------------------------------------------------- *)
(* A naive proof procedure to lift really trivial arithmetic stuff from R.   *)
(* ------------------------------------------------------------------------- *)

val VECTOR_ARITH_TAC =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[dot_def, GSYM SUM_ADD_COUNT, GSYM SUM_SUB_COUNT,
              GSYM SUM_LMUL, GSYM SUM_RMUL, GSYM SUM_NEG] THEN
  (MATCH_MP_TAC SUM_EQ_COUNT ORELSE MATCH_MP_TAC SUM_EQ_0_COUNT ORELSE
   GEN_REWRITE_TAC ONCE_DEPTH_CONV empty_rewrites [CART_EQ]) THEN
  SIMP_TAC bool_ss[GSYM FORALL_AND_THM] THEN TRY EQ_TAC THEN
  TRY(HO_MATCH_MP_TAC MONO_ALL) THEN TRY(GEN_TAC) THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`,
              TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`] THEN
  TRY(MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`)) THEN
  SRW_TAC[FCP_ss][vec_add_def, vec_sub_def, vec_neg_def, vec_mul_def, VECTOR_0,
                  vec_map_def, vec_map2_def] THEN POP_ASSUM MP_TAC THEN
  REAL_ARITH_TAC;

fun VECTOR_ARITH tm = Tactical.default_prover (tm,VECTOR_ARITH_TAC);
(* ------------------------------------------------------------------------- *)
(* Obvious "component-pushing".                                              *)
(* ------------------------------------------------------------------------- *)

val VEC_0_COMPONENT = prove 
(`!i. i<dimindex(:'n) ==> ((VECTOR_0:real['n]) ' i = &0)`,
 SRW_TAC [fcpLib.FCP_ss] [VECTOR_0]);

val VECTOR_ADD_COMPONENT = store_thm(
"VECTOR_ADD_COMPONENT",
`!x:real['a] y i. i < dimindex (:'a) ==> ((x + y) ' i = (x ' i) + (y ' i))`,
SRW_TAC [fcpLib.FCP_ss][vec_add_def,vec_map2_def]);

val VECTOR_NEG_COMPONENT = store_thm(
  "VECTOR_NEG_COMPONENT",
  `!x:real['a] i. i < dimindex (:'a) ==> ((~x) ' i = -(x ' i))`,
  SRW_TAC [fcpLib.FCP_ss][vec_neg_def,vec_map_def]);

val VECTOR_SUB_COMPONENT = store_thm(
"VECTOR_SUB_COMPONENT",
`!x:real['a] y i. i < dimindex (:'a) ==> ((x - y) ' i = (x ' i) - (y ' i))`,
SRW_TAC [fcpLib.FCP_ss][vec_sub_def,vec_map2_def]);

val VECTOR_MUL_COMPONENT = store_thm(
"VECTOR_MUL_COMPONENT",
`!x:real['a] c i. i < dimindex (:'a) ==> ((c * x) ' i = c * (x ' i))`,
SRW_TAC [fcpLib.FCP_ss][vec_mul_def,vec_map_def]);

val COND_COMPONENT = prove
 (`(if b then x else y) ' i = if b then x ' i else y ' i`,
  PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Some frequently useful arithmetic lemmas over vectors.                    *)
(* ------------------------------------------------------------------------- *)

val VECTOR_ADD_SYM = VECTOR_ARITH ``!x y:real['a]. x + y = y + x``;

val VECTOR_ADD_LID = VECTOR_ARITH ``!x. VECTOR_0 + x = x``;

val VECTOR_ADD_RID = VECTOR_ARITH ``!x. x + VECTOR_0 = x``;

val VECTOR_SUB_REFL = VECTOR_ARITH ``!x. x - x = VECTOR_0``;

val VECTOR_ADD_LINV = VECTOR_ARITH ``!x. ~x + x = VECTOR_0``;

val VECTOR_ADD_RINV = VECTOR_ARITH ``!x. x + ~x = VECTOR_0``;

val VECTOR_SUB_RADD = VECTOR_ARITH ``!x y. x - (x + y) = ~y:real['n]``;

val VECTOR_NEG_SUB = VECTOR_ARITH ``!x:real['n] y. ~(x - y) = y - x``;

val VECTOR_SUB_EQ = VECTOR_ARITH ``!x y. (x - y = VECTOR_0) <=> (x = y)``;

val VECTOR_MUL_ASSOC = VECTOR_ARITH ``!a b x. a * (b * x) = (a * b) * x``;

val VECTOR_MUL_LID = VECTOR_ARITH ``!x. &1 * x = x``;

val VECTOR_MUL_LZERO = VECTOR_ARITH ``!x. &0 * x = VECTOR_0``;

val VECTOR_SUB_ADD = VECTOR_ARITH ``(x - y) + y = x:real['n]``;

val VECTOR_SUB_ADD2 = VECTOR_ARITH ``y + (x - y) = x:real['n]``;

val VECTOR_ADD_LDISTRIB = VECTOR_ARITH ``c * (x + y) = c * x + c * y``;

val VECTOR_SUB_LDISTRIB = VECTOR_ARITH ``c * (x - y) = c * x - c * y``;

val VECTOR_ADD_RDISTRIB = VECTOR_ARITH ``(a + b) * x = a * x + b * x``;

val VECTOR_SUB_RDISTRIB = VECTOR_ARITH ``(a - b) * x = a * x - b * x``;

val VECTOR_ADD_SUB = VECTOR_ARITH ``(x + y:real['n]) - x = y``;

val VECTOR_EQ_ADDR = VECTOR_ARITH ``(x + y = x) <=> (y = VECTOR_0)``;

val VECTOR_EQ_ADDL = VECTOR_ARITH ``(x + y = y) <=> (x = VECTOR_0)``;

val VECTOR_SUB = VECTOR_ARITH ``x - y = x + ~(y:real['n])``;

val VECTOR_SUB_RZERO = VECTOR_ARITH ``x - VECTOR_0 = x``;

val VECTOR_MUL_RZERO = VECTOR_ARITH ``c * VECTOR_0 = VECTOR_0``;

val VECTOR_NEG_MINUS1 = VECTOR_ARITH ``~x = (-(&1)) * x``;

val VECTOR_ADD_ASSOC = VECTOR_ARITH ``(x:real['n]) + (y + z) = x + y + z``;

val VECTOR_SUB_LZERO = VECTOR_ARITH ``VECTOR_0 - x = ~x``;

val VECTOR_NEG_NEG = VECTOR_ARITH ``~(~(x:real['n])) = x``;

val VECTOR_MUL_LNEG = VECTOR_ARITH ``~c * x = ~(c * x)``;

val VECTOR_MUL_RNEG = VECTOR_ARITH ``c * ~x = ~(c * x)``;

val VECTOR_NEG_0 = VECTOR_ARITH ``~(VECTOR_0) = VECTOR_0``;

val VECTOR_ADD_AC = VECTOR_ARITH
  ``(m + n = n + m:real['n]) /\
   ((m + n) + p = m + n + p) /\
   (m + n + p = n + m + p)``;

(* ------------------------------------------------------------------------- *)
(* Properties of the dot product.                                            *)
(* ------------------------------------------------------------------------- *)

val DOT_SYM = VECTOR_ARITH ``!x y. (x dot y) = (y dot x)``;

val DOT_LADD = VECTOR_ARITH ``!x y z. ((x + y) dot z) = (x dot z) + (y dot z)``;

val DOT_RADD = VECTOR_ARITH ``!x y z. (x dot (y + z)) = (x dot y) + (x dot z)``;

val DOT_LSUB = VECTOR_ARITH ``!x y z. ((x - y) dot z) = (x dot z) - (y dot z)``;

val DOT_RSUB = VECTOR_ARITH ``!x y z. (x dot (y - z)) = (x dot y) - (x dot z)``;

val DOT_LMUL = VECTOR_ARITH ``!c x y. ((c * x) dot y) = c * (x dot y)``;

val DOT_RMUL = VECTOR_ARITH ``!c x y. (x dot (c * y)) = c * (x dot y)``;

val DOT_LNEG = VECTOR_ARITH ``!x y. ((~x) dot y) = ~(x dot y)``;

val DOT_RNEG = VECTOR_ARITH ``!x y. (x dot (~y)) = ~(x dot y)``;

val DOT_LZERO = VECTOR_ARITH ``!x. (VECTOR_0 dot x) = &0``;

val DOT_RZERO = VECTOR_ARITH ``!x. (x dot VECTOR_0) = &0``;

(* ------------------------------------------------------------------------- *)
(* Sums of vectors.                                                          *)
(* ------------------------------------------------------------------------- *)

val NEUTRAL_VECTOR_ADD = prove
 (`NEUTRAL(+) = VECTOR_0:real['n]`,
  REWRITE_TAC[NEUTRAL_DEF] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  BETA_TAC THEN REWRITE_TAC[VECTOR_EQ_ADDR,VECTOR_EQ_ADDL]);

val MONOIDAL_VECTOR_ADD = prove
 (`MONOIDAL((+):real['n]->real['n]->real['n])`,
  REWRITE_TAC[MONOIDAL_DEF, NEUTRAL_VECTOR_ADD] THEN
  REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);

val VSUM_DEF = Define
  `(VSUM:('a->bool)->('a->real['n])->real['n]) s f = FCP i. SUM s (\x. f(x) ' i)`;

val VSUM_CLAUSES = prove
 (`(!f. VSUM {} f = VECTOR_0) /\
   (!x f s. FINITE s
            ==> (VSUM (x INSERT s) f =
                 if x IN s then VSUM s f else f(x) + VSUM s f))`,
  SRW_TAC[FCP_ss][VSUM_DEF, VECTOR_ADD_COMPONENT, SUM_CLAUSES, VEC_0_COMPONENT]);

val VSUM = prove
 (`!f s. FINITE s ==> (VSUM s f = ITERATE (+) s f)`,
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, ITERATE_CLAUSES, MONOIDAL_VECTOR_ADD] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD]);

val VSUM_EQ_0 = prove
 (`!f s. (!x:'a. x IN s ==> (f(x) = VECTOR_0)) ==> (VSUM s f = VECTOR_0)`,
  SRW_TAC[FCP_ss][VSUM_DEF, VECTOR_0, SUM_EQ_0]);

val VSUM_0 = prove
 (`VSUM s (\x. VECTOR_0) = VECTOR_0`,
  SIMP_TAC bool_ss[VSUM_EQ_0]);

val VSUM_LMUL = prove
 (`!f c s.  VSUM s (\x. c * f(x)) = c * VSUM s f`,
  SRW_TAC[FCP_ss][VSUM_DEF, VECTOR_MUL_COMPONENT, SUM_LMUL]);

val VSUM_RMUL = prove
 (`!c s v. VSUM s (\x. c x * v) = (SUM s c) * v`,
  SRW_TAC[FCP_ss][VSUM_DEF, VECTOR_MUL_COMPONENT, SUM_RMUL]);

val VSUM_ADD = prove
 (`!f g s. FINITE s ==> (VSUM s (\x. f x + g x) = VSUM s f + VSUM s g)`,
  SRW_TAC[FCP_ss][VSUM_DEF, VECTOR_ADD_COMPONENT, SUM_ADD]);

val VSUM_SUB = prove
 (`!f g s. FINITE s ==> (VSUM s (\x. f x - g x) = VSUM s f - VSUM s g)`,
  SRW_TAC[FCP_ss][VSUM_DEF, VECTOR_SUB_COMPONENT, SUM_SUB]);

val VSUM_COMPONENT = prove
 (`!s f i. i < dimindex(:'n)
           ==> ((VSUM s (f:'a->real['n])) ' i = SUM s (\x. f(x) ' i))`,
  SIMP_TAC bool_ss[VSUM_DEF, FCP_BETA]);
(*20120703*)
val VSUM_IMAGE = prove
 (`!f g s. FINITE s /\ (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (VSUM (IMAGE f s) g = VSUM s (g o f))`,
  SRW_TAC[FCP_ss][VSUM_DEF] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
  ASM_SIMP_TAC bool_ss[o_DEF]);

val VSUM_DELETE = prove
 (`!f s a. FINITE s /\ a IN s
           ==> (VSUM (s DELETE a) f = VSUM s f - f a)`,
  SRW_TAC[FCP_ss][VSUM_DEF, SUM_DELETE, VECTOR_SUB_COMPONENT]);

val VSUM_NEG = prove
 (`!f s. VSUM s (\x. ~f x) = ~VSUM s f`,
  SRW_TAC[FCP_ss][VSUM_DEF, SUM_NEG, VECTOR_NEG_COMPONENT]);
(**)
val VSUM_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (VSUM s f = VSUM s g)`,
  SRW_TAC[FCP_ss][VSUM_DEF] THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC bool_ss[]);
(*20120704*)
(*
20121004
*)
val VSUM_DELETE_CASES = prove
 (`!x f s.
        FINITE(s:'a->bool)
        ==> (VSUM(s DELETE x) f = if x IN s then VSUM s f - f x else VSUM s f)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC bool_ss[prove(`~(x IN s) ==> (s DELETE x = s)`, REWRITE_TAC[DELETE_NON_ELEMENT])] THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites
   [MATCH_MP (prove(`x IN s ==> (s = x INSERT (s DELETE x))`, PROVE_TAC[INSERT_DELETE])) th]) THEN
  ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_DELETE, IN_DELETE] THEN VECTOR_ARITH_TAC);

val VSUM_RESTRICT_SET = prove
 (`!P s f. VSUM {x | x IN s /\ P x} f =
           VSUM s (\x. if P x then f x else VECTOR_0)`,
  SRW_TAC[FCP_ss][VSUM_DEF, VEC_0_COMPONENT, SUM_RESTRICT_SET, COND_COMPONENT]);
(**)
(* ------------------------------------------------------------------------- *)
(* Basis vectors in coordinate directions.                                   *)
(* ------------------------------------------------------------------------- *)

val basis_def = Define
  `basis k = FCP i. if i = k then &1 else &0`;

val BASIS_INJ = prove
 (`!i j. 
	i < dimindex(:'n) /\ j < dimindex(:'n) /\ (basis i :real['n] = basis j)
     ==> (i = j)`,
  SRW_TAC[FCP_ss][basis_def] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``i:num``) THEN
  CONV_TAC CONTRAPOS_CONV THEN ASM_SIMP_TAC bool_ss[REAL_10]);

val BASIS_NE = prove
 (`!i j. 
	i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j)
     ==> ~(basis i :real['n] = basis j)`,
  PROVE_TAC[BASIS_INJ]);

val BASIS_COMPONENT = prove
 (`!k i. i < dimindex(:'n)
         ==> ((basis k :real['n]) ' i = if i = k then &1 else &0)`,
  SRW_TAC[FCP_ss][basis_def]);

val BASIS_EXPANSION = prove
 (`!x:real['n]. VSUM (count(dimindex(:'n))) (\i. x ' i * basis i) = x`,
  SRW_TAC[FCP_ss][VSUM_COMPONENT, VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT, REAL_MUL_RID]);

val BASIS_EXPANSION_UNIQUE = prove
 (`!u x:real['n].
	(VSUM (count(dimindex(:'n))) (\i. f(i) * basis i) = x) <=>
    (!i. i < dimindex(:'n) ==> (f(i) = x ' i))`,
  SRW_TAC[FCP_ss][VSUM_COMPONENT, VECTOR_MUL_COMPONENT, BASIS_COMPONENT] THEN
  REWRITE_TAC[COND_RAND, REAL_MUL_RZERO, REAL_MUL_RID] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o RAND_CONV o LAND_CONV o
                   ONCE_DEPTH_CONV) empty_rewrites[EQ_SYM_EQ] THEN
  SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT]);

val DOT_BASIS = prove
 (`!x:real['n] i.
        i < dimindex(:'n)
        ==> (((basis i) dot x) = x ' i) /\ ((x dot (basis i)) = x ' i)`,
  REWRITE_TAC[dot_def, basis_def] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN 
  EXISTS_TAC `SUM (count (dimindex (:'n))) (\i'. (if i' = i then 1 else 0) * x ' i')` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC,
   MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  REWRITE_TAC[COND_RATOR, COND_RAND, REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT, REAL_MUL_LID]);

val VECTOR_EQ_LDOT = prove
 (`!y z. (!x. (x dot y) = (x dot z)) <=> (y = z)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC bool_ss[] THEN
  REWRITE_TAC[CART_EQ] THEN PROVE_TAC[DOT_BASIS]);

val VECTOR_EQ_RDOT = prove
 (`!x y. (!z. (x dot z) = (y dot z)) <=> (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC bool_ss[] THEN
  REWRITE_TAC[CART_EQ] THEN PROVE_TAC[DOT_BASIS]);

(* ------------------------------------------------------------------------- *)
(* Linear functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val linear_def = Define
  `linear (f:real['m]->real['n]) =
        (!x y. f(x + y) = f(x) + f(y)) /\
        (!c x. f(c * x) = c * f(x))`;

val LINEAR_COMPOSE_CMUL = prove
 (`!f c. linear f ==> linear (\x. c * f(x))`,
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);

val LINEAR_COMPOSE_NEG = prove
 (`!f. linear f ==> linear (\x. ~(f(x)))`,
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);

val LINEAR_COMPOSE_ADD = prove
 (`!f g. linear f /\ linear g ==> linear (\x. f(x) + g(x))`,
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);

val LINEAR_COMPOSE_SUB = prove
 (`!f g. linear f /\ linear g ==> linear (\x. f(x) - g(x))`,
  SIMP_TAC bool_ss[linear_def] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);

val LINEAR_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> linear (g o f)`,
  SIMP_TAC bool_ss[linear_def, o_THM]);

val LINEAR_ID = prove
 (`linear (\x. x)`,
  REWRITE_TAC[linear_def] THEN BETA_TAC THEN REWRITE_TAC[]);

val LINEAR_I = prove
 (`linear I`,
  REWRITE_TAC[I_DEF, K_DEF, S_DEF] THEN BETA_TAC THEN BETA_TAC THEN REWRITE_TAC[LINEAR_ID]);

val LINEAR_ZERO = prove
 (`linear (\x. VECTOR_0)`,
  REWRITE_TAC[linear_def] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);

val LINEAR_NEGATION = prove
 (`linear(~)`,
  REWRITE_TAC[linear_def] THEN VECTOR_ARITH_TAC);

val LINEAR_COMPOSE_VSUM = prove
 (`!f s. FINITE s /\ (!a. a IN s ==> linear(f a))
         ==> linear(\x. VSUM s (\a. f a x))`,
  GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES,LINEAR_ZERO] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  HO_MATCH_MP_TAC LINEAR_COMPOSE_ADD THEN
  REWRITE_TAC [ETA_AX] THEN PROVE_TAC[]);

val LINEAR_VMUL_COMPONENT = prove
 (`!f:real['m]->real['n] v k.
     linear f /\ k < dimindex(:'n)
     ==> linear (\x. f(x) ' k * v)`,
  SIMP_TAC bool_ss[linear_def, VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);

val LINEAR_0 = prove
 (`!f. linear f ==> (f(VECTOR_0) = VECTOR_0)`,
  PROVE_TAC[VECTOR_MUL_LZERO, linear_def]);

val LINEAR_CMUL = prove
 (`!f c x. linear f ==> (f(c * x) = c * f(x))`,
  SIMP_TAC bool_ss[linear_def]);

val LINEAR_NEG = prove
 (`!f x. linear f ==> (f(~x) = ~(f x))`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN SIMP_TAC bool_ss[LINEAR_CMUL]);

val LINEAR_ADD = prove
 (`!f x y. linear f ==> (f(x + y) = f(x) + f(y))`,
  SIMP_TAC bool_ss[linear_def]);

val LINEAR_SUB = prove
 (`!f x y. linear f ==> (f(x - y) = f(x) - f(y))`,
  SIMP_TAC bool_ss[VECTOR_SUB, LINEAR_ADD, LINEAR_NEG]);

val LINEAR_VSUM = prove
 (`!f g s. linear f /\ FINITE s ==> (f(VSUM s g) = VSUM s (f o g))`,
  GEN_TAC THEN GEN_TAC THEN SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES] THEN FIRST_ASSUM(fn th =>
    SIMP_TAC bool_ss[MATCH_MP LINEAR_0 th, MATCH_MP LINEAR_ADD th, o_THM]));

val LINEAR_VSUM_MUL = prove
 (`!f s c v.
        linear f /\ FINITE s
        ==> (f(VSUM s (\i. c i * v i)) = VSUM s (\i. c(i) * f(v i)))`,
  SIMP_TAC bool_ss[LINEAR_VSUM, o_DEF, LINEAR_CMUL]);

val LINEAR_INJECTIVE_0 = prove
 (`!f. linear f
       ==> ((!x y. (f(x) = f(y)) ==> (x = y)) <=>
            (!x. (f(x) = VECTOR_0) ==> (x = VECTOR_0)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC bool_ss[GSYM LINEAR_SUB] THEN PROVE_TAC[VECTOR_SUB_RZERO]);

val SYMMETRIC_LINEAR_IMAGE = prove
 (`!f s. (!x. x IN s ==> ~x IN s) /\ linear f
          ==> !x. x IN (IMAGE f s) ==> ~x IN (IMAGE f s)`,
  SIMP_TAC bool_ss[FORALL_IN_IMAGE, GSYM LINEAR_NEG] THEN
  PROVE_TAC[IN_IMAGE]);

(* ------------------------------------------------------------------------- *)
(* Bilinear functions.                                                       *)
(* ------------------------------------------------------------------------- *)

val bilinear_def = Define
  `bilinear f = (!x. linear(\y. f x y)) /\ (!y. linear(\x. f x y))`;

(* ------------------------------------------------------------------------- *)
(* Adjoints.                                                                 *)
(* ------------------------------------------------------------------------- *)

val ADJOINT_DEF = Define
 `ADJOINT(f:real['m]->real['n]) = @f'. !x y. (f(x) dot y) = (x dot f'(y))`;

val ADJOINT_WORKS = prove
 (`!f:real['m]->real['n]. linear f ==> !x y. (f(x) dot y) = (x dot (ADJOINT f)(y))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ADJOINT_DEF] THEN CONV_TAC SELECT_CONV THEN
  SIMP_TAC bool_ss[Once SWAP_FORALL_THM, Once (GSYM SKOLEM_THM)] THEN
  GEN_TAC THEN
  EXISTS_TAC `(FCP i. (f:real['m]->real['n]) (basis i) dot y):real['m]` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV) empty_rewrites[GSYM BASIS_EXPANSION] THEN
  ASM_SIMP_TAC bool_ss[LINEAR_VSUM, FINITE_COUNT] THEN
  REWRITE_TAC[dot_def] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC 
	`SUM (count (dimindex (:'n)))
		(\i. SUM (count (dimindex (:'m))) (\i'.f (x ' i' * basis i') ' i *  y ' i))` THEN
  CONJ_TAC THENL[
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][VSUM_COMPONENT, GSYM SUM_RMUL], ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
	`SUM (count (dimindex (:'m)))
		(\i. x ' i * SUM (count (dimindex (:'n))) (\i'. f (basis i) ' i' * y ' i'))` THEN
  CONJ_TAC THENL[
	REWRITE_TAC[GSYM SUM_LMUL] THEN SIMP_TAC bool_ss[Once SUM_SWAP_COUNT] THEN
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[][] THEN MATCH_MP_TAC SUM_EQ THEN
	SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT, LINEAR_CMUL, REAL_MUL_ASSOC], ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]);

val ADJOINT_LINEAR = prove
 (`!f:real['m]->real['n]. linear f ==> linear(ADJOINT f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[linear_def, GSYM VECTOR_EQ_LDOT] THEN
  ASM_SIMP_TAC bool_ss[DOT_RMUL, DOT_RADD, GSYM ADJOINT_WORKS]);

val ADJOINT_CLAUSES = prove
 (`!f:real['m]->real['n].
     linear f ==> (!x y. (x dot (ADJOINT f)(y)) = (f(x) dot y)) /\
                  (!x y. ((ADJOINT f)(y) dot x) = (y dot f(x)))`,
  PROVE_TAC[ADJOINT_WORKS, DOT_SYM]);

val ADJOINT_ADJOINT = prove
 (`!f:real['m]->real['n]. linear f ==> (ADJOINT(ADJOINT f) = f)`,
  SIMP_TAC bool_ss[FUN_EQ_THM, GSYM VECTOR_EQ_LDOT, ADJOINT_CLAUSES, ADJOINT_LINEAR]);

val ADJOINT_UNIQUE = prove
 (`!f f'. linear f /\ (!x y. (f'(x) dot y) = (x dot f(y)))
          ==> (f' = ADJOINT f)`,
  SIMP_TAC bool_ss[FUN_EQ_THM, GSYM VECTOR_EQ_RDOT, ADJOINT_CLAUSES]);

(* ------------------------------------------------------------------------- *)
(* Matrix notation. NB: an MxN matrix is of type real^N^M, not real^M^N.     *)
(* We could define a special type if we're going to use them a lot.          *)
(* ------------------------------------------------------------------------- *)

val matrix_cmul_def = Define
  `matrix_cmul:real->real['n]['m]->real['n]['m] c A = FCP i j. c * A ' i ' j`;

val matrix_neg_def = Define
  `matrix_neg:real['n]['m]->real['n]['m] A = FCP i j. -(A ' i ' j)`;

val matrix_add_def = Define
  `matrix_add:real['n]['m]->real['n]['m]->real['n]['m] A B = FCP i j. A ' i ' j + B ' i ' j`;

val matrix_sub_def = Define
  `matrix_sub:real['n]['m]->real['n]['m]->real['n]['m] A B = FCP i j. A ' i ' j - B ' i ' j`;

val matrix_mul_def = Define
  `matrix_mul:real['p]['m]->real['n]['p]->real['n]['m] A B =
          FCP i j. SUM (count(dimindex(:'p))) (\k. A ' i ' k * B ' k ' j)`;

val matrix_vector_mul_def = Define
  `matrix_vector_mul:real['n]['m]->real['n]->real['m] A x = 
			FCP i. SUM (count(dimindex(:'n))) (\j. A ' i ' j * x ' j)`;

val vector_matrix_mul_def = Define
  `vector_matrix_mul:real['m]->real['n]['m]->real['n] x A = 
			FCP j. SUM (count(dimindex(:'m))) (\i. A ' i ' j * x ' i)`;

val _ = overload_on ("~", ``matrix_neg:real['n]['m]->real['n]['m]``);
val _ = overload_on ("+", ``matrix_add:real['n]['m]->real['n]['m]->real['n]['m]``);
val _ = overload_on ("-", ``matrix_sub:real['n]['m]->real['n]['m]->real['n]['m]``);
val _ = overload_on ("**",``matrix_mul:real['p]['m]->real['n]['p]->real['n]['m]``);
val _ = overload_on ("**",``matrix_vector_mul:real['n]['m]->real['n]->real['m]``);
val _ = overload_on ("**",``vector_matrix_mul:real['m]->real['n]['m]->real['n]``);
val _ = overload_on ("*", ``matrix_cmul:real->real['n]['m]->real['n]['m]``);

val ROW_DEF = Define
  `ROW i (A:real['a]['b]) = (FCP j. A ' i ' j ): real['a]`;

val COLUMN_DEF = Define
  `COLUMN j (A:real['a]['b]) = (FCP i. A ' i ' j):real['b]`;

val TRANSP_DEF = Define
  `TRANSP (A:real['a]['b]) = (FCP i j. (A ' j ' i)):real['b]['a]`;

val MAT_DEF = Define
  `(MAT:num -> real['a]['b]) k = FCP i j. if i = j then &k else &0`;

val ROWS_DEF = Define
 `ROWS(A:real['n]['m]) = { ROW i A | i < dimindex(:'m)}`;

val COLUMNS_DEF = Define
 `COLUMNS(A:real['n]['m]) = { COLUMN i A | i < dimindex(:'n)}`;
(**)
val ROW_FCP = store_thm("ROW_FCP",
    `k < dimindex(:'m) ==>
      (ROW k ((FCP i j. f i j):real['n]['m]) = FCP j. f k j)`,
    SRW_TAC [fcpLib.FCP_ss][ROW_DEF]);

val COLUMN_FCP = store_thm("COLUMN_FCP",
    `k < dimindex (:'n) ==>
       (COLUMN k ((FCP i j. f i j):real['n]['m]) = FCP i. f i k)`,
    SRW_TAC [fcpLib.FCP_ss][COLUMN_DEF]);  
(**) 
val MATRIX_CMUL_COMPONENT = prove
 (`!c A:real['n]['m] i j. i < dimindex(:'m) /\ j < dimindex(:'n) ==> ((c * A) ' i ' j = c * A ' i ' j)`,
  SRW_TAC[FCP_ss][matrix_cmul_def]);

val MATRIX_ADD_COMPONENT = prove
 (`!A B:real['n]['m] i j. i < dimindex(:'m) /\ j < dimindex(:'n) ==> ((A + B) ' i ' j = A ' i ' j + B ' i ' j)`,
  SRW_TAC[FCP_ss][matrix_add_def]);

val MATRIX_SUB_COMPONENT = prove
 (`!A B:real['n]['m] i j. i < dimindex(:'m) /\ j < dimindex(:'n) ==> ((A - B) ' i ' j = A ' i ' j - B ' i ' j)`,
  SRW_TAC[FCP_ss][matrix_sub_def]);

val MATRIX_NEG_COMPONENT = prove
 (`!A:real['n]['m] i j. i < dimindex(:'m) /\ j < dimindex(:'n) ==> ((~A) ' i ' j = -A ' i ' j)`,
  SRW_TAC[FCP_ss][matrix_neg_def]);

val MAT_COMPONENT = prove
 (`!n i j.
        i < dimindex(:'m) /\ j < dimindex(:'n)
        ==> ((MAT n:real['n]['m]) ' i ' j = if i = j then &n else &0)`,
  SRW_TAC[FCP_ss][MAT_DEF]);

val MATRIX_CMUL_ASSOC = prove
 (`!a b X:real['n]['m]. a * (b * X) = (a * b) * X`,
  SRW_TAC[FCP_ss][matrix_cmul_def, REAL_MUL_ASSOC]);

val MATRIX_CMUL_LID = prove
 (`!X:real['n]['m]. &1 * X = X`,
  SRW_TAC[FCP_ss][matrix_cmul_def, REAL_MUL_LID]);

val MATRIX_ADD_SYM = prove
 (`!A:real['n]['m] B. A + B = B + A`,
  SRW_TAC[FCP_ss][matrix_add_def, REAL_ADD_SYM]);

val MATRIX_ADD_ASSOC = prove
 (`!A:real['n]['m] B C. A + (B + C) = (A + B) + C`,
  SRW_TAC[FCP_ss][matrix_add_def, REAL_ADD_ASSOC]);

val MATRIX_ADD_LID = prove
 (`!A. MAT 0 + A = A`,
  SRW_TAC[FCP_ss][matrix_add_def, MAT_DEF, COND_ID, REAL_ADD_LID]);

val MATRIX_ADD_RID = prove
 (`!A. A + MAT 0 = A`,
  SRW_TAC[FCP_ss][matrix_add_def, MAT_DEF, COND_ID, REAL_ADD_LID]);

val MATRIX_ADD_LNEG = prove
 (`!A. ~A + A = MAT 0`,
  SRW_TAC[FCP_ss][matrix_neg_def, matrix_add_def, MAT_DEF, COND_ID, REAL_ADD_LINV]);

val MATRIX_ADD_RNEG = prove
 (`!A. A + ~A = MAT 0`,
  SRW_TAC[FCP_ss][matrix_neg_def, matrix_add_def, MAT_DEF, COND_ID, REAL_ADD_RINV]);

val MATRIX_SUB = prove
 (`!A:real['n]['m] B. A - B = A + ~B`,
  SRW_TAC[FCP_ss][matrix_neg_def, matrix_add_def, matrix_sub_def, real_sub]);

val MATRIX_SUB_REFL = prove
 (`!A. A - A = MAT 0`,
  REWRITE_TAC[MATRIX_SUB, MATRIX_ADD_RNEG]);

val MATRIX_ADD_LDISTRIB = prove
 (`!A:real['p]['m] B:real['n]['p] C. A ** (B + C) = A ** B + A ** C`,
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_add_def, GSYM SUM_ADD_COUNT] THEN
  MATCH_MP_TAC SUM_EQ_COUNT THEN
  SRW_TAC[FCP_ss][REAL_ADD_LDISTRIB]);
(**)
val VECTOR_DOT_FCP2 = store_thm("VECTOR_DOT_FCP",
    `((($FCP f :real ** 'n) dot v) =
           SUM (count (dimindex(:'n))) (\i. f i * (v ' i))) /\
      ((u dot ($FCP f :real ** 'n)) =
           SUM (count (dimindex(:'n))) (\i. (u ' i) * f i))`,
      SRW_TAC [fcpLib.FCP_ss] [dot_def, SUM_EQ]);	  

val MATRIX_MUL_EQ = prove
 (`!A:real['p]['m] B:real['n]['p] k:real. (FCP i j. SUM 	(count(dimindex(:'p))) (\k. A ' i ' k * B ' k ' j)) =
	(FCP i j. (ROW i A) dot (COLUMN j B)): real['n]['m]`,
	SRW_TAC[FCP_ss][dot_def, ROW_DEF, COLUMN_DEF] THEN
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]
);  	  
	  
val MATRIX_MUL_ASSOC = store_thm ("MATRIX_MUL_ASSOC", 
    `!(A:real['n]['m]) (B:real['p]['n]) (C:real['q]['p]). 
      (A ** B) ** C = A ** (B ** C)`,
    SRW_TAC [fcpLib.FCP_ss][matrix_mul_def, MATRIX_MUL_EQ, ROW_FCP, COLUMN_FCP, VECTOR_DOT_FCP2] THEN
    SRW_TAC [][dot_def, GSYM SUM_LMUL, GSYM SUM_RMUL] THEN
    SRW_TAC [][Once SUM_SWAP_COUNT] THEN
    MATCH_MP_TAC SUM_EQ THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC SUM_EQ THEN
    SRW_TAC [][] THEN
    SRW_TAC [fcpLib.FCP_ss][ROW_DEF, COLUMN_DEF] THEN
    REAL_ARITH_TAC);  
(**)
val MATRIX_MUL_LMUL = prove
 (`!A:real['n]['m] B:real['p]['n] c. (c * A) ** B = c * (A ** B)`,
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def, MATRIX_CMUL_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN 
  EXISTS_TAC
  `SUM (count (dimindex (:'n))) (\k. c * (A ' i ' k * B ' k ' i'))` THEN CONJ_TAC THENL[
    MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][MATRIX_CMUL_COMPONENT, REAL_MUL_ASSOC], ALL_TAC] THEN
  SIMP_TAC bool_ss[SUM_LMUL]);
 
val MATRIX_MUL_RMUL = prove
 (`!A:real['n]['m] B:real['p]['n] c. A ** (c * B) = c * (A ** B)`,
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def, MATRIX_CMUL_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN 
  EXISTS_TAC
  `SUM (count (dimindex (:'n))) (\k. c * (A ' i ' k * B ' k ' i'))` THEN CONJ_TAC THENL[
    MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][MATRIX_CMUL_COMPONENT] THEN REAL_ARITH_TAC, ALL_TAC] THEN
  SIMP_TAC bool_ss[SUM_LMUL]);

(**)
val MATRIX_VECTOR_MUL_ASSOC = prove
 (`!A:real['n]['m] B:real['p]['n] x:real['p]. A ** B ** x = (A ** B) ** x`,
  REPEAT GEN_TAC THEN
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC 
  `SUM (count (dimindex (:'n)))
   (\j.
      A ' i ' j *
        SUM (count (dimindex (:'p))) (\k. B ' j ' k * x ' k))`
  THEN CONJ_TAC	THENL[MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN	
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
  `SUM (count (dimindex (:'p)))
   (\j. SUM (count (dimindex (:'n))) (\k. A ' i ' k * B ' k ' j) * x ' j)`
  THEN CONJ_TAC THENL[
	REWRITE_TAC[GSYM SUM_LMUL, GSYM SUM_RMUL] THEN BETA_TAC THEN
	REWRITE_TAC[REAL_MUL_ASSOC] THEN SIMP_TAC bool_ss[Once SUM_SWAP_COUNT],
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]]);

val MATRIX_VECTOR_MUL_LID = prove
 (`!x:real['n]. MAT 1 ** x = x`,
  REWRITE_TAC[matrix_vector_mul_def,
   GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[EQ_SYM_EQ]
    (SPEC_ALL MAT_DEF)] THEN
  SRW_TAC[FCP_ss][] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM (count (dimindex (:'n)))(\j. (if j = i then 1 else 0) * x ' j)` THEN
  CONJ_TAC THENL[MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  REWRITE_TAC[COND_RATOR, COND_RAND] THEN
  ASM_SIMP_TAC bool_ss[SUM_DELTA, REAL_MUL_LZERO, IN_COUNT, REAL_MUL_LID]);

val MATRIX_VECTOR_MUL_LZERO = prove
 (`!x:real['n]. MAT 0 ** x = VECTOR_0`,
  SRW_TAC[FCP_ss][MAT_DEF, matrix_vector_mul_def, VEC_0_COMPONENT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM (count (dimindex (:'n)))(\j. 0 * x ' j)` THEN
  CONJ_TAC THENL[MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LZERO, SUM_0]);

val MATRIX_VECTOR_MUL_RZERO = prove
 (`!A:real['m]['n]. A ** VECTOR_0 = VECTOR_0`,
  SRW_TAC[FCP_ss][matrix_vector_mul_def, VEC_0_COMPONENT] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM (count (dimindex (:'m)))(\j. 0)` THEN CONJ_TAC THENL[
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][VEC_0_COMPONENT], REWRITE_TAC[SUM_0]]);

val MATRIX_TRANSP_MUL = prove
 (`!A B. TRANSP(A ** B) = TRANSP(B) ** TRANSP(A)`,
  SRW_TAC[FCP_ss][matrix_mul_def, TRANSP_DEF] THEN MATCH_MP_TAC SUM_EQ THEN
  SRW_TAC[FCP_ss][REAL_MUL_SYM]);  

val MATRIX_EQ = prove
 (`!A:real['n]['m] B. (A = B) = !x:real['n]. A ** x = B ** x`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN ``i:num`` o SPEC ``(basis i):real['n]``) THEN
  SIMP_TAC bool_ss[CART_EQ, matrix_vector_mul_def, FCP_BETA, basis_def] THEN
  SUBGOAL_THEN `!i i'.
   (SUM (count (dimindex (:'n)))
   (\j. A:real['n]['m] ' i' ' j * (FCP i'. if i' = i then 1 else 0):real['n] ' j) =  
	SUM (count (dimindex (:'n)))
   (\j. A ' i' ' j * if j = i then 1 else 0))` ASSUME_TAC THENL[
		REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  SUBGOAL_THEN `!i i'.
   (SUM (count (dimindex (:'n)))
   (\j. B:real['n]['m] ' i' ' j * (FCP i'. if i' = i then 1 else 0):real['n] ' j) =  
	SUM (count (dimindex (:'n)))
   (\j. B ' i' ' j * if j = i then 1 else 0))` ASSUME_TAC THENL[
		REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC bool_ss[SUM_DELTA, COND_RAND, REAL_MUL_RZERO, REAL_MUL_RID, IN_COUNT]);
(**)
val TRANSP_MAT = prove
 (`!n. TRANSP(MAT n) = MAT n`,
  SRW_TAC[FCP_ss][TRANSP_DEF, MAT_DEF, EQ_SYM_EQ]);
(**)
val TRANSP_TRANSP = prove
 (`!A:real['n]['m]. TRANSP(TRANSP A) = A`,
  SRW_TAC[FCP_ss][TRANSP_DEF]);

val TRANSP_EQ = prove
 (`!A B:real['m]['n]. (TRANSP A = TRANSP B) <=> (A = B)`,
  PROVE_TAC[TRANSP_TRANSP]);

val ROW_TRANSP = prove
 (`!A:real['n]['m] i.
        i < dimindex(:'n) ==> (ROW i (TRANSP A) = COLUMN i A)`,
  SRW_TAC[FCP_ss][ROW_DEF, COLUMN_DEF, TRANSP_DEF]);

val COLUMN_TRANSP = prove
 (`!A:real['n]['m] i.
        i < dimindex(:'m) ==> (COLUMN i (TRANSP A) = ROW i A)`,
  SRW_TAC[FCP_ss][ROW_DEF, COLUMN_DEF, TRANSP_DEF]);

val ROWS_TRANSP = prove
 (`!A:real['n]['m]. ROWS(TRANSP A) = COLUMNS A`,
  REWRITE_TAC[ROWS_DEF, COLUMNS_DEF, EXTENSION] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[ROW_TRANSP]);

val COLUMNS_TRANSP = prove
 (`!A:real['n]['m]. COLUMNS(TRANSP A) = ROWS A`,
  PROVE_TAC[TRANSP_TRANSP, ROWS_TRANSP]);

val VECTOR_MATRIX_MUL_TRANSP = prove
 (`!A:real['m]['n] x:real['n]. x ** A = TRANSP A ** x`,
  REWRITE_TAC[matrix_vector_mul_def, vector_matrix_mul_def, TRANSP_DEF] THEN
  SRW_TAC[FCP_ss][] THEN MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN SRW_TAC[FCP_ss][]);

val MATRIX_VECTOR_MUL_TRANSP = prove
 (`!A:real['m]['n] x:real['m]. A ** x = x ** TRANSP A`,
  REWRITE_TAC[VECTOR_MATRIX_MUL_TRANSP, TRANSP_TRANSP]);
(**)
val MATRIX_MUL_LID = prove
 (`!A:real['n]['m]. MAT 1 ** A = A`,
	REPEAT GEN_TAC THEN SRW_TAC [FCP_ss][matrix_mul_def, MAT_DEF] 
	THEN MATCH_MP_TAC EQ_TRANS
	THEN EXISTS_TAC `SUM (count (dimindex (:'m)))(\k. if k = i then A ' k ' i' else 0)`
	THEN CONJ_TAC THENL
	[MATCH_MP_TAC SUM_EQ THEN SRW_TAC [][] THEN SRW_TAC [FCP_ss][],
	ASM_SIMP_TAC bool_ss[SUM_DELTA, IN_COUNT]]);
  
val MATRIX_MUL_RID = prove
 (`!A:real['n]['m]. A ** MAT 1 = A`,
	REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [GSYM TRANSP_EQ]
	THEN ONCE_REWRITE_TAC[MATRIX_TRANSP_MUL]
	THEN REWRITE_TAC[TRANSP_MAT]
	THEN MATCH_ACCEPT_TAC MATRIX_MUL_LID);
 
(* ------------------------------------------------------------------------- *)
(* Two sometimes fruitful ways of looking at matrix-vector multiplication.   *)
(* ------------------------------------------------------------------------- *)

val MATRIX_MUL_DOT = prove
 (`!A:real['n]['m] x. A ** x = FCP i. A ' i dot x`,
  REWRITE_TAC[matrix_vector_mul_def, dot_def] THEN SRW_TAC[FCP_ss][]);

val MATRIX_MUL_VSUM = prove
 (`!A:real['n]['m] x. A ** x = VSUM(count(dimindex(:'n))) (\i. x ' i * COLUMN i A)`,
  SRW_TAC[FCP_ss][matrix_vector_mul_def, VSUM_COMPONENT, VECTOR_MUL_COMPONENT,
				  COLUMN_DEF, REAL_MUL_SYM]);
(* ------------------------------------------------------------------------- *)
(* Slightly gruesome lemmas: better to define sums over vectors really...    *)
(* ------------------------------------------------------------------------- *)

val VECTOR_COMPONENTWISE = prove
 (`!x:real['n].
    x = FCP j. SUM(count(dimindex(:'n)))
                     (\i. x ' i * (basis i :real['n]) ' j)`,
  SRW_TAC[FCP_ss][basis_def] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[EQ_SYM_EQ] THEN
  ASM_SIMP_TAC bool_ss[COND_RAND, REAL_MUL_RZERO, SUM_DELTA, IN_COUNT] THEN
  REWRITE_TAC[REAL_MUL_RID]);

val LINEAR_COMPONENTWISE = prove
 (`!f:real['m]->real['n].
      linear(f)
      ==> !x j. j < dimindex(:'n)
                ==> (f x ' j =
                     SUM(count(dimindex(:'m))) (\i. x ' i * f(basis i) ' j))`,
  REWRITE_TAC[linear_def] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) empty_rewrites
   [VECTOR_COMPONENTWISE] THEN
  SPEC_TAC(`dimindex(:'m)`,`n:num`) THEN
  INDUCT_TAC THEN
  SIMP_TAC bool_ss[COUNT_ZERO, COUNT_SUC, FINITE_COUNT, IN_COUNT, SUM_CLAUSES, LT_REFL] THENL
   [REWRITE_TAC[GSYM VECTOR_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) empty_rewrites
     [GSYM VECTOR_MUL_LZERO] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC bool_ss[VEC_0_COMPONENT],
    ASSUM_LIST(fn thl => REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC bool_ss[GSYM VECTOR_MUL_COMPONENT,
             ASSUME ``j < dimindex(:'n)``] THEN
    ASSUM_LIST(fn thl => REWRITE_TAC(map GSYM thl)) THEN
    SIMP_TAC bool_ss[GSYM VECTOR_ADD_COMPONENT,
             ASSUME ``j < dimindex(:'n)``] THEN
    ASSUM_LIST(fn thl => REWRITE_TAC(map GSYM thl)) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SRW_TAC [FCP_ss][VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT]]);

(* ------------------------------------------------------------------------- *)
(* Inverse matrices (not necessarily square, but it's vacuous otherwise).    *)
(* ------------------------------------------------------------------------- *)

val invertible_def = Define
  `invertible(A:real['n]['m]) =
        ?A':real['m]['n]. (A ** A' = MAT 1) /\ (A' ** A = MAT 1)`;

val MATRIX_INV_DEF = Define
  `MATRIX_INV(A:real['n]['m]) =
        @A':real['m]['n]. (A ** A' = MAT 1) /\ (A' ** A = MAT 1)`;

val MATRIX_INV = prove
 (`!A:real['n]['m].
    invertible A ==> (A ** MATRIX_INV A = MAT 1) /\ (MATRIX_INV A ** A = MAT 1)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MATRIX_INV_DEF, invertible_def] THEN
  CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[GSYM invertible_def]);

val INVERTIBLE_MATRIX_INV = prove
 (`!A:real['n]['n]. invertible A ==> invertible(MATRIX_INV A)`,
 METIS_TAC[MATRIX_INV, invertible_def]); 

(**)
val MATRIX_RMUL_EQ = prove
 (`!A:real['n]['m] (X Y):real['m]['p]. invertible A ==> ((X = Y) = (X ** A = Y ** A))`,
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]);

val MATRIX_LMUL_EQ = prove
 (`!A:real['n]['m] (X Y):real['p]['n]. invertible A ==> ((X = Y) = (A ** X = A ** Y))`,
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]);  
(**)
(**)
val MATRIX_RMUL_INV_EQ = prove
 (`!A:real['n]['m] (X Y):real['n]['p]. invertible A ==> ((X = Y) = (X ** MATRIX_INV A = Y ** MATRIX_INV A))`,
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]);

val MATRIX_LMUL_INV_EQ = prove
  (`!A:real['n]['m] (X Y):real['p]['m]. invertible A ==> ((X = Y) = (MATRIX_INV A ** X = MATRIX_INV A ** Y))`,
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]);  

val MATRIX_EQ_RMUL = prove
 (`!(A B C):real['n]['n]. invertible C /\ (A ** C = B ** C) ==> (A = B)`,
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_RID, MATRIX_MUL_ASSOC]);

val MATRIX_EQ_LMUL = prove
 (`!(A B C):real['n]['n]. invertible C /\ (C ** A  = C ** B)==> (A = B)`,
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, MATRIX_MUL_LID, MATRIX_MUL_ASSOC]);  
(**)
val MATRIX_INV_INV = prove
 (`!(A B):real['n]['n]. invertible A ==>(MATRIX_INV(MATRIX_INV A) = A)`,
  REPEAT STRIP_TAC THEN
  METIS_TAC[MATRIX_INV, INVERTIBLE_MATRIX_INV, MATRIX_RMUL_INV_EQ]); 
 
(* ------------------------------------------------------------------------- *)
(* Correspondence between matrices and linear operators.                     *)
(* ------------------------------------------------------------------------- *)

val matrix_def = Define
  `(matrix:(real['m]->real['n])->real['m]['n]) f = FCP i j. f(basis j) ' i`;

val MATRIX_VECTOR_MUL_LINEAR = prove
 (`!A:real['n]['m]. linear(\x. A ** x)`,
  REWRITE_TAC[linear_def, matrix_vector_mul_def] THEN
  SRW_TAC[FCP_ss][VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM SUM_ADD_COUNT, GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN BETA_TAC THEN
  SRW_TAC[FCP_ss][VECTOR_ADD_COMPONENT, VECTOR_MUL_COMPONENT, IN_COUNT] THEN REAL_ARITH_TAC);

val MATRIX_WORKS = prove
 (`!f:real['m]->real['n]. linear f ==> !x. matrix f ** x = f(x)`,
  REWRITE_TAC[matrix_def, matrix_vector_mul_def] THEN
  SRW_TAC[FCP_ss][] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC EQ_TRANS THEN 
  EXISTS_TAC `SUM (count (dimindex (:'m))) (\j. x ' j * f (basis j) ' i)` THEN
  CONJ_TAC THENL[MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], 
  ASM_SIMP_TAC bool_ss[GSYM LINEAR_COMPONENTWISE]]);

val MATRIX_VECTOR_MUL = prove
 (`!f:real['m]->real['n]. linear f ==> (f = \x. matrix f ** x)`,
  SIMP_TAC bool_ss[FUN_EQ_THM, MATRIX_WORKS]);

val MATRIX_OF_MATRIX_VECTOR_MUL = prove
 (`!A:real['n]['m]. matrix(\x. A ** x) = A`,
  SIMP_TAC bool_ss[MATRIX_EQ, MATRIX_VECTOR_MUL_LINEAR, MATRIX_WORKS]);

val MATRIX_COMPOSE = prove
 (`!f g. linear f /\ linear g ==> (matrix(g o f) = matrix g ** matrix f)`,
  SIMP_TAC bool_ss[MATRIX_EQ, MATRIX_WORKS, LINEAR_COMPOSE,
           GSYM MATRIX_VECTOR_MUL_ASSOC, o_THM]);

val MATRIX_VECTOR_COLUMN = prove
 (`!A:real['n]['m] x.
        A ** x = VSUM(count(dimindex(:'n))) (\i. x ' i * (TRANSP A) ' i)`,
  REWRITE_TAC[matrix_vector_mul_def, TRANSP_DEF] THEN
  SRW_TAC[FCP_ss][VSUM_COMPONENT, VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][REAL_MUL_COMM]);

val MATRIX_MUL_COMPONENT = prove
 (`!i. i < dimindex(:'n)
       ==> (((A:real['n]['n]) ** (B:real['n]['n])) ' i = TRANSP B ** A ' i)`,
  SRW_TAC[FCP_ss][matrix_mul_def, matrix_vector_mul_def, vector_matrix_mul_def,TRANSP_DEF] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][REAL_MUL_COMM]);
 
val ADJOINT_MATRIX = prove
 (`!A:real['n]['m]. ADJOINT(\x. A ** x) = (\x. TRANSP A ** x)`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC ADJOINT_UNIQUE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN REPEAT GEN_TAC THEN
  SIMP_TAC bool_ss[TRANSP_DEF, dot_def, matrix_vector_mul_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN 
  EXISTS_TAC 
  `SUM (count (dimindex (:'n)))(\i. SUM (count (dimindex (:'m)))(\j. A ' j ' i * x ' j) * y ' i)` THEN
  CONJ_TAC THENL[
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][] THEN DISJ2_TAC THEN
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][], 
	ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN 
  EXISTS_TAC	
  `SUM (count (dimindex (:'m)))(\i. x ' i * SUM (count (dimindex (:'n))) (\j. A ' i ' j * y ' j))` THEN
  CONJ_TAC THENL[
	REWRITE_TAC[GSYM SUM_LMUL, GSYM SUM_RMUL] THEN SIMP_TAC bool_ss[Once SUM_SWAP_COUNT] THEN
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][] THEN
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][] THEN REAL_ARITH_TAC, 
	ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][]);

val MATRIX_ADJOINT = prove
 (`!f. linear f ==> (matrix(ADJOINT f) = TRANSP(matrix f))`,
  GEN_TAC THEN DISCH_THEN
   (fn th => GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV) empty_rewrites
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
  REWRITE_TAC[ADJOINT_MATRIX, MATRIX_OF_MATRIX_VECTOR_MUL]);

val MATRIX_ID = prove
 (`matrix(\x. x) = MAT 1`,
  SIMP_TAC bool_ss[MATRIX_EQ, LINEAR_ID, MATRIX_WORKS, MATRIX_VECTOR_MUL_LID]);

val MATRIX_I = prove
 (`matrix I = MAT 1`,
  SIMP_TAC bool_ss[I_DEF, S_DEF, K_DEF, MATRIX_ID]);

val LINEAR_EQ_MATRIX = prove
 (`!f g. linear f /\ linear g /\ (matrix f = matrix g) ==> (f = g)`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MATRIX_VECTOR_MUL)) THEN
  ASM_REWRITE_TAC[]);

val MATRIX_SELF_ADJOINT = prove
 (`!f. linear f ==> ((ADJOINT f = f) <=> (TRANSP(matrix f) = matrix f))`,
  SIMP_TAC bool_ss[GSYM MATRIX_ADJOINT] THEN
  PROVE_TAC[LINEAR_EQ_MATRIX, ADJOINT_LINEAR]);

(* ------------------------------------------------------------------------- *)
(* A bit of linear algebra.                                                  *)
(* ------------------------------------------------------------------------- *)

val subspace_def = Define
 `subspace s =
       (VECTOR_0 IN s /\
        (!x y. x IN s /\ y IN s ==> (x + y) IN s) /\
        (!c x. x IN s ==> (c * x) IN s))`;
(*FROM OTHER LIBRARY*)
val hull_def = Define
  `hull P s = BIGINTER {t | P t /\ s SUBSET t}`;

set_fixity "hull" (Infixl 21);

val HULL_P = prove
 (`!P s. P s ==> ((P hull s) = s)`,
  REWRITE_TAC[hull_def, EXTENSION, IN_BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[SUBSET_DEF]);

val P_HULL = prove
 (`!P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f)) ==> P(P hull s)`,
  REWRITE_TAC[hull_def, BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN SIMP_TAC bool_ss[SPECIFICATION]);

val HULL_EQ = prove
 (`!P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f))
         ==> (((P hull s) = s) <=> P s)`,
  PROVE_TAC[P_HULL, HULL_P]);

val HULL_HULL = prove
 (`!P s. (P hull (P hull s)) = (P hull s)`,
  REWRITE_TAC[hull_def, EXTENSION, IN_BIGINTER, SUBSET_DEF] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]);

val HULL_SUBSET = prove
 (`!P s. s SUBSET (P hull s)`,
  REWRITE_TAC[hull_def, SUBSET_DEF, IN_BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]);

val HULL_MONO = prove
 (`!P s t. s SUBSET t ==> (P hull s) SUBSET (P hull t)`,
  REWRITE_TAC[hull_def, SUBSET_DEF, IN_BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]);

val HULL_ANTIMONO = prove
 (`!P Q s. P SUBSET Q ==> (Q hull s) SUBSET (P hull s)`,
  REWRITE_TAC[SUBSET_DEF, hull_def, IN_BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[IN_DEF]);

val HULL_MINIMAL = prove
 (`!P s t. s SUBSET t /\ P t ==> (P hull s) SUBSET t`,
  REWRITE_TAC[hull_def, SUBSET_DEF, IN_BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]);

val SUBSET_HULL = prove
 (`!P s t. P t ==> ((P hull s) SUBSET t <=> s SUBSET t)`,
  REWRITE_TAC[hull_def, SUBSET_DEF, IN_BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]);

val HULL_UNIQUE = prove
 (`!P s t. s SUBSET t /\ P t /\ (!t'. s SUBSET t' /\ P t' ==> t SUBSET t')
           ==> ((P hull s) = t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[hull_def, SUBSET_DEF, IN_BIGINTER] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[SUBSET_HULL, SUBSET_DEF]);

val HULL_UNION_SUBSET = prove
 (`!P s t. (P hull s) UNION (P hull t) SUBSET (P hull (s UNION t))`,
  SIMP_TAC bool_ss[UNION_SUBSET, HULL_MONO, SUBSET_UNION]);

val HULL_UNION = prove
 (`!P s t. (P hull (s UNION t)) = (P hull ((P hull s) UNION (P hull t)))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull_def] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION, UNION_SUBSET] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[SUBSET_HULL]);

val HULL_UNION_LEFT = prove
 (`!P s t.
        (P hull (s UNION t)) = (P hull ((P hull s) UNION t))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull_def] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION, UNION_SUBSET] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[SUBSET_HULL]);

val HULL_UNION_RIGHT = prove
 (`!P s t.
        (P hull (s UNION t)) = (P hull (s UNION (P hull t)))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[hull_def] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION, UNION_SUBSET] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[SUBSET_HULL]);

val HULL_REDUNDANT_EQ = prove
 (`!P a s. a IN (P hull s) <=> ((P hull (a INSERT s)) = (P hull s))`,
  REWRITE_TAC[hull_def, BIGINTER, EXTENSION, SUBSET_DEF, IN_INSERT] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN METIS_TAC[]); (*此处用METIS_TAC效果好*)

val HULL_REDUNDANT = prove
 (`!P a s. a IN (P hull s) ==> ((P hull (a INSERT s)) = (P hull s))`,
  REWRITE_TAC[HULL_REDUNDANT_EQ]);

val HULL_INDUCT = prove
 (`!P p s. (!x:'a. x IN s ==> p x) /\ P {x | p x}
           ==> !x. x IN (P hull s) ==> p x`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`P:('a->bool)->bool`, `s:'a->bool`, `{x:'a | p x}`]
                HULL_MINIMAL) THEN
  REWRITE_TAC[SUBSET_DEF] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]);

val HULL_INC = prove
 (`!P s x. x IN s ==> x IN (P hull s)`,
  PROVE_TAC[REWRITE_RULE[SUBSET_DEF] HULL_SUBSET]);

val HULL_IMAGE_SUBSET = prove
 (`!P f s. P(P hull s) /\ (!s. P s ==> P(IMAGE f s))
           ==> (P hull (IMAGE f s)) SUBSET ((IMAGE f (P hull s)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC bool_ss[IMAGE_SUBSET, HULL_SUBSET]);

val HULL_IMAGE_GALOIS = prove
 (`!P f g s. (!s. P(P hull s)) /\
             (!s. P s ==> P(IMAGE f s)) /\ (!s. P s ==> P(IMAGE g s)) /\
             (!s t. s SUBSET IMAGE g t <=> IMAGE f s SUBSET t)
             ==> ((P hull (IMAGE f s)) = IMAGE f (P hull s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC bool_ss[HULL_IMAGE_SUBSET] THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC I empty_rewrites [GSYM th]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC bool_ss[HULL_SUBSET]);

val HULL_IMAGE = prove
 (`!P f s. (!s. P(P hull s)) /\ (!s. P(IMAGE f s) <=> P s) /\
           (!x y:'a. (f x = f y) ==> (x = y)) /\ (!y. ?x. f x = y)
           ==> ((P hull (IMAGE f s)) = IMAGE f (P hull s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[BIJECTIVE_LEFT_RIGHT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:'a->'a` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC HULL_IMAGE_GALOIS THEN EXISTS_TAC `g:'a->'a` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
  [ALL_TAC, REWRITE_TAC[SUBSET_DEF, IN_IMAGE] THEN PROVE_TAC[]]  THEN
  X_GEN_TAC `s:'a->bool` THEN
  FIRST_X_ASSUM(fn th => GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM th]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION, IN_IMAGE] THEN PROVE_TAC[]);

val IS_HULL = prove
 (`!P s. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f))
         ==> (P s <=> ?t. s = (P hull t))`,
  PROVE_TAC[HULL_P, P_HULL]);

val HULLS_EQ = prove
 (`!P s t.
        (!f. (!s. s IN f ==> P s) ==> P (BIGINTER f)) /\
        s SUBSET (P hull t) /\ t SUBSET (P hull s)
        ==> ((P hull s) = (P hull t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC bool_ss[P_HULL]);

val HULL_P_AND_Q = prove
 (`!P Q. (!f. (!s. s IN f ==> P s) ==> P(BIGINTER f)) /\
         (!f. (!s. s IN f ==> Q s) ==> Q(BIGINTER f)) /\
         (!s. Q s ==> Q(P hull s))
         ==> (((\x. P x /\ Q x) hull s) = (P hull (Q hull s)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HULL_UNIQUE THEN ASM_SIMP_TAC bool_ss[HULL_INC, SUBSET_HULL] THEN
  PROVE_TAC[P_HULL, HULL_SUBSET, SUBSET_TRANS]);
(**)

val span_def = Define
  `span s = (subspace hull s)`;

val dependent_def = Define
 `dependent s = (?a. a IN s /\ a IN span(s DELETE a))`;

val independent_def = Define
 `independent s = ~(dependent s)`;

(* ------------------------------------------------------------------------- *)
(* Closure properties of subspaces.                                          *)
(* ------------------------------------------------------------------------- *)

val SUBSPACE_UNIV = prove
 (`subspace(UNIV:real['n]->bool)`,
  REWRITE_TAC[subspace_def, IN_UNIV]);

val SUBSPACE_IMP_NONEMPTY = prove
 (`!s. subspace s ==> ~(s = {})`,
  REWRITE_TAC[subspace_def] THEN PROVE_TAC[NOT_IN_EMPTY]);

val SUBSPACE_0 = prove
 (`subspace s ==> VECTOR_0 IN s`,
  SIMP_TAC bool_ss[subspace_def]);

val SUBSPACE_ADD = prove
 (`!x y s. subspace s /\ x IN s /\ y IN s ==> (x + y) IN s`,
  SIMP_TAC bool_ss[subspace_def]);

val SUBSPACE_MUL = prove
 (`!x c s. subspace s /\ x IN s ==> (c * x) IN s`,
  SIMP_TAC bool_ss[subspace_def]);

val SUBSPACE_NEG = prove
 (`!x c s. subspace s /\ x IN s ==> (~x) IN s`,
  SIMP_TAC bool_ss[VECTOR_ARITH ``~x:real['n] = -(&1) * x``, SUBSPACE_MUL]);

val SUBSPACE_SUB = prove
 (`!x y s. subspace s /\ x IN s /\ y IN s ==> (x - y) IN s`,
  SIMP_TAC bool_ss[VECTOR_SUB, SUBSPACE_ADD, SUBSPACE_NEG]);

val SUBSPACE_VSUM = prove
 (`!s f t. subspace s /\ FINITE t /\ (!x. x IN t ==> f(x) IN s)
           ==> (VSUM t f) IN s`,
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, SUBSPACE_0, IN_INSERT, SUBSPACE_ADD]);
  
val SUBSPACE_LINEAR_IMAGE = prove
 (`!f s. linear f /\ subspace s ==> subspace(IMAGE f s)`,
  SIMP_TAC bool_ss[subspace_def, GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  (*SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN *)REWRITE_TAC[IN_IMAGE] THEN
  PROVE_TAC[linear_def, LINEAR_0]);

val SUBSPACE_LINEAR_PREIMAGE = prove
 (`!f s. linear f /\ subspace s ==> subspace {x | f(x) IN s}`,
  SIMP_TAC bool_ss[subspace_def, GSPEC_ETA, IN_ABS] THEN
  PROVE_TAC[linear_def, LINEAR_0]);

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

val SPAN_SPAN = prove
 (`!s. span(span s) = span s`,
  REWRITE_TAC[span_def, HULL_HULL]);

val SPAN_MONO = prove
 (`!s t. s SUBSET t ==> span s SUBSET span t`,
  REWRITE_TAC[span_def, HULL_MONO]);

val SUBSPACE_SPAN = prove
 (`!s. subspace(span s)`,
  GEN_TAC THEN REWRITE_TAC[span_def] THEN MATCH_MP_TAC P_HULL THEN
  SIMP_TAC bool_ss[subspace_def, IN_BIGINTER]);

val SPAN_CLAUSES = prove
 (`(!a s. a IN s ==> a IN span s) /\
   (VECTOR_0 IN span s) /\
   (!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s) /\
   (!x c s. x IN span s ==> (c * x) IN span s)`,
  PROVE_TAC[span_def, HULL_SUBSET, SUBSET_DEF, SUBSPACE_SPAN, subspace_def]);

val SPAN_INDUCT = prove
 (`!s h. (!x. x IN s ==> x IN h) /\ subspace h ==> !x. x IN span(s) ==> h(x)`,
  REWRITE_TAC[span_def] THEN PROVE_TAC[SUBSET_DEF, HULL_MINIMAL, IN_DEF]);

val SPAN_EMPTY = prove
 (`span {} = {VECTOR_0}`,
  REWRITE_TAC[span_def] THEN MATCH_MP_TAC HULL_UNIQUE THEN
  SIMP_TAC bool_ss[subspace_def, SUBSET_DEF, IN_SING, NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);

val INDEPENDENT_EMPTY = prove
 (`independent {}`,
  REWRITE_TAC[independent_def, dependent_def, NOT_IN_EMPTY]);

val INDEPENDENT_NONZERO = prove
 (`!s. independent s ==> ~(VECTOR_0 IN s)`,
  REWRITE_TAC[independent_def, dependent_def] THEN PROVE_TAC[SPAN_CLAUSES]);

val INDEPENDENT_MONO = prove
 (`!s t. independent t /\ s SUBSET t ==> independent s`,
  REWRITE_TAC[independent_def, dependent_def] THEN
  PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_DELETE]);

val DEPENDENT_MONO = prove
 (`!s t:real['n]->bool. dependent s /\ s SUBSET t ==> dependent t`,
  ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> ~r /\ q ==> ~p`] THEN
  REWRITE_TAC[GSYM independent_def, INDEPENDENT_MONO]);

val SPAN_SUBSPACE = prove
 (`!b s. b SUBSET s /\ s SUBSET (span b) /\ subspace s ==> (span b = s)`,
  PROVE_TAC[SUBSET_ANTISYM, span_def, HULL_MINIMAL]);

val SPAN_INDUCT_ALT = prove
 (`!s h. h(VECTOR_0) /\
         (!c x y. x IN s /\ h(y) ==> h(c * x + y))
          ==> !x:real['n]. x IN span(s) ==> h(x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o prove_nonschematic_inductive_relations_exist bool_monoset o concl) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real['n]->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real['n]. x IN span(s) ==> g(x)`
   (fn th => PROVE_TAC[th]) THEN
  MATCH_MP_TAC SPAN_INDUCT THEN REWRITE_TAC[subspace_def,SPECIFICATION] THEN
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC bool_ss[Once SWAP_FORALL_THM, RIGHT_FORALL_IMP_THM] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM HO_MATCH_MP_TAC) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB, VECTOR_MUL_ASSOC] THEN
  PROVE_TAC[IN_DEF, VECTOR_ADD_LID, VECTOR_ADD_ASSOC, VECTOR_ADD_SYM,
                VECTOR_MUL_LID, VECTOR_MUL_RZERO]);

(* ------------------------------------------------------------------------- *)
(* Individual closure properties.                                            *)
(* ------------------------------------------------------------------------- *)

val SPAN_SUPERSET = prove
 (`!x. x IN s ==> x IN span s`,
  PROVE_TAC[SPAN_CLAUSES]);

val SPAN_INC = prove
 (`!s. s SUBSET span s`,
  REWRITE_TAC[SUBSET_DEF, SPAN_SUPERSET]);

val SPAN_UNION_SUBSET = prove
 (`!s t. span s UNION span t SUBSET span(s UNION t)`,
  REWRITE_TAC[span_def, HULL_UNION_SUBSET]);

val SPAN_UNIV = prove
 (`span(UNIV:real['n]->bool) = (UNIV:real['n]->bool)`,
  SIMP_TAC bool_ss[SPAN_INC, (prove(`UNIV SUBSET s ==> (s = UNIV)`, PROVE_TAC[UNIV_SUBSET]))]);

val SPAN_0 = prove
 (`VECTOR_0 IN span s`,
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_0]);

val SPAN_ADD = prove
 (`!x y s. x IN span s /\ y IN span s ==> (x + y) IN span s`,
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_ADD]);

val SPAN_MUL = prove
 (`!x c s. x IN span s ==> (c * x) IN span s`,
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_MUL]);

val SPAN_MUL_EQ = prove
 (`!x:real['n] c s. ~(c = &0) ==> ((c * x) IN span s <=> x IN span s)`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN ASM_SIMP_TAC bool_ss[SPAN_MUL] THEN
  SUBGOAL_THEN `(inv(c) * c * x:real['n]) IN span s` MP_TAC THENL
   [ASM_SIMP_TAC bool_ss[GSYM VECTOR_MUL_ASSOC, SPAN_MUL],
    ASM_SIMP_TAC bool_ss[REAL_MUL_LINV, VECTOR_MUL_LID]]);

val SPAN_NEG = prove
 (`!x s. x IN span s ==> (~x) IN span s`,
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_NEG]);

val SPAN_NEG_EQ = prove
 (`!x s. ~x IN span s <=> x IN span s`,
  PROVE_TAC[SPAN_NEG, VECTOR_NEG_NEG]);

val SPAN_SUB = prove
 (`!x y s. x IN span s /\ y IN span s ==> (x - y) IN span s`,
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_SUB]);

val SPAN_VSUM = prove
 (`!s f t. FINITE t /\ (!x. x IN t ==> f(x) IN span(s))
           ==> (VSUM t f) IN span(s)`,
  PROVE_TAC[SUBSPACE_SPAN, SUBSPACE_VSUM]);

val SPAN_ADD_EQ = prove
 (`!s x y. x IN span s ==> ((x + y) IN span s <=> y IN span s)`,
  PROVE_TAC[SPAN_ADD, SPAN_SUB, VECTOR_ARITH ``(x + y) - x:real['n] = y``]);

val SPAN_EQ_SELF = prove
 (`!s. (span s = s) <=> subspace s`,
  GEN_TAC THEN EQ_TAC THENL [PROVE_TAC[SUBSPACE_SPAN], ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SPAN_SUBSPACE THEN
  ASM_REWRITE_TAC[SUBSET_REFL, SPAN_INC]);

val SPAN_SUBSET_SUBSPACE = prove
 (`!s t:real['n]->bool. s SUBSET t /\ subspace t ==> span s SUBSET t`,
  PROVE_TAC[SPAN_MONO, SPAN_EQ_SELF]);

val SUBSPACE_TRANSLATION_SELF = prove
 (`!s a. subspace s /\ a IN s ==> (IMAGE (\x. a + x) s = s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_SURJ, SURJ_DEF] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o GEN_REWRITE_RULE I empty_rewrites [GSYM SPAN_EQ_SELF]) THEN
  ASM_SIMP_TAC bool_ss[SPAN_ADD_EQ, SPAN_CLAUSES] THEN
  PROVE_TAC[VECTOR_ARITH ``(a + x:real['n] = y) <=> (x = y - a)``, 
            SPAN_SUPERSET,SPAN_SUB, EXISTS_REFL]);

val SUBSPACE_TRANSLATION_SELF_EQ = prove
 (`!s a:real['n]. subspace s ==> ((IMAGE (\x. a + x) s = s) <=> a IN s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC bool_ss[SUBSPACE_TRANSLATION_SELF] THEN
  DISCH_THEN(MP_TAC o AP_TERM ``\s. (a:real['n]) IN s``) THEN
  BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `VECTOR_0:real['n]` THEN
  PROVE_TAC[subspace_def, VECTOR_ADD_RID]);

val SUBSPACE_SUMS = prove
 (`!s t. subspace s /\ subspace t
         ==> subspace {x + y | x IN s /\ y IN t}`,
  SIMP_TAC bool_ss[subspace_def, GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REPEAT STRIP_TAC THENL
   [PROVE_TAC[VECTOR_ADD_LID],
    ASM_REWRITE_TAC[] THEN
	ONCE_REWRITE_TAC[VECTOR_ARITH
     ``(x + y) + (x' + y'):real['n] = (x + x') + (y + y')``] THEN
    PROVE_TAC[],
    ASM_REWRITE_TAC[] THEN
	REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN PROVE_TAC[]]);

val SPAN_UNION = prove
 (`!s t. span(s UNION t) = {x + y:real['n] | x IN span s /\ y IN span t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
    SIMP_TAC bool_ss[SUBSPACE_SUMS, SUBSPACE_SPAN] THEN
    REWRITE_TAC[SUBSET_DEF, IN_UNION] THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
	X_GEN_TAC `x:real['n]` THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`x:real['n]`, `VECTOR_0:real['n]`] THEN
      ASM_SIMP_TAC bool_ss[SPAN_SUPERSET, SPAN_0, VECTOR_ADD_RID],
      MAP_EVERY EXISTS_TAC [`VECTOR_0:real['n]`, `x:real['n]`] THEN
      ASM_SIMP_TAC bool_ss[SPAN_SUPERSET, SPAN_0, VECTOR_ADD_LID]],
    REWRITE_TAC[SUBSET_DEF] THEN
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
	X_GEN_TAC `x:real['n]` THEN SIMP_TAC bool_ss [GSYM LEFT_FORALL_IMP_THM] THEN
	REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_ADD THEN
    PROVE_TAC[SPAN_MONO, SUBSET_UNION, SUBSET_DEF]]);

(* ------------------------------------------------------------------------- *)
(* Mapping under linear image.                                               *)
(* ------------------------------------------------------------------------- *)

val SPAN_LINEAR_IMAGE = prove
 (`!f:real['m]->real['n] s. linear f ==> (span(IMAGE f s) = IMAGE f (span s))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I empty_rewrites[EXTENSION] THEN
  X_GEN_TAC `x:real['n]` THEN EQ_TAC THEN SPEC_TAC(`x:real['n]`,`x:real['n]`) THENL
   [ALL_TAC, SIMP_TAC bool_ss[FORALL_IN_IMAGE]] THEN HO_MATCH_MP_TAC SPAN_INDUCT THEN
   REWRITE_TAC[prove(`(\x. x IN s) = s`, SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS]),
     prove(`(\x. f x IN span(s)) = {x | f(x) IN span s}`, SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS])] THEN
    ASM_SIMP_TAC bool_ss[SUBSPACE_SPAN, SUBSPACE_LINEAR_IMAGE, SUBSPACE_LINEAR_PREIMAGE] THEN
    SIMP_TAC bool_ss[FORALL_IN_IMAGE, GSPEC_ETA, IN_ABS] THEN 
    PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF, IN_IMAGE]);

(* ------------------------------------------------------------------------- *)
(* The key breakdown property.                                               *)
(* ------------------------------------------------------------------------- *)

val SPAN_BREAKDOWN = prove
 (`!b s a:real['n].
      b IN s /\ a IN span s ==> ?k. (a - k * b) IN span(s DELETE b)`,
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN HO_MATCH_MP_TAC SPAN_INDUCT THEN
  SIMP_TAC bool_ss[subspace_def, IN_ABS] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `a:real['n] = b`, ALL_TAC] THEN
  PROVE_TAC[SPAN_CLAUSES, IN_DELETE, VECTOR_ARITH
   ``(a - &1 * a = VECTOR_0) /\ (a - &0 * b = a) /\
    ((x + y) - (k1 + k2) * b = (x - k1 * b) + (y - k2 * b)) /\
    (c * x - (c * k) * y = c * (x - k * y))``]);

val SPAN_BREAKDOWN_EQ = prove
 (`!a:real['n] s. (x IN span(a INSERT s) <=> (?k. (x - k * a) IN span s))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJ(prove(`(a:real['n]) IN (a INSERT s)`, REWRITE_TAC[IN_INSERT]))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_BREAKDOWN) THEN
    HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    SPEC_TAC(`x - k * a:real['n]`,`y:real['n]`) THEN
    REWRITE_TAC[GSYM SUBSET_DEF] THEN MATCH_MP_TAC SPAN_MONO THEN
	REWRITE_TAC[DELETE_INSERT, DELETE_SUBSET],
    DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
    SUBST1_TAC(VECTOR_ARITH ``x = (x - k * a) + k * a:real['n]``) THEN
    MATCH_MP_TAC SPAN_ADD THEN
    PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_INSERT, SPAN_CLAUSES]]);

val SPAN_INSERT_0 = prove
 (`!s. span(VECTOR_0 INSERT s) = span s`,
  SIMP_TAC bool_ss[EXTENSION, SPAN_BREAKDOWN_EQ, VECTOR_MUL_RZERO, VECTOR_SUB_RZERO]);

val SPAN_SING = prove
 (`!a. span {a} = {u * a | u IN (UNIV:real set)}`,
  REWRITE_TAC[EXTENSION, SPAN_BREAKDOWN_EQ, SPAN_EMPTY] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC[IN_UNIV, IN_SING, VECTOR_SUB_EQ]);

(* ------------------------------------------------------------------------- *)
(* Hence some "reversal" results.                                            *)
(* ------------------------------------------------------------------------- *)

val IN_SPAN_INSERT = prove
 (`!a b:real['n] s.
        a IN span(b INSERT s) /\ ~(a IN span s) ==> b IN span(a INSERT s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real['n]`, `(b:real['n]) INSERT s`, `a:real['n]`]
    SPAN_BREAKDOWN) THEN ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN ASM_CASES_TAC `k = &0` THEN
  ASM_REWRITE_TAC[VECTOR_ARITH ``a - &0 * b:real['n] = a``, DELETE_INSERT] THENL
   [PROVE_TAC[SPAN_MONO, SUBSET_DEF, DELETE_SUBSET], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC ``inv(k)`` o MATCH_MP SPAN_MUL) THEN
  ASM_SIMP_TAC bool_ss[VECTOR_SUB_LDISTRIB, VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN
  DISCH_TAC THEN SUBST1_TAC(VECTOR_ARITH
   ``b:real['n] = inv(k) * a - (inv(k) * a - &1 * b)``) THEN
  MATCH_MP_TAC SPAN_SUB THEN
  PROVE_TAC[SPAN_CLAUSES, IN_INSERT, SUBSET_DEF, IN_DELETE, SPAN_MONO]);

val IN_SPAN_DELETE = prove
 (`!a b s.
         a IN span s /\ ~(a IN span (s DELETE b))
         ==> b IN span (a INSERT (s DELETE b))`,
  PROVE_TAC[IN_SPAN_INSERT, SPAN_MONO, SUBSET_DEF, IN_INSERT, IN_DELETE]);

val EQ_SPAN_INSERT_EQ = prove
 (`!s x y:real['n]. (x - y) IN span s ==> (span(x INSERT s) = span(y INSERT s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SPAN_BREAKDOWN_EQ, EXTENSION] THEN
  PROVE_TAC[SPAN_ADD, SPAN_SUB, SPAN_MUL,
                VECTOR_ARITH ``(z - k * y:real['n]) - k * (x - y) = z - k * x``,
                VECTOR_ARITH ``(z - k * x:real['n]) + k * (x - y) = z - k * y``]);

(* ------------------------------------------------------------------------- *)
(* Transitivity property.                                                    *)
(* ------------------------------------------------------------------------- *)

val SPAN_TRANS = prove
 (`!x y:real['n] s. x IN span(s) /\ y IN span(x INSERT s) ==> y IN span(s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real['n]`, `(x:real['n]) INSERT s`, `y:real['n]`]
         SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBST1_TAC(VECTOR_ARITH ``y:real['n] = (y - k * x) + k * x``) THEN
  MATCH_MP_TAC SPAN_ADD THEN ASM_SIMP_TAC bool_ss[SPAN_MUL] THEN
  PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_INSERT, IN_DELETE]);

(* ------------------------------------------------------------------------- *)
(* An explicit expansion is sometimes needed.                                *)
(* ------------------------------------------------------------------------- *)

val SPAN_EXPLICIT = prove
 (`!(p:real['n] -> bool).
        span p =
         {y | ?s u. FINITE s /\ s SUBSET p /\
                    (VSUM s (\v. u v * v) = y)}`,
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  SIMP_TAC bool_ss[SUBSET_DEF, GSPEC_ETA, IN_ABS] THENL
   [ALL_TAC,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SPAN_VSUM THEN ASM_SIMP_TAC bool_ss[BETA_THM] THEN
    PROVE_TAC[SPAN_SUPERSET, SPAN_MUL]] THEN
  HO_MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
   [EXISTS_TAC `{}:real['n]->bool` THEN
    REWRITE_TAC[FINITE_RULES, VSUM_CLAUSES, EMPTY_SUBSET, NOT_IN_EMPTY],
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`, `x:real['n]`, `y:real['n]`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real['n]->bool`, `u:real['n]->real`] THEN
  STRIP_TAC THEN EXISTS_TAC `(x:real['n]) INSERT s` THEN
  EXISTS_TAC `\y. if y = x then (if x IN s then (u:real['n]->real) y + c else c)
                  else u y` THEN
  ASM_SIMP_TAC bool_ss[FINITE_INSERT, IN_INSERT, VSUM_CLAUSES] THEN
  CONJ_TAC THENL [PROVE_TAC[], ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (prove(
     `x IN s ==> (s = x INSERT (s DELETE x))`, SIMP_TAC bool_ss[INSERT_DELETE]))) THEN
    ASM_SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_INSERT, FINITE_DELETE, IN_DELETE] THEN
    MATCH_MP_TAC(VECTOR_ARITH
      ``(y:real['n] = z) ==> ((c + d) * x + y = d * x + (c * x + z))``),
    AP_TERM_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN BETA_TAC THEN PROVE_TAC[IN_DELETE]);
(*20120704*)
val DEPENDENT_EXPLICIT = prove
 (`!p. dependent (p:real['n]-> bool) <=>
                ?s u. FINITE s /\ s SUBSET p /\
                      (?v. v IN s /\ ~(u v = &0)) /\
                      (VSUM s (\v. u v * v) = VECTOR_0)`,
  GEN_TAC THEN SIMP_TAC bool_ss[dependent_def, SPAN_EXPLICIT, GSPEC_ETA, IN_ABS] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
  EQ_TAC THEN SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THENL
   [MAP_EVERY X_GEN_TAC [`s:real['n]->bool`,`u:real['n]->real`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`VSUM s (\v. u v * v) INSERT s`,
      `\y. if y = VSUM s (\v. u v * v) then - &1 else (u:real['n]->real) y`, `VSUM s (\v. u v * v)`] THEN
    ASM_REWRITE_TAC[IN_INSERT, INSERT_SUBSET, FINITE_INSERT] THEN
    CONJ_TAC THENL [PROVE_TAC[SUBSET_DELETE], ALL_TAC] THEN
    ASM_SIMP_TAC bool_ss[VSUM_CLAUSES] THEN REWRITE_TAC[REAL_10, REAL_NEG_EQ0] THEN
    COND_CASES_TAC THENL [PROVE_TAC[SUBSET_DEF, IN_DELETE], ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH ``(- &1 * a + s = VECTOR_0) <=> (a = s)``] THEN
    MATCH_MP_TAC VSUM_EQ THEN BETA_TAC THEN PROVE_TAC[],
    MAP_EVERY X_GEN_TAC [`s:real['n]->bool`, `u:real['n]->real`, `a:real['n]`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`s DELETE (a:real['n])`,
      `\i. -((u:real['n]->real) i) / (u a)`] THEN
    ASM_SIMP_TAC bool_ss[VSUM_DELETE, FINITE_DELETE] THEN
    SUBGOAL_THEN `VSUM s (\v. -u v / u a * v) - -u a / u a * a = a` SUBST1_TAC THENL[
      REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC bool_ss[VECTOR_MUL_LNEG, GSYM VECTOR_MUL_ASSOC, VSUM_LMUL, VSUM_NEG,
						 VECTOR_MUL_RNEG, VECTOR_MUL_RZERO] THEN
      ASM_SIMP_TAC bool_ss[VECTOR_MUL_ASSOC, REAL_MUL_LINV] THEN VECTOR_ARITH_TAC,
	  PROVE_TAC[SUBSET_DEF, SUBSET_DELETE_BOTH]]]);

val DEPENDENT_FINITE = prove
 (`!s:real['n]->bool.
        FINITE s
        ==> (dependent s <=> ?u. (?v. v IN s /\ ~(u v = &0)) /\
                                 (VSUM s (\v. u(v) * v) = VECTOR_0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DEPENDENT_EXPLICIT] THEN EQ_TAC THEN
  SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real['n]->bool`, `u:real['n]->real`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    EXISTS_TAC `\v:real['n]. if v IN t then u(v) else &0` THEN
    BETA_TAC THEN CONJ_TAC THENL [PROVE_TAC[SUBSET_DEF], ALL_TAC] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ASM_SIMP_TAC bool_ss[VECTOR_MUL_LZERO, GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC bool_ss[prove(`t SUBSET s ==> ({x | x IN s /\ x IN t} = t)`,
						 REWRITE_TAC[GSYM IN_INTER, GSPEC_ID] THEN
						 PROVE_TAC[SUBSET_INTER_ABSORPTION, INTER_COMM])],
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`s:real['n]->bool`, `u:real['n]->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);

val SPAN_FINITE = prove
 (`!s:real['n]->bool.
        FINITE s ==> (span s = {y | ?u. VSUM s (\v. u v * v) = y})`,
  REPEAT STRIP_TAC THEN SIMP_TAC bool_ss[SPAN_EXPLICIT, EXTENSION, GSPEC_ETA, IN_ABS] THEN
  X_GEN_TAC `y:real['n]` THEN EQ_TAC THEN SIMP_TAC bool_ss[GSYM LEFT_FORALL_IMP_THM] THENL
   [MAP_EVERY X_GEN_TAC [`t:real['n]->bool`, `u:real['n]->real`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `\x:real['n]. if x IN t then u(x) else &0` THEN
    SIMP_TAC bool_ss[COND_RAND, COND_RATOR, VECTOR_MUL_LZERO] THEN
    ASM_SIMP_TAC bool_ss[GSYM VSUM_RESTRICT_SET] THEN
    ASM_SIMP_TAC bool_ss[prove(`t SUBSET s ==> ({x | x IN s /\ x IN t} = t)`,
						 REWRITE_TAC[GSYM IN_INTER, GSPEC_ID] THEN
						 PROVE_TAC[SUBSET_INTER_ABSORPTION, INTER_COMM])],
    X_GEN_TAC `u:real['n]->real` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`s:real['n]->bool`, `u:real['n]->real`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);

(* ------------------------------------------------------------------------- *)
(* Standard bases are a spanning set, and obviously finite.                  *)
(* ------------------------------------------------------------------------- *)

val SPAN_STDBASIS = prove
 (`span {basis i :real['n] | i < dimindex(:'n)} = UNIV`,
  REWRITE_TAC[EXTENSION, IN_UNIV] THEN X_GEN_TAC `x:real['n]` THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites[GSYM BASIS_EXPANSION] THEN
  MATCH_MP_TAC SPAN_VSUM THEN SIMP_TAC bool_ss[FINITE_COUNT, IN_COUNT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[]);

val HAS_SIZE_STDBASIS = prove
 (`{basis i :real['n] | i < dimindex(:'n)} HAS_SIZE dimindex(:'n)`,
  SIMP_TAC bool_ss[Once (prove(`{f x | P x} = IMAGE f {x | P x}`,
				   REWRITE_TAC[EXTENSION] THEN
				   CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
				   SIMP_TAC bool_ss[IN_IMAGE, GSPEC_ETA, IN_ABS, IN_DEF]))] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  REWRITE_TAC[HAS_SIZE_def, GSYM count_def, FINITE_COUNT, CARD_COUNT, IN_COUNT] THEN
  PROVE_TAC[BASIS_INJ]);

val FINITE_STDBASIS = prove
 (`FINITE {basis i :real['n] |i < dimindex(:'n)}`,
  PROVE_TAC[HAS_SIZE_STDBASIS, HAS_SIZE_def]);

val CARD_STDBASIS = prove
 (`CARD {basis i :real['n] |i < dimindex(:'n)} = dimindex(:'n)`,
   PROVE_TAC[HAS_SIZE_STDBASIS, HAS_SIZE_def]);
		
val IN_SPAN_IMAGE_BASIS = prove
 (`!x:real['n] s.
        x IN span(IMAGE basis s) <=>
          !i. i < dimindex(:'n) /\ ~(i IN s) ==>(x ' i = &0)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`x:real['n]`,`x:real['n]`) THEN HO_MATCH_MP_TAC SPAN_INDUCT THEN
    SIMP_TAC bool_ss[subspace_def, IN_ABS, VEC_0_COMPONENT, VECTOR_ADD_COMPONENT,
             VECTOR_MUL_COMPONENT, REAL_MUL_RZERO, REAL_ADD_RID] THEN
    SIMP_TAC bool_ss[FORALL_IN_IMAGE, BASIS_COMPONENT] THEN PROVE_TAC[],
    DISCH_TAC THEN SIMP_TAC bool_ss[SPAN_EXPLICIT, GSPEC_ETA, IN_ABS] THEN
    EXISTS_TAC `(IMAGE basis (count(dimindex(:'n)) INTER s)):real['n]->bool` THEN
    SIMP_TAC bool_ss[IMAGE_FINITE, FINITE_INTER, FINITE_COUNT] THEN
    SIMP_TAC bool_ss[RIGHT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET], ALL_TAC] THEN
    EXISTS_TAC `\v:real['n]. x dot v` THEN
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
    ONCE_REWRITE_TAC[prove(
     `(if x = y then p else q) = (if y = x then p else q)`, PROVE_TAC[])] THEN
    SIMP_TAC bool_ss[SUM_DELTA, REAL_MUL_RZERO, IN_INTER, IN_COUNT, DOT_BASIS] THEN
    PROVE_TAC[REAL_MUL_RID]]);
(* ------------------------------------------------------------------------- *)
(* This is useful for building a basis step-by-step.                         *)
(* ------------------------------------------------------------------------- *)

val INDEPENDENT_STDBASIS = prove
 (`independent {basis i :real['n] | i < dimindex(:'n)}`,
  SIMP_TAC std_ss[
	Once (prove(`{f x | P x} = IMAGE f {x | P x}`,
	  REWRITE_TAC[EXTENSION, IN_IMAGE] THEN
      CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[]))] THEN
  REWRITE_TAC[independent_def, dependent_def] THEN
  SIMP_TAC pure_ss[EXISTS_IN_IMAGE] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `IMAGE basis {i | i < dimindex(:'n)} DELETE
           (basis k:real['n]) =
    IMAGE basis ({i | i < dimindex(:'n)} DELETE k)`
  SUBST1_TAC THENL
   [SIMP_TAC bool_ss[EXTENSION, IN_IMAGE, IN_DELETE, GSPEC_ETA, IN_ABS] THEN
    GEN_TAC THEN EQ_TAC THEN PROVE_TAC[BASIS_INJ],
    ALL_TAC] THEN
  REWRITE_TAC[IN_SPAN_IMAGE_BASIS] THEN DISCH_THEN(MP_TAC o SPEC ``k:num``) THEN
  ASM_SIMP_TAC bool_ss[IN_DELETE, BASIS_COMPONENT, REAL_OF_NUM_EQ] THEN ARITH_TAC);

val INDEPENDENT_INSERT = prove
 (`!a:real['n] s. independent(a INSERT s) <=>
                  if a IN s then independent s
                  else independent s /\ ~(a IN span s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a:real['n]) IN s` THEN
  ASM_SIMP_TAC bool_ss[prove(`x IN s ==> (x INSERT s = s)`,
	SIMP_TAC bool_ss[INSERT_DEF, EXTENSION, GSPEC_ETA, IN_ABS] THEN PROVE_TAC[])] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [PROVE_TAC[INDEPENDENT_MONO, SUBSET_DEF, IN_INSERT],
      POP_ASSUM MP_TAC THEN REWRITE_TAC[independent_def, dependent_def] THEN
      PROVE_TAC[IN_INSERT, DELETE_INSERT, DELETE_NON_ELEMENT]],
    ALL_TAC] THEN
  SIMP_TAC bool_ss[independent_def, dependent_def] THEN
  STRIP_TAC THEN X_GEN_TAC `b:real['n]` THEN
  REWRITE_TAC[IN_INSERT] THEN ASM_CASES_TAC `b:real['n] = a` THENL[
	ASM_SIMP_TAC bool_ss[DELETE_INSERT] THEN PROVE_TAC[DELETE_NON_ELEMENT],
  ASM_SIMP_TAC bool_ss[DELETE_INSERT] THEN
  PROVE_TAC[IN_SPAN_INSERT, INSERT_DELETE]]);

(* ------------------------------------------------------------------------- *)
(* The degenerate case of the Exchange Lemma.                                *)
(* ------------------------------------------------------------------------- *)

val SPANNING_SUBSET_INDEPENDENT = prove
 (`!s t:real['n]->bool.
        t SUBSET s /\ independent s /\ s SUBSET span(t) ==> (s = t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_DEF] THEN
  X_GEN_TAC `a:real['n]` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites [independent_def]) THEN
  SIMP_TAC bool_ss[dependent_def] THEN
  DISCH_THEN(MP_TAC o SPEC ``a:real['n]``) THEN ASM_REWRITE_TAC[] THEN
  PROVE_TAC[SPAN_MONO, SUBSET_DEF, IN_DELETE]);

(* ------------------------------------------------------------------------- *)
(* The general case of the Exchange Lemma, the key to what follows.          *)
(* ------------------------------------------------------------------------- *)
 
val EXCHANGE_LEMMA = prove
 (`!s t:real['n]->bool.
        FINITE t /\ independent s /\ s SUBSET span t
        ==> ?t'. (t' HAS_SIZE (CARD t)) /\
                 s SUBSET t' /\ t' SUBSET (s UNION t) /\ s SUBSET (span t')`,
  Induct_on `CARD(t DIFF s :real['n]->bool)` THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(s:real['n]->bool) SUBSET t` THENL
   [PROVE_TAC[HAS_SIZE_def, SUBSET_UNION], ALL_TAC,
    PROVE_TAC[HAS_SIZE_def, SUBSET_UNION], ALL_TAC]THEN
  ASM_CASES_TAC `t SUBSET (s:real['n]->bool)` THENL
   [PROVE_TAC[SPANNING_SUBSET_INDEPENDENT, HAS_SIZE_def], ALL_TAC,
    PROVE_TAC[SPANNING_SUBSET_INDEPENDENT, HAS_SIZE_def], ALL_TAC] THEN
  STRIP_TAC THEN
  Q.PAT_ASSUM `$~ X` (MP_TAC o REWRITE_RULE[SUBSET_DEF]) THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real['n]` STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_ASSUM `$= X Y` (MP_TAC o SYM) THENL
  [ASM_SIMP_TAC bool_ss[FINITE_DIFF, CARD_EQ_0] THEN
   PROVE_TAC[IN_DIFF, MEMBER_NOT_EMPTY], ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `s SUBSET span(t DELETE (b:real['n]))` THENL
   [FIRST_X_ASSUM(MP_TAC o
		SPECL [`t DELETE (b:real['n])`, `s:real['n]->bool`]) THEN
    ASM_REWRITE_TAC[prove(`s DELETE a DIFF t = (s DIFF t) DELETE a`,
		SIMP_TAC bool_ss[DELETE_DEF, DIFF_DEF, EXTENSION, GSPEC_ETA, IN_ABS] THEN PROVE_TAC[])] THEN
    ASM_SIMP_TAC bool_ss[CARD_DELETE, FINITE_DIFF, IN_DIFF, FINITE_DELETE] THEN
    ASM_REWRITE_TAC[SUC_SUB1] THEN
	DISCH_THEN(X_CHOOSE_THEN `u:real['n]->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(b:real['n]) INSERT u` THEN
    ASM_SIMP_TAC bool_ss[SUBSET_INSERT, INSERT_SUBSET, IN_UNION] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(u:real['n]->bool) HAS_SIZE CARD(t:real['n]->bool) - 1` THEN
      SIMP_TAC bool_ss[HAS_SIZE_def, FINITE_RULES, CARD_CLAUSES] THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [PROVE_TAC[SUBSET_DEF, IN_UNION, IN_DELETE], ALL_TAC] THEN
      PROVE_TAC[prove(`~(n = 0) ==> (SUC(n - 1) = n)`, ARITH_TAC),
                    CARD_EQ_0, MEMBER_NOT_EMPTY],
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `u SUBSET s UNION (t DELETE (b:real['n]))` THEN
  	  PROVE_TAC[SUBSET_DEF, IN_UNION, IN_DELETE],
      PROVE_TAC[SUBSET_DEF, SPAN_MONO, IN_INSERT]],
    ALL_TAC] THEN
  UNDISCH_TAC `~(s SUBSET span (t DELETE (b:real['n])))` THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[SUBSET_DEF] THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real['n]` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real['n] = b)` ASSUME_TAC THENL
    [PROVE_TAC[], ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real['n]) IN t)` ASSUME_TAC THENL
   [PROVE_TAC[IN_DELETE, SPAN_CLAUSES], ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(a:real['n]) INSERT (t DELETE b)`, `s:real['n]->bool`]) THEN
  ASM_SIMP_TAC bool_ss[prove(
     `a IN s ==> (((a INSERT (t DELETE b)) DIFF s) = (t DIFF s) DELETE b)`,
	  SIMP_TAC bool_ss[DELETE_DEF, DIFF_DEF, EXTENSION, GSPEC_ETA, IN_ABS,
 	                   IN_INSERT] THEN PROVE_TAC[])] THEN
    ASM_SIMP_TAC bool_ss[CARD_DELETE, FINITE_DELETE, FINITE_DIFF, IN_DIFF] THEN
    ASM_SIMP_TAC bool_ss[SUC_SUB1, FINITE_INSERT, FINITE_DELETE] THEN
  SUBGOAL_THEN `s SUBSET span (a:real['n] INSERT t DELETE b)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_DEF] THEN X_GEN_TAC `x:real['n]` THEN
    DISCH_TAC THEN MATCH_MP_TAC SPAN_TRANS THEN EXISTS_TAC `b:real['n]` THEN
    PROVE_TAC[IN_SPAN_DELETE, SUBSET_DEF, SPAN_MONO,
              prove(`t SUBSET (b INSERT (a INSERT (t DELETE b)))`, REWRITE_TAC[SUBSET_INSERT_DELETE, DELETE_SUBSET])],
    ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real['n]->bool` THEN
  ASM_SIMP_TAC bool_ss[HAS_SIZE_def, CARD_CLAUSES, CARD_DELETE, FINITE_DELETE, IN_DELETE,
               prove(`(SUC(n - 1) = n) <=> ~(n = 0)`, ARITH_TAC), CARD_EQ_0] THEN
  ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[INSERT_UNION] THEN
  PROVE_TAC[NOT_IN_EMPTY, UNION_SUBSET, DELETE_SUBSET, SUBSET_TRANS, SUBSET_UNION]);
 
(* ------------------------------------------------------------------------- *)
(* This implies corresponding size bounds.                                   *)
(* ------------------------------------------------------------------------- *)

val INDEPENDENT_SPAN_BOUND = prove
 (`!s t. FINITE t /\ independent s /\ s SUBSET span(t)
         ==> FINITE s /\ CARD(s) <= CARD(t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EXCHANGE_LEMMA) THEN
  PROVE_TAC[HAS_SIZE_def, CARD_SUBSET, SUBSET_FINITE]);

val INDEPENDENT_BOUND = prove
 (`!s:real['n]->bool.
        independent s ==> FINITE s /\ CARD(s) <= dimindex(:'n)`,
  GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM CARD_STDBASIS] THEN
  MATCH_MP_TAC INDEPENDENT_SPAN_BOUND THEN
  ASM_REWRITE_TAC[FINITE_STDBASIS, SPAN_STDBASIS, SUBSET_UNIV]);

val DEPENDENT_BIGGERSET = prove
 (`!s:real['n]->bool. (FINITE s ==> CARD(s) > dimindex(:'n)) ==> dependent s`,
  MP_TAC INDEPENDENT_BOUND THEN HO_MATCH_MP_TAC MONO_ALL THEN
  PROVE_TAC[GREATER_DEF, NOT_LESS, independent_def]);

val INDEPENDENT_IMP_FINITE = prove
 (`!s:real['n]->bool. independent s ==> FINITE s`,
  SIMP_TAC bool_ss[INDEPENDENT_BOUND]);

(* ------------------------------------------------------------------------- *)
(* Explicit formulation of independence.                                     *)
(* ------------------------------------------------------------------------- *)

val INDEPENDENT_EXPLICIT = prove
 (`!b:real['n]->bool.
        independent b <=>
            FINITE b /\
            !c. (VSUM b (\v. c(v) * v) = VECTOR_0) ==> !v. v IN b ==> (c(v) = &0)`,
  GEN_TAC THEN
  ASM_CASES_TAC `FINITE(b:real['n]->bool)` THENL
   [ALL_TAC, PROVE_TAC[INDEPENDENT_BOUND]] THEN
  ASM_SIMP_TAC bool_ss[independent_def, DEPENDENT_FINITE, IMP_DISJ_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [DISJ_COMM] THEN
  EQ_TAC THEN PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Hence we can create a maximal independent subset.                         *)
(* ------------------------------------------------------------------------- *)

val MAXIMAL_INDEPENDENT_SUBSET_EXTEND = prove
 (`!s v:real['n]->bool.
        s SUBSET v /\ independent s
        ==> ?b. s SUBSET b /\ b SUBSET v /\ independent b /\
                v SUBSET (span b)`,
  REPEAT GEN_TAC THEN
  Induct_on `dimindex(:'n) - CARD(s:real['n]->bool)` THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `v SUBSET (span(s:real['n]->bool))` THENL
   [PROVE_TAC[SUBSET_REFL], ALL_TAC, PROVE_TAC[SUBSET_REFL], ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV empty_rewrites[SUBSET_DEF]) THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real['n]` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `(a:real['n]) INSERT s`, 
    FIRST_X_ASSUM(MP_TAC o SPEC ``(a:real['n]) INSERT s``)] THEN
  SUBGOAL_THEN `independent ((a:real['n]) INSERT s)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INDEPENDENT_INSERT, COND_ID], ALL_TAC,
    ASM_REWRITE_TAC[INDEPENDENT_INSERT, COND_ID], ALL_TAC] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET] THENL
   [CONJ_TAC THENL
    [PROVE_TAC[SUBSET_INSERT, SPAN_SUPERSET, SUBSET_REFL], ALL_TAC] THEN
    Q.PAT_ASSUM `$= X Y` (MP_TAC o SYM) THEN
    PROVE_TAC[SUB_EQ_0, AND_IMP_INTRO, CARD_CLAUSES, NOT_LEQ,
            SPAN_SUPERSET, FINITE_INSERT, INDEPENDENT_BOUND], ALL_TAC] THEN
  SUBGOAL_THEN `v' = dimindex (:'n) - CARD ((a:real['n]) INSERT s)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites[GSYM SUC_SUB1] THEN
    ASM_SIMP_TAC bool_ss[INDEPENDENT_BOUND, CARD_CLAUSES], ALL_TAC] THEN
  PROVE_TAC[SPAN_SUPERSET, ADD1, SUB_PLUS]);

val MAXIMAL_INDEPENDENT_SUBSET = prove
 (`!v:real['n]->bool. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b)`,
  MP_TAC(SPEC ``EMPTY:real['n]->bool`` MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  REWRITE_TAC[EMPTY_SUBSET, INDEPENDENT_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Notion of dimension.                                                      *)
(* ------------------------------------------------------------------------- *)

val dim_def = Define
  `dim v = @n. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
                   (b HAS_SIZE n)`;

val BASIS_EXISTS = prove
 (`!v. ?b. b SUBSET v /\ independent b /\ v SUBSET (span b) /\
           (b HAS_SIZE (dim v))`,
  GEN_TAC THEN REWRITE_TAC[dim_def] THEN CONV_TAC SELECT_CONV THEN
  PROVE_TAC[MAXIMAL_INDEPENDENT_SUBSET, HAS_SIZE_def, INDEPENDENT_BOUND]);

val BASIS_EXISTS_FINITE = prove
 (`!v. ?b. FINITE b /\
           b SUBSET v /\
           independent b /\
           v SUBSET (span b) /\
           (b HAS_SIZE (dim v))`,
  PROVE_TAC[BASIS_EXISTS, INDEPENDENT_IMP_FINITE]);

val BASIS_SUBSPACE_EXISTS = prove
 (`!s:real['n]->bool.
        subspace s
        ==> ?b. FINITE b /\
                b SUBSET s /\
                independent b /\
                (span b = s) /\
                (b HAS_SIZE dim s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real['n]->bool` BASIS_EXISTS) THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  PROVE_TAC[SPAN_EQ_SELF, SPAN_MONO, INDEPENDENT_IMP_FINITE]);

(* ------------------------------------------------------------------------- *)
(* Consequences of independence or spanning for cardinality.                 *)
(* ------------------------------------------------------------------------- *)

val INDEPENDENT_CARD_LE_DIM = prove
 (`!v b:real['n]->bool.
        b SUBSET v /\ independent b ==> FINITE b /\ CARD(b) <= dim v`,
  PROVE_TAC[BASIS_EXISTS, INDEPENDENT_SPAN_BOUND, HAS_SIZE_def, SUBSET_TRANS]);

val SPAN_CARD_GE_DIM = prove
 (`!v b:real['n]->bool.
        v SUBSET (span b) /\ FINITE b ==> dim(v) <= CARD(b)`,
  PROVE_TAC[BASIS_EXISTS, INDEPENDENT_SPAN_BOUND, HAS_SIZE_def, SUBSET_TRANS]);

(* ------------------------------------------------------------------------- *)
(* Converses to those.                                                       *)
(* ------------------------------------------------------------------------- *)

val CARD_GE_DIM_INDEPENDENT = prove
 (`!v b:real['n]->bool.
        b SUBSET v /\ independent b /\ dim v <= CARD(b)
        ==> v SUBSET (span b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a:real['n]. ~(a IN v /\ ~(a IN span b))` MP_TAC THENL
   [ALL_TAC, PROVE_TAC[SUBSET_DEF]] THEN
  X_GEN_TAC `a:real['n]` THEN STRIP_TAC THEN
  SUBGOAL_THEN `independent((a:real['n]) INSERT b)` ASSUME_TAC THENL
   [PROVE_TAC[INDEPENDENT_INSERT], ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real['n]->bool`, `(a:real['n]) INSERT b`]
                INDEPENDENT_CARD_LE_DIM) THEN
  ASM_SIMP_TAC bool_ss[INSERT_SUBSET, CARD_CLAUSES, INDEPENDENT_BOUND] THEN
  PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF, prove(
    `x <= y ==> ~(SUC y <= x)`, ARITH_TAC)]);

val CARD_LE_DIM_SPANNING = prove
 (`!v b:real['n]->bool.
        v SUBSET (span b) /\ FINITE b /\ CARD(b) <= dim v
        ==> independent b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[independent_def, dependent_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real['n]` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `dim(v:real['n]->bool) <= CARD(b DELETE (a:real['n]))` MP_TAC THENL
   [ALL_TAC,
    ASM_SIMP_TAC bool_ss[CARD_DELETE] THEN MATCH_MP_TAC
     (prove(`b:num <= n /\ ~(b = 0) ==> ~(n <= b - 1)`, ARITH_TAC)) THEN
    ASM_SIMP_TAC bool_ss[CARD_EQ_0] THEN PROVE_TAC[MEMBER_NOT_EMPTY]] THEN
  MATCH_MP_TAC SPAN_CARD_GE_DIM THEN ASM_SIMP_TAC bool_ss[FINITE_DELETE] THEN
  REWRITE_TAC[SUBSET_DEF] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SPAN_TRANS THEN EXISTS_TAC `a:real['n]` THEN
  ASM_SIMP_TAC bool_ss[INSERT_DELETE] THEN
  PROVE_TAC[SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* More general size bound lemmas.                                           *)
(* ------------------------------------------------------------------------- *)

val SPANS_IMAGE = prove
 (`!f b v. linear f /\ v SUBSET (span b)
           ==> (IMAGE f v) SUBSET span(IMAGE f b)`,
  SIMP_TAC bool_ss[SPAN_LINEAR_IMAGE, IMAGE_SUBSET]);

(* ------------------------------------------------------------------------- *)
(* Relation between bases and injectivity/surjectivity of map.               *)
(* ------------------------------------------------------------------------- *)

val SPANNING_SURJECTIVE_IMAGE = prove
 (`!f:real['m]->real['n] s.
        UNIV SUBSET (span s) /\ linear f /\ (!y. ?x. f(x) = y)
        ==> UNIV SUBSET span(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE (f:real['m]->real['n]) UNIV` THEN
  ASM_SIMP_TAC bool_ss[SPANS_IMAGE] THEN
  REWRITE_TAC[SUBSET_DEF, IN_UNIV, IN_IMAGE] THEN PROVE_TAC[]);

val INDEPENDENT_INJECTIVE_IMAGE_GEN = prove
 (`!f:real['m]->real['n] s.
        independent s /\ linear f /\
        (!x y. x IN span s /\ y IN span s /\ (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[independent_def, DEPENDENT_EXPLICIT] THEN
  REWRITE_TAC[CONJ_ASSOC, FINITE_SUBSET_IMAGE] THEN
  SIMP_TAC bool_ss[PROVE[]
     ``(?s u. ((?t. p t /\ (s = f t)) /\ q s u) /\ r s u) <=>
      (?t u. p t /\ q (f t) u /\ r (f t) u)``] THEN
  SIMP_TAC bool_ss[EXISTS_IN_IMAGE, GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real['m]->bool`, `u:real['n]->real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`t:real['m]->bool`, `(u:real['n]->real) o (f:real['m]->real['n])`] THEN
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
    PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF]]);

val INDEPENDENT_INJECTIVE_IMAGE = prove
 (`!f:real['m]->real['n] s.
        independent s /\ linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> independent (IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE_GEN THEN
  PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* We can extend a linear basis-basis injection to the whole set.            *)
(* ------------------------------------------------------------------------- *)

val LINEAR_INDEP_IMAGE_LEMMA = prove
 (`!f b. linear(f:real['m]->real['n]) /\
         FINITE b /\
         independent (IMAGE f b) /\
         (!x y. x IN b /\ y IN b /\ (f x = f y) ==> (x = y))
         ==> !x. x IN span b ==> (f(x) = VECTOR_0) ==> (x = VECTOR_0)`,
  SIMP_TAC bool_ss[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV) empty_rewrites[AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL [SIMP_TAC bool_ss[IN_SING, SPAN_EMPTY], ALL_TAC] THEN
  X_GEN_TAC `b:real['m]->bool` THEN STRIP_TAC THEN
  X_GEN_TAC `a:real['m]` THEN STRIP_TAC THEN Q.PAT_ASSUM `$==> X Y` MP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [PROVE_TAC[INDEPENDENT_MONO, IMAGE_CLAUSES, SUBSET_DEF, IN_INSERT],
    ALL_TAC] THEN
  DISCH_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real['m]` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:real['m]`, `(a:real['m]) INSERT b`, `x:real['m]`]
    SPAN_BREAKDOWN) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  SIMP_TAC bool_ss[ASSUME ``~((a:real['m]) IN b)``, prove(
    `~(a IN b) ==> ((a INSERT b) DELETE a = b)`,
	REWRITE_TAC[DELETE_INSERT, DELETE_NON_ELEMENT])] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real['m]->real['n])(x - k * a) IN span(IMAGE f b)` MP_TAC THENL
   [PROVE_TAC[SPAN_LINEAR_IMAGE, IN_IMAGE], ALL_TAC] THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
  FIRST_ASSUM(fn th => REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH ``VECTOR_0 - k * x = (-k) * x``] THEN
  ASM_CASES_TAC `k = &0` THENL
   [PROVE_TAC[VECTOR_ARITH ``x:real['n] - &0 * y = x``], ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC ``-inv(k)`` o MATCH_MP SPAN_MUL) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC, REAL_MUL_LNEG, REAL_MUL_RNEG] THEN
  SIMP_TAC bool_ss[REAL_NEGNEG, REAL_MUL_LINV, ASSUME ``~(k = &0)``] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I empty_rewrites[independent_def]) THEN
  SIMP_TAC bool_ss[dependent_def, NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC ``(f:real['m]->real['n]) a``) THEN
  SUBGOAL_THEN
   `IMAGE (f:real['m]->real['n]) (a INSERT b) DELETE f a =
    IMAGE f ((a INSERT b) DELETE a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION, IN_IMAGE, IN_DELETE, IN_INSERT] THEN
    PROVE_TAC[IN_INSERT],
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DELETE_INSERT] THEN
  SIMP_TAC bool_ss[prove(`~(a IN b) ==> (b DELETE a = b)`, REWRITE_TAC[DELETE_NON_ELEMENT]),
           ASSUME ``~(a:real['m] IN b)``] THEN
  SIMP_TAC bool_ss[IMAGE_CLAUSES, IN_INSERT]);


(* ------------------------------------------------------------------------- *)
(* We can extend a linear mapping from basis.                                *)
(* ------------------------------------------------------------------------- *)

val LINEAR_INDEPENDENT_EXTEND_LEMMA = prove
 (`!f b. FINITE b
         ==> independent b
             ==> ?g:real['m]->real['n].
                        (!x y. x IN span b /\ y IN span b
                                ==> (g(x + y) = g(x) + g(y))) /\
                        (!x c. x IN span b ==> (g(c * x) = c * g(x))) /\
                        (!x. x IN b ==> (g x = f x))`,
  GEN_TAC THEN HO_MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY, INDEPENDENT_INSERT] THEN CONJ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `(\x. VECTOR_0):real['m]->real['n]` THEN
    SIMP_TAC bool_ss[SPAN_EMPTY] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC,
    ALL_TAC] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real['m]->bool`, `a:real['m]`] THEN
  DISCH_THEN(fn th => REPEAT STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `h = \z:real['m]. @k. (z - k * a) IN span b` THEN
  SUBGOAL_THEN `!z:real['m]. z IN span(a INSERT b)
                    ==> (z - h(z) * a) IN span(b) /\
                        !k. (z - k * a) IN span(b) ==> (k = h(z))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [UNABBREV_TAC `h` THEN BETA_TAC THEN CONV_TAC SELECT_CONV THEN
      PROVE_TAC[SPAN_BREAKDOWN_EQ],
      ALL_TAC] THEN
    SIMP_TAC bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP SPAN_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH ``(z - a * v:real['m]) - (z - b * v) = (b - a) * v``] THEN
    ASM_CASES_TAC `k = (h:real['m]->real) z` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC ``inv(k - (h:real['m]->real) z)`` o
               MATCH_MP SPAN_MUL) THEN
    ASM_SIMP_TAC bool_ss[REAL_MUL_LINV, VECTOR_MUL_ASSOC, REAL_SUB_0] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID],
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO, Once FORALL_AND_THM] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\z:real['m]. h(z) * (f:real['m]->real['n])(a) + g(z - h(z) * a)` THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real['m]`, `y:real['m]`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real['m]->real)(x + y) = h(x) + h(y)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       ``(x + y) - (k + l) * a:real['m] = (x - k * a) + (y - l * a)``] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_ADD THEN ASM_SIMP_TAC bool_ss[],
      ALL_TAC] THEN
    ASM_SIMP_TAC bool_ss[VECTOR_ARITH
       ``(x + y) - (k + l) * a:real['m] = (x - k * a) + (y - l * a)``] THEN
    VECTOR_ARITH_TAC,
    MAP_EVERY X_GEN_TAC [`x:real['m]`, `c:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h:real['m]->real)(c * x:real['m]) = c * h(x)` ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH
       ``c * x - (c * k) * a:real['m] = c * (x - k * a)``] THEN
      CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN ASM_SIMP_TAC bool_ss[],
      ALL_TAC] THEN
    ASM_SIMP_TAC bool_ss[VECTOR_ARITH
       ``c * x - (c * k) * a:real['m] = c * (x - k * a)``] THEN
    VECTOR_ARITH_TAC,
    ALL_TAC] THEN
  X_GEN_TAC `x:real['m]` THEN BETA_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC) THENL
   [SUBGOAL_THEN `&1 = h(a:real['m])` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM MATCH_MP_TAC, ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH ``a - &1 * a = VECTOR_0``, SPAN_0] THENL
     [PROVE_TAC[SPAN_SUPERSET, SUBSET_DEF, IN_INSERT], ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`VECTOR_0:real['m]`, `VECTOR_0:real['m]`]) THEN
    REWRITE_TAC[SPAN_0, VECTOR_ADD_LID] THEN
    REWRITE_TAC[VECTOR_ARITH ``(a = a + a) <=> (a = VECTOR_0)``] THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC,
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 = h(x:real['m])` (SUBST1_TAC o SYM) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC, ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LID, VECTOR_MUL_LZERO, VECTOR_SUB_RZERO] THEN
  PROVE_TAC[SUBSET_DEF, IN_INSERT, SPAN_SUPERSET]);

val LINEAR_INDEPENDENT_EXTEND = prove
 (`!f b. independent b
         ==> ?g:real['m]->real['n]. linear g /\ (!x. x IN b ==> (g x = f x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real['m]->bool`, `(UNIV:real['m]->bool)`]
           MAXIMAL_INDEPENDENT_SUBSET_EXTEND) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV, UNIV_SUBSET] THEN
  REWRITE_TAC[EXTENSION, IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real['m]->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real['m]->real['n]`, `c:real['m]->bool`]
    LINEAR_INDEPENDENT_EXTEND_LEMMA) THEN
  ASM_SIMP_TAC bool_ss[INDEPENDENT_BOUND, linear_def] THEN
  PROVE_TAC[SUBSET_DEF]);

(* ------------------------------------------------------------------------- *)
(* Linear functions are equal on a subspace if they are on a spanning set.   *)
(* ------------------------------------------------------------------------- *)

val SUBSPACE_KERNEL = prove
 (`!f. linear f ==> subspace {x | f(x) = VECTOR_0}`,
  SIMP_TAC bool_ss[subspace_def, GSPEC_ETA, IN_ABS] THEN
  SIMP_TAC bool_ss[LINEAR_ADD, LINEAR_CMUL, VECTOR_ADD_LID, VECTOR_MUL_RZERO, LINEAR_0]);

val LINEAR_EQ_0_SPAN = prove
 (`!f:real['m]->real['n] b.
        linear f /\ (!x. x IN b ==> (f(x) = VECTOR_0))
        ==> !x. x IN span(b) ==> (f(x) = VECTOR_0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC SPAN_INDUCT THEN ASM_SIMP_TAC bool_ss[IN_ABS] THEN
  MP_TAC(ISPEC `f:real['m]->real['n]` SUBSPACE_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC bool_ss[EXTENSION, GSPEC_ETA, IN_ABS]);

val LINEAR_EQ_0 = prove
 (`!f b s. linear f /\ s SUBSET (span b) /\ (!x. x IN b ==> (f(x) = VECTOR_0))
           ==> !x. x IN s ==> (f(x) = VECTOR_0)`,
  PROVE_TAC[LINEAR_EQ_0_SPAN, SUBSET_DEF]);

val LINEAR_EQ = prove
 (`!f g b s. linear f /\ linear g /\ s SUBSET (span b) /\
             (!x. x IN b ==> (f(x) = g(x)))
              ==> !x. x IN s ==> (f(x) = g(x))`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  STRIP_TAC THEN HO_MATCH_MP_TAC LINEAR_EQ_0 THEN
  METIS_TAC[LINEAR_COMPOSE_SUB]);

val LINEAR_EQ_STDBASIS = prove
 (`!f:real['m]->real['n] g.
        linear f /\ linear g /\
        (!i. i < dimindex(:'m)
             ==> (f(basis i) = g(basis i)))
        ==> (f = g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN UNIV ==> ((f:real['m]->real['n]) x = g x)`
   (fn th => MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM, IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_EQ THEN
  EXISTS_TAC `{basis i :real['m] | i < dimindex(:'m)}` THEN
  ASM_SIMP_TAC bool_ss[SPAN_STDBASIS, SUBSET_REFL] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Detailed theorems about left and right invertibility in general case.     *)
(* ------------------------------------------------------------------------- *)

val LEFT_INVERTIBLE_TRANSP = prove
 (`!A:real['n]['m].
    (?B:real['n]['m]. B ** TRANSP A = MAT 1) <=> (?B:real['m]['n]. A ** B = MAT 1)`,
  PROVE_TAC[MATRIX_TRANSP_MUL, TRANSP_MAT, TRANSP_TRANSP]);

val RIGHT_INVERTIBLE_TRANSP = prove
 (`!A:real['n]['m].
    (?B:real['n]['m]. TRANSP A ** B = MAT 1) <=> (?B:real['m]['n]. B ** A = MAT 1)`,
  PROVE_TAC[MATRIX_TRANSP_MUL, TRANSP_MAT, TRANSP_TRANSP]);

val LINEAR_INJECTIVE_LEFT_INVERSE = prove
 (`!f:real['m]->real['n].
        linear f /\ (!x y. (f x = f y) ==> (x = y))
        ==> ?g. linear g /\ (g o f = I)`,
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?h. linear(h:real['n]->real['m]) /\
        !x. x IN IMAGE (f:real['m]->real['n])
               {basis i | i < dimindex(:'m)} ==> (h x = g x)`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    MATCH_MP_TAC INDEPENDENT_INJECTIVE_IMAGE THEN
    PROVE_TAC[INJECTIVE_LEFT_INVERSE, INDEPENDENT_STDBASIS],
    HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real['n]->real['m]` THEN
    ASM_SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN
	CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC bool_ss[I_THM, LINEAR_COMPOSE, o_THM] THEN
    SIMP_TAC bool_ss[I_DEF, K_DEF, S_DEF, LINEAR_ID] THEN
	PROVE_TAC[]]);

val LINEAR_SURJECTIVE_RIGHT_INVERSE = prove
 (`!f:real['m]->real['n].
        linear f /\ (!y. ?x. f x = y) ==> ?g. linear g /\ (f o g = I)`,
  REWRITE_TAC[SURJECTIVE_RIGHT_INVERSE] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `?h. linear(h:real['n]->real['m]) /\
        !x. x IN {basis i | i < dimindex(:'n)} ==> (h x = g x)`
  MP_TAC THENL
   [MATCH_MP_TAC LINEAR_INDEPENDENT_EXTEND THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS],
    HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real['n]->real['m]` THEN
    ASM_SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN
	CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LINEAR_EQ_STDBASIS THEN
    ASM_SIMP_TAC bool_ss[I_THM, LINEAR_COMPOSE, o_THM] THEN
    SIMP_TAC bool_ss[I_DEF, K_DEF, S_DEF, LINEAR_ID] THEN
	PROVE_TAC[]]);

val MATRIX_LEFT_INVERTIBLE_INJECTIVE = prove
 (`!A:real['n]['m].
        (?B:real['m]['n]. B ** A = MAT 1) <=>
        !x y:real['n]. (A ** x = A ** y) ==> (x = y)`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN REPEAT GEN_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM ``\x:real['m]. (B:real['m]['n]) ** x``) THEN
    BETA_TAC THEN ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    DISCH_TAC THEN MP_TAC(ISPEC
     `\x:real['n]. (A:real['n]['m]) ** x` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_SIMP_TAC bool_ss[MATRIX_VECTOR_MUL_LINEAR, FUN_EQ_THM, I_THM, o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real['m]->real['n]` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(g):real['m]['n]` THEN
    REWRITE_TAC[MATRIX_EQ, MATRIX_VECTOR_MUL_LID] THEN
    PROVE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS]]);

val MATRIX_LEFT_INVERTIBLE_KER = prove
 (`!A:real['n]['m].
        (?B:real['m]['n]. B ** A = MAT 1) <=> !x. (A ** x = VECTOR_0) ==> (x = VECTOR_0)`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INJECTIVE] THEN
  HO_MATCH_MP_TAC LINEAR_INJECTIVE_0 THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]);

val MATRIX_RIGHT_INVERTIBLE_SURJECTIVE = prove
 (`!A:real['n]['m].
        (?B:real['m]['n]. A ** B = MAT 1) <=> !y. ?x. A ** x = y`,
  GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN X_GEN_TAC `y:real['m]` THEN
    EXISTS_TAC `(B:real['m]['n]) ** (y:real['m])` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    DISCH_TAC THEN MP_TAC(ISPEC
     `\x:real['n]. (A:real['n]['m]) ** x` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
    ASM_SIMP_TAC bool_ss[MATRIX_VECTOR_MUL_LINEAR, FUN_EQ_THM, I_THM, o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real['m]->real['n]` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `matrix(g):real['m]['n]` THEN
    REWRITE_TAC[MATRIX_EQ, MATRIX_VECTOR_MUL_LID] THEN
    PROVE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_WORKS]]);

val MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS = prove
 (`!A:real['n]['m]. (?B:real['m]['n]. B ** A = MAT 1) <=>
                !c. (VSUM(count(dimindex(:'n))) (\i. c(i) * COLUMN i A) = VECTOR_0) ==>
                    !i. i < dimindex(:'n) ==> (c(i) = &0)`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_KER, MATRIX_MUL_VSUM] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `c:num->real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC ``(FCP i. c(i)):real['n]``),
    X_GEN_TAC `x:real['n]` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC ``\i. (x:real['n]) ' i``) THEN BETA_TAC] THEN
  SUBGOAL_THEN `VSUM (count (dimindex (:'n))) (\i. (FCP i. c i):real['n] ' i * COLUMN i A) =
    VSUM (count (dimindex (:'n))) (\i. c i * COLUMN i A)` ASSUME_TAC THENL
    [MATCH_MP_TAC VSUM_EQ THEN SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT], ALL_TAC,
	 MATCH_MP_TAC VSUM_EQ THEN SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT], ALL_TAC] THEN
  SRW_TAC[FCP_ss][VEC_0_COMPONENT]);

val MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS = prove
 (`!A:real['n]['m]. (?B:real['m]['n]. A ** B = MAT 1) <=>
                !c. (VSUM(count(dimindex(:'m))) (\i. c(i) * ROW i A) = VECTOR_0) ==>
                    !i. i < dimindex(:'m) ==> (c(i) = &0)`,
  ONCE_REWRITE_TAC[GSYM LEFT_INVERTIBLE_TRANSP] THEN
  REWRITE_TAC[MATRIX_LEFT_INVERTIBLE_INDEPENDENT_COLUMNS] THEN
  SUBGOAL_THEN `!A:real['n]['m] c:num->real.
		VSUM (count (dimindex (:'m))) (\i. c i * COLUMN i (TRANSP A))=
		VSUM (count (dimindex (:'m))) (\i. c i * ROW i A)` ASSUME_TAC THENL
	[REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN SRW_TAC[FCP_ss][COLUMN_TRANSP], ALL_TAC] THEN
  ASM_REWRITE_TAC[]);

val MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS = prove
 (`!A:real['n]['m]. (?B:real['m]['n]. A ** B = MAT 1) <=> (span(COLUMNS A) = (UNIV:real['m]->bool))`,
  GEN_TAC THEN REWRITE_TAC[MATRIX_RIGHT_INVERTIBLE_SURJECTIVE] THEN
  REWRITE_TAC[MATRIX_MUL_VSUM, EXTENSION, IN_UNIV] THEN
  AP_TERM_TAC THEN SIMP_TAC bool_ss[FUN_EQ_THM] THEN X_GEN_TAC `y:real['m]` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real['n]` (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC SPAN_VSUM THEN SIMP_TAC bool_ss[FINITE_COUNT, IN_COUNT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC(CONJUNCT1 SPAN_CLAUSES) THEN
    REWRITE_TAC[COLUMNS_DEF] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[],
    ALL_TAC] THEN
  SPEC_TAC(`y:real['m]`,`y:real['m]`) THEN HO_MATCH_MP_TAC SPAN_INDUCT_ALT THEN
  CONJ_TAC THENL
   [EXISTS_TAC `VECTOR_0 :real['n]` THEN
    MATCH_MP_TAC EQ_TRANS THEN
	EXISTS_TAC `VSUM (count (dimindex (:'n))) (\i.VECTOR_0 :real['m])` THEN
	CONJ_TAC THENL[MATCH_MP_TAC VSUM_EQ, ALL_TAC] THEN
    SRW_TAC[FCP_ss][VEC_0_COMPONENT, VECTOR_MUL_LZERO, VSUM_0],
	ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real`, `y1:real['m]`, `y2:real['m]`] THEN
  REWRITE_TAC[COLUMNS_DEF] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `x:real['n]` (SUBST1_TAC o SYM))) THEN
  EXISTS_TAC `(FCP j. if j = i then c + (x:real['n]) ' i else x ' j):real['n]` THEN
  SUBGOAL_THEN `count (dimindex (:'n)) = i INSERT (count (dimindex (:'n)) DELETE i)`
  SUBST1_TAC THENL [PROVE_TAC[INSERT_DELETE, IN_COUNT], ALL_TAC] THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_DELETE, FINITE_COUNT, IN_DELETE] THEN
  ASM_SIMP_TAC bool_ss[FCP_BETA, VECTOR_ADD_RDISTRIB, VECTOR_ADD_ASSOC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  SIMP_TAC bool_ss[FINITE_DELETE, IN_DELETE, FINITE_COUNT, FCP_BETA, IN_COUNT]);

val MATRIX_LEFT_INVERTIBLE_SPAN_ROWS = prove
 (`!A:real['n]['m]. (?B:real['m]['n]. B ** A = MAT 1) <=> (span(ROWS A) = (UNIV:real['n]->bool))`,
  PROVE_TAC[RIGHT_INVERTIBLE_TRANSP, COLUMNS_TRANSP,
            MATRIX_RIGHT_INVERTIBLE_SPAN_COLUMNS]);

(* ------------------------------------------------------------------------- *)
(* An injective map real^N->real^N is also surjective.                       *)
(* ------------------------------------------------------------------------- *)

val LINEAR_INJECTIVE_IMP_SURJECTIVE = prove
 (`!f:real['n]->real['n].
        linear f /\ (!x y. (f(x) = f(y)) ==> (x = y))
        ==> !y. ?x. f(x) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(UNIV:real['n]->bool)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV, HAS_SIZE_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real['n]->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIV SUBSET span(IMAGE (f:real['n]->real['n]) b)` MP_TAC THENL
   [MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    PROVE_TAC[INDEPENDENT_INJECTIVE_IMAGE, LESS_EQ_REFL,
              SUBSET_UNIV, CARD_IMAGE_INJ],
    ASM_SIMP_TAC bool_ss[SPAN_LINEAR_IMAGE] THEN
    PROVE_TAC[SUBSET_DEF, IN_IMAGE, IN_UNIV]]);

(* ------------------------------------------------------------------------- *)
(* And vice versa.                                                           *)
(* ------------------------------------------------------------------------- *)

val LINEAR_SURJECTIVE_IMP_INJECTIVE = prove
 (`!f:real['n]->real['n].
        linear f /\ (!y. ?x. f(x) = y)
        ==> !x y. (f(x) = f(y)) ==> (x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(UNIV:real['n]->bool)` BASIS_EXISTS) THEN
  REWRITE_TAC[SUBSET_UNIV, HAS_SIZE_def] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real['n]->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN span b ==> ((f:real['n]->real['n]) x = VECTOR_0) ==> (x = VECTOR_0)`
   (fn th => PROVE_TAC[th, LINEAR_INJECTIVE_0, SUBSET_DEF, IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_INDEP_IMAGE_LEMMA THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_DIM_SPANNING THEN
    EXISTS_TAC `(UNIV:real['n]->bool)` THEN
    ASM_SIMP_TAC bool_ss[IMAGE_FINITE, SPAN_LINEAR_IMAGE] THEN
    REWRITE_TAC[SUBSET_DEF, IN_UNIV, IN_IMAGE] THEN
    PROVE_TAC[CARD_IMAGE_LE, SUBSET_DEF, IN_UNIV],
    ALL_TAC] THEN
  SUBGOAL_THEN `dim(UNIV:real['n]->bool) <= CARD(IMAGE (f:real['n]->real['n]) b)`
  MP_TAC THENL
   [MATCH_MP_TAC SPAN_CARD_GE_DIM THEN
    ASM_SIMP_TAC bool_ss[SPAN_LINEAR_IMAGE, IMAGE_FINITE] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real['n]->real['n]) UNIV` THEN
    ASM_SIMP_TAC bool_ss[IMAGE_SUBSET] THEN
    ASM_REWRITE_TAC[SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN PROVE_TAC[],
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o ISPEC `f:real['n]->real['n]` o
                MATCH_MP CARD_IMAGE_LE) THEN
  ASM_REWRITE_TAC[AND_IMP_INTRO] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`b:real['n]->bool`, `IMAGE (f:real['n]->real['n]) b`, `f:real['n]->real['n]`]
   SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC bool_ss[IMAGE_FINITE, INDEPENDENT_BOUND, SUBSET_REFL, LESS_EQUAL_ANTISYM] THEN
  SIMP_TAC bool_ss[FORALL_IN_IMAGE] THEN PROVE_TAC[]);

val LINEAR_SURJECTIVE_IFF_INJECTIVE = prove
 (`!f:real['n]->real['n].
      linear f ==> ((!y. ?x. f x = y) <=> (!x y. (f x = f y) ==> (x = y)))`,
  PROVE_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE,
            LINEAR_SURJECTIVE_IMP_INJECTIVE]);

(* ------------------------------------------------------------------------- *)
(* Hence either is enough for isomorphism.                                   *)
(* ------------------------------------------------------------------------- *)

val LEFT_RIGHT_INVERSE_EQ = prove
 (`!f:'a->'a g h. (f o g = I) /\ (g o h = I) ==> (f = h)`,
  PROVE_TAC[o_ASSOC, I_o_ID]);

val ISOMORPHISM_EXPAND = prove
 (`!f g. (f o g = I) /\ (g o f = I) <=> (!x. f(g x) = x) /\ (!x. g(f x) = x)`,
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM]);

val LINEAR_INJECTIVE_ISOMORPHISM = prove
 (`!f:real['n]->real['n].
        linear f /\ (!x y. (f x = f y) ==> (x = y))
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(ISPEC `f:real['n]->real['n]` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(ISPEC `f:real['n]->real['n]` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(ISPEC `f:real['n]->real['n]` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  ASM_SIMP_TAC bool_ss[] THEN PROVE_TAC[LEFT_RIGHT_INVERSE_EQ]);

val LINEAR_SURJECTIVE_ISOMORPHISM = prove
 (`!f:real['n]->real['n].
        linear f /\ (!y. ?x. f x = y)
        ==> ?f'. linear f' /\ (!x. f'(f x) = x) /\ (!x. f(f' x) = x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM ISOMORPHISM_EXPAND] THEN
  MP_TAC(ISPEC `f:real['n]->real['n]` LINEAR_SURJECTIVE_RIGHT_INVERSE) THEN
  MP_TAC(ISPEC `f:real['n]->real['n]` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  MP_TAC(ISPEC `f:real['n]->real['n]` LINEAR_SURJECTIVE_IMP_INJECTIVE) THEN
  ASM_SIMP_TAC bool_ss[] THEN PROVE_TAC[LEFT_RIGHT_INVERSE_EQ]);

(* ------------------------------------------------------------------------- *)
(* Left and right inverses are the same for R^N->R^N.                        *)
(* ------------------------------------------------------------------------- *)

val LINEAR_INVERSE_LEFT = prove
 (`!f:real['n]->real['n] f'.
        linear f /\ linear f' ==> ((f o f' = I) <=> (f' o f = I))`,
  SUBGOAL_THEN
   `!f:real['n]->real['n] f'.
        linear f /\ linear f' /\ (f o f' = I) ==> (f' o f = I)`
   (fn th => PROVE_TAC[th]) THEN
  REWRITE_TAC[FUN_EQ_THM, o_THM, I_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real['n]->real['n]` LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  PROVE_TAC[]);

val MATRIX_LEFT_RIGHT_INVERSE = prove
 (`!A:real['n]['n] A':real['n]['n]. (A ** A' = MAT 1) <=> (A' ** A = MAT 1)`,
  SUBGOAL_THEN
    `!A:real['n]['n] A':real['n]['n]. (A ** A' = MAT 1) ==> (A' ** A = MAT 1)`
    (fn th => PROVE_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real['n]. (A:real['n]['n]) ** x`
    LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  SIMP_TAC bool_ss[MATRIX_VECTOR_MUL_LINEAR] THEN
  SUBGOAL_THEN `!y:real['n]. ?x. (A:real['n]['n]) ** x = y` ASSUME_TAC THENL
   [X_GEN_TAC `x:real['n]` THEN EXISTS_TAC `(A':real['n]['n]) ** (x:real['n])` THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `f':real['n]->real['n]` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `matrix (f':real['n]->real['n]) ** (A:real['n]['n]) = MAT 1`
  MP_TAC THENL
   [ASM_SIMP_TAC bool_ss[MATRIX_EQ, MATRIX_WORKS, GSYM MATRIX_VECTOR_MUL_ASSOC,
                 MATRIX_VECTOR_MUL_LID],
    ALL_TAC] THEN
  DISCH_THEN(fn th => ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o AP_TERM ``(\m:real['n]['n]. m ** (A':real['n]['n]))``) THEN
  SIMP_TAC bool_ss[MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_RID, MATRIX_MUL_LID] THEN PROVE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Invertibility of matrices and corresponding linear functions.             *)
(* ------------------------------------------------------------------------- *)

val MATRIX_LEFT_INVERTIBLE = prove
 (`!f:real['m]->real['n].
    linear f ==> ((?B:real['n]['m]. B ** matrix f = MAT 1) <=>
                  (?g. linear g /\ (g o f = I)))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `\y:real['n]. (B:real['n]['m]) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_SIMP_TAC bool_ss[FUN_EQ_THM, o_THM, I_THM, MATRIX_VECTOR_MUL_ASSOC,
                    MATRIX_VECTOR_MUL_LID],
    EXISTS_TAC `matrix(g:real['n]->real['m])` THEN
    ASM_SIMP_TAC bool_ss[GSYM MATRIX_COMPOSE, MATRIX_I]]);

val MATRIX_RIGHT_INVERTIBLE = prove
 (`!f:real['m]->real['n].
    linear f ==> ((?B:real['n]['m]. matrix f ** B = MAT 1) <=>
                  (?g. linear g /\ (f o g = I)))`,
  GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `\y:real['n]. (B:real['n]['m]) ** y` THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    FIRST_X_ASSUM(fn th => GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) empty_rewrites
                [MATCH_MP MATRIX_VECTOR_MUL th]) THEN
    ASM_SIMP_TAC bool_ss[FUN_EQ_THM, o_THM, I_THM, MATRIX_VECTOR_MUL_ASSOC,
                    MATRIX_VECTOR_MUL_LID],
    EXISTS_TAC `matrix(g:real['n]->real['m])` THEN
    ASM_SIMP_TAC bool_ss[GSYM MATRIX_COMPOSE, MATRIX_I]]);

val INVERTIBLE_LEFT_INVERSE = prove
 (`!A:real['n]['n]. invertible(A) <=> ?B:real['n]['n]. B ** A = MAT 1`,
  PROVE_TAC[invertible_def, MATRIX_LEFT_RIGHT_INVERSE]);

val INVERTIBLE_RIGHT_INVERSE = prove
 (`!A:real['n]['n]. invertible(A) <=> ?B:real['n]['n]. A ** B = MAT 1`,
  PROVE_TAC[invertible_def, MATRIX_LEFT_RIGHT_INVERSE]);

val MATRIX_INVERTIBLE = prove
 (`!f:real['n]->real['n].
        linear f
        ==> (invertible(matrix f) <=>
             ?g. linear g /\ (f o g = I) /\ (g o f = I))`,
  SIMP_TAC bool_ss[INVERTIBLE_LEFT_INVERSE, MATRIX_LEFT_INVERTIBLE] THEN
  PROVE_TAC[LINEAR_INVERSE_LEFT]);

val MATRIX_LINV_UNIQ = prove
 (`!(A B):real['n]['n]. (A ** B = MAT 1) ==> (A = MATRIX_INV B)`,
 METIS_TAC[MATRIX_RMUL_EQ, MATRIX_INV, INVERTIBLE_LEFT_INVERSE]);

val MATRIX_RINV_UNIQ = prove
 (`!(A B):real['n]['n]. (A ** B = MAT 1) ==> (B = MATRIX_INV A)`,
 METIS_TAC[MATRIX_LINV_UNIQ, MATRIX_INV_INV, INVERTIBLE_LEFT_INVERSE]);

