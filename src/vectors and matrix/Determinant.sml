(* ========================================================================= *)
(* Determinant and Matrix *)
(*      
It is translated from the corresponding code file of Harrision in Hol-Light.	            
AUTHORS  : (Copyright) Liming Li, Yong Guan and Zhiping Shi
             Beijing Engineering Research Center of High Reliable      
             Emmbedded System, Capital Normal University, China 
             		 
DATE  : 2011.12.08                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of determinant.                                                *)
(* ------------------------------------------------------------------------- *)

val DET_DEF = Define
 `DET(A:real['n]['n]) =
        SUM { p | p PERMUTES count(dimindex (:'n))}
            (\p. SIGN(p) * (PRODUCT (count(dimindex (:'n))) (\i. A ' i '(p i))))`;


val ALG_COMP_DEF = Define
 `(ALG_COMP:real['n]['n]-> num -> num -> real) A i j =
		DET ((FCP k l. if k = i then (if l = j then &1 else &0) else
				(if l = j then &0 else A ' k ' l)):real['n]['n])`;

(* ------------------------------------------------------------------------- *)
(* A few general lemmas we need below.                                       *)
(* ------------------------------------------------------------------------- *)

val IN_DIMINDEX_SWAP = prove
 (`!m n j. m < dimindex(:'n) /\ n < dimindex(:'n) /\ j < dimindex(:'n)
           ==> SWAP(m,n) j < dimindex(:'n)`,
  REWRITE_TAC[SWAP_DEF] THEN ARITH_TAC);

val FCP_BETA_PERM = prove
 (`!p i. p PERMUTES count(dimindex (:'n)) /\ i < dimindex(:'n)
         ==> (((FCP) g : 'a ** 'n) ' (p i) = g(p i))`,
  PROVE_TAC[FCP_BETA, PERMUTES_IN_IMAGE, IN_COUNT]);

(* ------------------------------------------------------------------------- *)
(* Basic determinant properties.                                             *)
(* ------------------------------------------------------------------------- *)

val DET_TRANSP = prove
 (`!A:real['n]['n]. DET (TRANSP A) = DET A`,
  GEN_TAC THEN REWRITE_TAC[DET_DEF] THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [SUM_PERMUTATIONS_INVERSE] THEN
  MATCH_MP_TAC SUM_EQ THEN
  SIMP_TAC bool_ss[FINITE_PERMUTATIONS, FINITE_COUNT] THEN X_GEN_TAC `p:num->num` THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN DISCH_TAC THEN BINOP_TAC THENL
   [PROVE_TAC[SIGN_INVERSE, PERMUTATION_PERMUTES, FINITE_COUNT],
    ALL_TAC] THEN
  FIRST_ASSUM(fn th => GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   empty_rewrites [GSYM(MATCH_MP PERMUTES_IMAGE th)]) THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `PRODUCT (count (dimindex(:'n)))
       ((\i. (TRANSP A:real['n]['n]) ' i ' (INVERSE p i)) o p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_IMAGE THEN
    PROVE_TAC[FINITE_COUNT, PERMUTES_INJECTIVE],
    MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[FINITE_COUNT, IN_COUNT] THEN
    SIMP_TAC bool_ss[TRANSP_DEF, FCP_BETA, o_THM] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PERMUTES_INVERSES_o) THEN
    SIMP_TAC bool_ss[FUN_EQ_THM, I_THM, o_THM] THEN STRIP_TAC THEN
    ASM_SIMP_TAC bool_ss[FCP_BETA_PERM, FCP_BETA]]);

val DET_LOWERTRIANGULAR = prove
 (`!A:real['n]['n].
       (!i j. i < dimindex(:'n) /\ j < dimindex(:'n) /\ i < j ==> (A ' i ' j = &0))
        ==> (DET(A) = PRODUCT (count (dimindex(:'n))) (\i. A ' i ' i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DET_DEF] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM {I}
     (\p. SIGN p * 
          PRODUCT (count (dimindex(:'n))) 
                (\i. (A:real['n]['n]) ' i ' (p i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[SUM_SING] THEN BETA_TAC THEN
    REWRITE_TAC[SIGN_I, REAL_MUL_LID, I_THM]] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  SIMP_TAC bool_ss[IN_SING, SUBSET_DEF] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PRODUCT_EQ_0_COUNT, REAL_ENTIRE, SIGN_NZ] THEN
  MP_TAC(SPECL [`p:num->num`, `count (dimindex(:'n))`] PERMUTES_NUMSET_LE) THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT, NOT_LESS]);

val DET_UPPERTRIANGULAR = prove
 (`!A:real['n]['n].
       (!i j. i < dimindex(:'n) /\ j < dimindex(:'n) /\ j < i ==> (A ' i ' j = &0))
        ==> (DET(A) = PRODUCT (count (dimindex(:'n))) (\i. A ' i ' i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DET_DEF] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM {I}
     (\p. SIGN p * 
          PRODUCT (count (dimindex(:'n))) 
                (\i. (A:real['n]['n]) ' i ' (p i)))` THEN
  CONJ_TAC THENL
   [ALL_TAC,
    REWRITE_TAC[SUM_SING] THEN BETA_TAC THEN
    REWRITE_TAC[SIGN_I, REAL_MUL_LID, I_THM]] THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  SIMP_TAC bool_ss[IN_SING, SUBSET_DEF] THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REWRITE_TAC[PERMUTES_I] THEN
  X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[PRODUCT_EQ_0_COUNT, REAL_ENTIRE, SIGN_NZ] THEN
  MP_TAC(SPECL [`p:num->num`, `count (dimindex(:'n))`] PERMUTES_NUMSET_GE) THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT, NOT_LESS]);

val DET_DIAGONAL = prove
 (`!A:real['n]['n].
    (!i j. i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j) ==> (A ' i ' j = &0))
        ==> (DET(A) = PRODUCT (count (dimindex(:'n))) (\i. A ' i ' i))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_LOWERTRIANGULAR THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[EQ_LESS_EQ, GSYM NOT_LESS]);

val DET_I = prove
 (`DET(MAT 1 :real['n]['n]) = &1`,
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `PRODUCT(count(dimindex(:'n)))(\i. MAT 1:real['n]['n] ' i ' i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DET_LOWERTRIANGULAR, MATCH_MP_TAC PRODUCT_EQ_1_COUNT] THEN
  SIMP_TAC bool_ss[MAT_DEF, FCP_BETA] THEN PROVE_TAC[EQ_LESS_EQ, NOT_LESS]);

val DET_0 = prove
 (`DET(MAT 0 :real['n]['n]) = &0`,
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `PRODUCT(count(dimindex(:'n)))(\i.MAT 0:real['n]['n] ' i ' i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DET_LOWERTRIANGULAR,
    REWRITE_TAC[PRODUCT_EQ_0_COUNT] THEN EXISTS_TAC `0`] THEN
  SIMP_TAC bool_ss[MAT_DEF, FCP_BETA, DIMINDEX_GE_1, LESS_EQ, GSYM ONE]);

val DET_PERMUTE_ROWS = prove
 (`!A:real['n]['n] p.
        p PERMUTES (count (dimindex(:'n)))
        ==> (DET(FCP i. A ' (p i)) = SIGN(p) * DET(A))`,
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
  (MATCH_MP PERMUTES_INVERSE (ASSUME ``p PERMUTES (count (dimindex(:'n)))``)) THEN
  DISCH_THEN(fn th => GEN_REWRITE_TAC LAND_CONV empty_rewrites
    [MATCH_MP PRODUCT_PERMUTE_COUNT th]) THEN
  MATCH_MP_TAC PRODUCT_EQ THEN REWRITE_TAC[IN_COUNT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
  SRW_TAC [FCP_ss][PERMUTES_INVERSE,PERMUTES_IN_COUNT] THEN
  PROVE_TAC[PERMUTES_INVERSES]);

val DET_PERMUTE_COLUMNS = prove
 (`!A:real['n]['n] p.
        p PERMUTES (count (dimindex(:'n)))
        ==> (DET((FCP i j. A ' i ' (p j)):real['n]['n]) = SIGN(p) * DET(A))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV) empty_rewrites [GSYM DET_TRANSP] THEN
  FIRST_ASSUM(fn th => ONCE_REWRITE_TAC
   [GSYM(MATCH_MP DET_PERMUTE_ROWS th)]) THEN
  GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC bool_ss[CART_EQ, TRANSP_DEF, FCP_BETA, FCP_BETA_PERM]);

val DET_IDENTICAL_ROWS = prove
 (`!A:real['n]['n] i j.
    i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j) /\ (ROW i A = ROW j A)
                    ==> (DET A = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:real['n]['n]`, `SWAP(i:num,j:num)`] DET_PERMUTE_ROWS) THEN
  ASM_SIMP_TAC bool_ss[PERMUTES_SWAP, IN_COUNT, SIGN_SWAP] THEN
  MATCH_MP_TAC(REAL_ARITH ``(a = b) ==> (b = - &1 * a) ==> (a = &0)``) THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THEN
  SIMP_TAC bool_ss[ROW_DEF, CART_EQ, FCP_BETA] THEN
  REWRITE_TAC[SWAP_DEF] THEN PROVE_TAC[]);

val DET_IDENTICAL_COLUMNS = prove
 (`!A:real['n]['n] i j.
  i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j) /\ (COLUMN i A = COLUMN j A)
                    ==> (DET A = &0)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DET_TRANSP] THEN
  MATCH_MP_TAC DET_IDENTICAL_ROWS THEN PROVE_TAC[ROW_TRANSP]);

val DET_ZERO_ROW = prove
 (`!A:real['n]['n] i.
       i < dimindex(:'n) /\ (ROW i A = VECTOR_0)  ==> (DET A = &0)`,
  SIMP_TAC bool_ss[DET_DEF, ROW_DEF, CART_EQ, FCP_BETA, VEC_0_COMPONENT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
  CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ENTIRE, SIGN_NZ] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC bool_ss[PRODUCT_EQ_0, FINITE_COUNT] THEN
  PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT]);

val DET_ZERO_COLUMN = prove
 (`!A:real['n]['n] i.
      i < dimindex(:'n) /\ (COLUMN i A = VECTOR_0)  ==> (DET A = &0)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM DET_TRANSP] THEN
  MATCH_MP_TAC DET_ZERO_ROW THEN PROVE_TAC[ROW_TRANSP]);

val DET_ROW_ADD = prove
 (`!a b c k.
          k < dimindex(:'n)
        ==> (DET ((FCP i. if i = k then a + b else c i):real['n]['n]) =
             DET ((FCP i. if i = k then a else c i):real['n]['n]) +
             DET ((FCP i. if i = k then b else c i):real['n]['n]))`,
  SIMP_TAC bool_ss[DET_DEF, GSYM SUM_ADD, FINITE_PERMUTATIONS, FINITE_COUNT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `p:num->num` THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  BETA_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `count(dimindex (:'n)) = k INSERT count (dimindex (:'n)) DELETE k`
  SUBST1_TAC THENL [PROVE_TAC[INSERT_DELETE, IN_COUNT], ALL_TAC] THEN
  SIMP_TAC bool_ss[PRODUCT_CLAUSES, FINITE_DELETE, FINITE_COUNT, IN_DELETE] THEN
  MATCH_MP_TAC(prove(
   `(c = a + b) /\ (y = x:real) /\ (z = x) ==> (c * x = a * y + b * z)`,
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  CONJ_TAC THENL
   [SRW_TAC[FCP_ss][FCP_BETA] THEN MATCH_MP_TAC VECTOR_ADD_COMPONENT THEN
    PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT],
    CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    SRW_TAC[FCP_ss][IN_DELETE, FINITE_DELETE, FINITE_COUNT]]);

val DET_ROW_MUL = prove
 (`!a b c k.
        k < dimindex(:'n)
        ==> (DET((FCP i. if i = k then c * a else b i):real['n]['n]) =
             c * DET((FCP i. if i = k then a else b i):real['n]['n]))`,
  SIMP_TAC bool_ss[DET_DEF, GSYM SUM_LMUL,FINITE_PERMUTATIONS, FINITE_COUNT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `p:num->num` THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  BETA_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `count(dimindex (:'n)) = k INSERT count (dimindex (:'n)) DELETE k`
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
    SRW_TAC[FCP_ss][IN_DELETE, FINITE_DELETE, FINITE_COUNT]]);

val DET_ROW_OPERATION = prove
 (`!A:real['n]['n] i.
        i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j)
        ==> (DET(FCP k. if k = i then ROW i A + c * ROW j A else ROW k A) =
             DET A)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC bool_ss[DET_ROW_ADD, DET_ROW_MUL] THEN
  MATCH_MP_TAC(prove(`(a = b) /\ (d = &0) ==> (a + c * d = b)`,
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN SRW_TAC [FCP_ss][] THEN
    COND_CASES_TAC THEN SRW_TAC [FCP_ss][ROW_DEF],
    MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
    MAP_EVERY EXISTS_TAC [`i:num`, `j:num`] THEN
    SRW_TAC [FCP_ss][ROW_DEF]]);

val DET_ROW_SPAN = prove
 (`!A:real['n]['n] i x.
        i < dimindex(:'n) /\
        x IN span {ROW j A |j < dimindex(:'n) /\ ~(j = i)}
        ==> (DET(FCP k. if k = i then ROW i A + x else ROW k A) =
             DET A)`,
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
     ``a + c * x + y:real['n] = (a + y) + c * x``] THEN
  ABBREV_TAC `z = ROW i (A:real['n]['n]) + y` THEN
  ASM_SIMP_TAC bool_ss[DET_ROW_MUL, DET_ROW_ADD] THEN
  MATCH_MP_TAC(prove(`(d = &0) ==> (a + c * d = a)`,
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)) THEN
  MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
  MAP_EVERY EXISTS_TAC [`i:num`, `j:num`] THEN
  SRW_TAC[FCP_ss][ROW_DEF]);

(* ------------------------------------------------------------------------- *)
(* May as well do this, though it's a bit unsatisfactory since it ignores    *)
(* exact duplicates by considering the rows/columns as a set.                *)
(* ------------------------------------------------------------------------- *)

val DET_DEPENDENT_ROWS = prove
 (`!A:real['n]['n]. dependent(ROWS A) ==> (DET A = &0)`,
  GEN_TAC THEN
  REWRITE_TAC[dependent_def, ROWS_DEF] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  SIMP_TAC bool_ss[GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `?i j. i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j) /\
          (ROW i (A:real['n]['n]) = ROW j A)`
  THENL [PROVE_TAC[DET_IDENTICAL_ROWS], ALL_TAC] THEN
  MP_TAC(SPECL [`A:real['n]['n]`, `i:num`, `~(ROW i (A:real['n]['n]))`]
    DET_ROW_SPAN) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[IMP_DISJ_THM] THEN DISJ1_TAC THEN MATCH_MP_TAC SPAN_NEG THEN
    Q.PAT_ASSUM `$IN X Y` MP_TAC THEN
    MATCH_MP_TAC(TAUT `(a = b) ==> a ==> b`) THEN
    REWRITE_TAC[SPECIFICATION] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION, IN_DELETE] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[],
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC DET_ZERO_ROW THEN
    EXISTS_TAC `i:num` THEN
    SRW_TAC[FCP_ss][ROW_DEF, VECTOR_ADD_COMPONENT, VECTOR_NEG_COMPONENT, VEC_0_COMPONENT]]);

val DET_DEPENDENT_COLUMNS = prove
 (`!A:real['n]['n]. dependent(COLUMNS A) ==> (DET A = &0)`,
  PROVE_TAC[DET_DEPENDENT_ROWS, ROWS_TRANSP, DET_TRANSP]);

(* ------------------------------------------------------------------------- *)
(* Multilinearity and the multiplication formula.                            *)
(* ------------------------------------------------------------------------- *)

val DET_LINEAR_ROW_VSUM = prove
 (`!a c s k.
         FINITE s /\ k < dimindex(:'n)
         ==> (DET((FCP i. if i = k then VSUM s a else c i):real['n]['n]) =
             SUM s
               (\j. DET((FCP i. if i = k then a(j) else c i):real['n]['n])))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES, SUM_CLAUSES, DET_ROW_ADD] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DET_ZERO_ROW THEN EXISTS_TAC `k:num` THEN
  SRW_TAC[FCP_ss][ROW_DEF, VEC_0_COMPONENT]);
  

val BOUNDED_FUNCTIONS_BIJECTIONS_1 = prove
 (`!p. p IN {(y,g) | y IN s /\
                     g IN {f | (!i. i < k ==> f i IN s) /\
                               (!i. ~(i < k) ==> (f i = i))}}
       ==> (\(y,g) i. if i = k then y else g(i)) p IN
             {f | (!i. i < SUC k ==> f i IN s) /\
                  (!i. ~(i < SUC k) ==> (f i = i))} /\
           ((\h. h(k),(\i. if i = k then i else h(i)))
            ((\(y,g) i. if i = k then y else g(i)) p) = p)`,
  SIMP_TAC std_ss[FORALL_PROD] THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN MAP_EVERY X_GEN_TAC [`y:num`, `h:num->num`] THEN
  REPEAT STRIP_TAC THENL
   [BETA_TAC THEN PROVE_TAC[LT],
    BETA_TAC THEN PROVE_TAC[LT],
    REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN
    PROVE_TAC[prove( `~(k:num < k)`, ARITH_TAC)]]);

val BOUNDED_FUNCTIONS_BIJECTIONS_2 = prove
 (`!h. h IN {f | (!i. i < SUC k ==> f i IN s) /\
                 (!i. ~(i < SUC k) ==> (f i = i))}
       ==> (\h. h(k),(\i. if i = k then i else h(i))) h IN
           {(y,g) | y IN s /\
                     g IN {f | (!i. i < k ==> f i IN s) /\
                               (!i. ~(i < k) ==> (f i = i))}} /\
           ((\(y,g) i. if i = k then y else g(i))
              ((\h. h(k),(\i. if i = k then i else h(i))) h) = h)`,
  CONV_TAC(REDEPTH_CONV GEN_BETA_CONV) THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN
  X_GEN_TAC `h:num->num` THEN REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC[`(h k):num`,`(\i. if i = k then i else h i):num->num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
	  [PROVE_TAC[LT],
	   BETA_TAC THEN PROVE_TAC[prove(`i < k ==> i< SUC k /\ ~(i = k)`, ARITH_TAC)],
	   BETA_TAC THEN PROVE_TAC[prove(`i< SUC k /\ ~(i = k) ==> i < k`, ARITH_TAC)]],
    REWRITE_TAC[FUN_EQ_THM] THEN BETA_TAC THEN PROVE_TAC[]]);

val FINITE_BOUNDED_FUNCTIONS = prove
 (`!s k:num. FINITE s
         ==> FINITE {f | (!i. i < k ==> f(i) IN s) /\
                         (!i. ~(i < k) ==> (f(i) = i))}`,
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
  SIMP_TAC bool_ss[FUN_EQ_THM] THEN PROVE_TAC[prove( `i:num < k ==> ~(i = k)`, ARITH_TAC),LT]);

val DET_LINEAR_ROWS_VSUM_LEMMA = prove
 (`!s k a c.
         FINITE s /\ k <= dimindex(:'n)
         ==> (DET((FCP i. if i < k then VSUM s (a i) else c i):real['n]['n]) =
              SUM {f | (!i. i < k ==> f(i) IN s) /\
                       !i. ~(i < k) ==> (f(i) = i)}
                  (\f. DET((FCP i. if i < k then a i (f i) else c i)
                          :real['n]['n])))`,
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ZERO_LESS_EQ, LT] THEN
    SIMP_TAC bool_ss[GSYM FUN_EQ_THM, GSPEC_EQ] THEN REWRITE_TAC[SUM_SING],
    ALL_TAC] THEN
  DISCH_TAC THEN Q.PAT_ASSUM `$==> X Y` MP_TAC THEN
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
  SRW_TAC[FCP_ss][] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  PROVE_TAC[LT, LT_REFL]);

val DET_LINEAR_ROWS_VSUM = prove
 (`!s k a.
         FINITE s
         ==> (DET((FCP i. VSUM s (a i)):real['n]['n]) =
              SUM {f | (!i. i < dimindex(:'n) ==> f(i) IN s) /\
                      !i. ~(i < dimindex(:'n)) ==> (f(i) = i)}
                 (\f. DET((FCP i. a i (f i)):real['n]['n])))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:num->bool`, `dimindex(:'n)`] DET_LINEAR_ROWS_VSUM_LEMMA) THEN
  ASM_SIMP_TAC bool_ss[LT_REFL, GSYM NOT_LESS, prove
   (`(FCP i. if i < dimindex(:'n) then x(i) else y(i)):real['n]['n] =
     (FCP i. x(i))`,
    SRW_TAC[FCP_ss][])]);

val MATRIX_MUL_VSUM_ALT = prove
 (`!A:real['n]['n] B:real['n]['n]. A ** B =
                  FCP i. VSUM (count(dimindex(:'n))) (\k. A ' i ' k * B ' k)`,
  SRW_TAC[FCP_ss][matrix_mul_def, VECTOR_MUL_COMPONENT, VSUM_COMPONENT]);

val DET_ROWS_MUL = prove
 (`!a c. DET((FCP i. c i * a i):real['n]['n]) =
         PRODUCT(count(dimindex(:'n))) (\i. c(i)) *
         DET((FCP i. a(i)):real['n]['n])`,
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
  SRW_TAC[FCP_ss][VECTOR_MUL_COMPONENT, PERMUTES_IN_COUNT]);

val DET_MUL = prove
 (`!A B:real['n]['n]. DET(A ** B) = DET(A) * DET(B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MATRIX_MUL_VSUM_ALT] THEN
  SIMP_TAC bool_ss[DET_LINEAR_ROWS_VSUM, FINITE_COUNT] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `SUM {p | p PERMUTES count(dimindex(:'n))}
            (\f. DET (FCP i. (A:real['n]['n]) ' i ' (f i) * (B:real['n]['n]) ' (f i)))` THEN
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
    MP_TAC(ISPECL [`count(dimindex(:'n))`, `f:num->num`]
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
      ASM_CASES_TAC ` x < dimindex(:'n)` THEN
      ASM_CASES_TAC ` y < dimindex(:'n)` THEN
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
   [MATCH_MP PRODUCT_PERMUTE_COUNT (ASSUME ``p PERMUTES count(dimindex(:'n))``)] THEN
  SIMP_TAC bool_ss[GSYM PRODUCT_MUL, FINITE_COUNT] THEN
  MATCH_MP_TAC PRODUCT_EQ_COUNT THEN
  SRW_TAC[FCP_ss][o_THM] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(A:real['n]['n]) ' i ' (p i) * (B:real['n]['n]) ' (p i) ' (q i)` THEN CONJ_TAC THENL
   [PROVE_TAC[VECTOR_MUL_COMPONENT, PERMUTES_IN_IMAGE, IN_COUNT],
    PROVE_TAC[PERMUTES_INVERSES]]);

(* ------------------------------------------------------------------------- *)
(* Relation to invertibility.                                                *)
(* ------------------------------------------------------------------------- *)

val INVERTIBLE_DET_NZ = prove
 (`!A:real['n]['n]. invertible(A) <=> ~(DET A = &0)`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC bool_ss[INVERTIBLE_RIGHT_INVERSE, GSYM LEFT_FORALL_IMP_THM] THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM ``DET:real['n]['n]->real``) THEN
    REWRITE_TAC[DET_MUL, DET_I] THEN PROVE_TAC[REAL_ENTIRE, REAL_10],
    ALL_TAC] THEN
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[INVERTIBLE_RIGHT_INVERSE] THEN
  REWRITE_TAC[MATRIX_RIGHT_INVERTIBLE_INDEPENDENT_ROWS] THEN
  SIMP_TAC bool_ss[NOT_FORALL_THM, NOT_IMP] THEN
  SIMP_TAC bool_ss[GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`, `i:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`A:real['n]['n]`, `i:num`, `~(ROW i (A:real['n]['n]))`]
    DET_ROW_SPAN) THEN
  GEN_REWRITE_TAC (LAND_CONV) empty_rewrites [IMP_DISJ_THM] THEN
  REWRITE_TAC[DISJ_IMP_THM] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
      `~(ROW i (A:real['n]['n])) =
       VSUM ((count (dimindex (:'n))) DELETE i) (\j. inv(c i) * c j * ROW j A)`
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
  SRW_TAC[FCP_ss][ROW_DEF, VEC_0_COMPONENT, VECTOR_ADD_RINV]);

val DET_EQ_0 = prove
 (`!A:real['n]['n]. (DET(A) = &0) <=> ~invertible(A)`,
  REWRITE_TAC[INVERTIBLE_DET_NZ]);

val DET_MATRIX_EQ_0 = prove
 (`!f:real['n]->real['n].
        linear f
        ==> ((DET(matrix f) = &0) <=>
             ~(?g. linear g /\ (f o g = I) /\ (g o f = I)))`,
  SIMP_TAC bool_ss[DET_EQ_0, MATRIX_INVERTIBLE]);

val DET_MATRIX_EQ_0_LEFT = prove
 (`!f:real['n]->real['n].
        linear f
        ==> ((DET(matrix f) = &0) <=>
             ~(?g. linear g /\ (g o f = I)))`,
   SIMP_TAC bool_ss[DET_MATRIX_EQ_0] THEN PROVE_TAC[LINEAR_INVERSE_LEFT]);

val DET_MATRIX_EQ_0_RIGHT = prove
 (`!f:real['n]->real['n].
        linear f
        ==> ((DET(matrix f) = &0) <=>
             ~(?g. linear g /\ (f o g = I)))`,
   SIMP_TAC bool_ss[DET_MATRIX_EQ_0] THEN PROVE_TAC[LINEAR_INVERSE_LEFT]);

(* ------------------------------------------------------------------------- *)
(* Cramer's rule.                                                            *)
(* ------------------------------------------------------------------------- *)

val CRAMER_LEMMA_TRANSP = prove
 (`!A:real['n]['n] x:real['n].
         k < dimindex(:'n)
        ==> (DET((FCP i. if i = k
                           then VSUM (count (dimindex(:'n))) (\i. (x ' i) * ROW i A)
                           else ROW i A): real['n]['n]) =
            (x ' k) * DET A)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `count (dimindex(:'n)) = k INSERT ((count (dimindex(:'n))) DELETE k)`
  SUBST1_TAC THENL [PROVE_TAC[INSERT_DELETE, IN_COUNT], ALL_TAC] THEN
  SIMP_TAC bool_ss[VSUM_CLAUSES, FINITE_COUNT, FINITE_DELETE, IN_DELETE] THEN
  REWRITE_TAC[VECTOR_ARITH
   ``(x:real['n] ' k) * ROW k (A:real['n]['n]) + s =
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
    CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN PROVE_TAC[]]);

val CRAMER_LEMMA = prove
 (`!A:real['n]['n] x:real['n].
        k < dimindex(:'n)
        ==> (DET((FCP i j. if j = k then (A**x) ' i else A ' i ' j):real['n]['n]) =
             x ' k * DET(A))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MATRIX_MUL_VSUM] THEN
  FIRST_ASSUM(MP_TAC o SYM o SPECL [`TRANSP(A:real['n]['n])`, `x:real['n]`] o
              MATCH_MP CRAMER_LEMMA_TRANSP) THEN
  REWRITE_TAC[DET_TRANSP] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites [GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  SRW_TAC[FCP_ss][TRANSP_DEF, MATRIX_MUL_VSUM, ROW_DEF, COLUMN_DEF,
				  COND_COMPONENT, VECTOR_MUL_COMPONENT, VSUM_COMPONENT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_COUNT THEN
  BETA_TAC THEN SRW_TAC[FCP_ss][]);

val CRAMER = prove
 (`!A:real['n]['n] x b.
        ~(DET(A) = &0)
        ==> ((A ** x = b) <=>
             (x = FCP k.
                   DET((FCP i j. if j = k then b ' i else A ' i ' j):real['n]['n]) /
                   DET(A)))`,
  GEN_TAC THEN SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  CONV_TAC SWAP_VARS_CONV THEN GEN_TAC THEN HO_MATCH_MP_TAC(PROVE[]
   ``(?x. p(x)) /\ (!x. p(x) ==> (x = a)) ==> !x. p(x) <=> (x = a)``) THEN
  CONJ_TAC THENL
   [MP_TAC(SPEC ``A:real['n]['n]`` INVERTIBLE_DET_NZ) THEN
    PROVE_TAC[invertible_def, MATRIX_VECTOR_MUL_ASSOC, MATRIX_VECTOR_MUL_LID],
    GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC bool_ss[CART_EQ, CRAMER_LEMMA, FCP_BETA, prove(
		`~(z = &0) ==> ((x = y / z) <=> (x * z = y))`,
		STRIP_TAC THEN EQ_TAC THEN RW_TAC bool_ss[real_div] THEN
	RW_TAC bool_ss[GSYM REAL_MUL_ASSOC, REAL_MUL_LINV, REAL_MUL_RINV,REAL_MUL_RID])]]);

val LAPLACE_ROW = prove
 (`!A:real['n]['n] i.
      i < dimindex (:'n) ==>
	  (DET(A) = SUM (count(dimindex (:'n))) (\j. (A ' i ' j ) * (ALG_COMP A i j)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ALG_COMP_DEF, DET_DEF] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC bool_ss[FINITE_PERMUTATIONS, FINITE_COUNT, Once SUM_SWAP] THEN
  MATCH_MP_TAC SUM_EQ THEN CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN BETA_TAC THEN 
  ONCE_REWRITE_TAC[REAL_ARITH ``!a b c:real. a * (b * c) = b * (a * c)``] THEN
  SIMP_TAC bool_ss[SUM_LMUL] THEN REWRITE_TAC[SIGN_NZ, REAL_EQ_LMUL] THEN
  X_GEN_TAC `p :num -> num` THEN DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN  
  EXISTS_TAC `SUM (count (dimindex (:'n)))
    (\j. if j = p i then PRODUCT (count (dimindex (:'n))) (\i. A ' i ' (p i)) else &0)` THEN
  CONJ_TAC THENL[
    REWRITE_TAC[SUM_DELTA] THEN PROVE_TAC[PERMUTES_IN_IMAGE, IN_COUNT], ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j` THEN SRW_TAC[FCP_ss][] THENL[
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
    `PRODUCT (count (dimindex (:'n)))(\i'. if i' = i then A ' i' ' (p i') else &1) *
     PRODUCT (count (dimindex (:'n)))
     (\i'.
       ((FCP k l.
          if k = i then
            if l = p i then &1 else &0
          else if l = p i then
            &0
          else
            A ' k ' l):real['n]['n]) ' i' ' (p i'))` THEN
	CONJ_TAC THENL[
	  SIMP_TAC bool_ss[GSYM PRODUCT_MUL_COUNT] THEN
      SRW_TAC[FCP_ss][PERMUTES_IN_COUNT] THEN MATCH_MP_TAC PRODUCT_EQ_COUNT THEN
      SRW_TAC[FCP_ss][PERMUTES_IN_COUNT] THEN PROVE_TAC[PERMUTES_INJECTIVE], ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_RMUL] THEN DISJ2_TAC THEN
    ASM_SIMP_TAC bool_ss[PRODUCT_DELTA, IN_COUNT], ALL_TAC] THEN
  DISJ2_TAC THEN SIMP_TAC bool_ss[FINITE_COUNT, PRODUCT_EQ_0] THEN
  EXISTS_TAC `i` THEN SRW_TAC[FCP_ss][PERMUTES_IN_COUNT]);

val LAPLACE_COLUMN = prove
 (`!A:real['n]['n] j.
      j < dimindex (:'n) ==>
	  (DET(A) = SUM (count(dimindex (:'n))) (\i. (A ' i ' j ) * (ALG_COMP A i j)))`,  
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `SUM (count (dimindex (:'n))) (\i. (TRANSP A) ' j ' i * ALG_COMP (TRANSP A) j i)` THEN
  CONJ_TAC THENL[ASM_SIMP_TAC bool_ss[GSYM LAPLACE_ROW, DET_TRANSP], ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][TRANSP_DEF, ALG_COMP_DEF] THEN DISJ2_TAC THEN
  GEN_REWRITE_TAC LAND_CONV empty_rewrites[GSYM DET_TRANSP] THEN AP_TERM_TAC THEN
  SRW_TAC[FCP_ss][TRANSP_DEF] THEN PROVE_TAC[]);

val ADJOINT_MATRIX_DEF = Define
 `(ADJOINT_MATRIX:real['n]['n]-> real['n]['n]) A =
		TRANSP(FCP i j. ALG_COMP A i j)`;
	
val LAPLACE_ROW_COROLLARY = prove
 (`!A:real['n]['n].
    !i j. i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j) ==>
	(SUM (count (dimindex(:'n))) (\k. A ' i ' k * ALG_COMP A j k) = &0)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
EXISTS_TAC
 `SUM (count (dimindex(:'n))) 
	(\k. ((FCP k. if k = j then ROW i A else ROW k A ):real['n]['n])' j ' k *
		ALG_COMP ((FCP k. if k = j then ROW i A else ROW k A ):real['n]['n]) j k)` THEN
CONJ_TAC THENL[
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][ROW_DEF, ALG_COMP_DEF] THEN
	DISJ2_TAC THEN AP_TERM_TAC THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
ASM_SIMP_TAC bool_ss[GSYM LAPLACE_ROW] THEN MATCH_MP_TAC DET_IDENTICAL_ROWS THEN
MAP_EVERY EXISTS_TAC [`i`, `j`] THEN SRW_TAC[FCP_ss][ROW_DEF]);

val LAPLACE_COLUMN_COROLLARY = prove
 (`!A:real['n]['n].
    !i j. i < dimindex(:'n) /\ j < dimindex(:'n) /\ ~(i = j) ==>
	(SUM (count (dimindex(:'n))) (\k. A ' k ' i * ALG_COMP A k j) = &0)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
EXISTS_TAC
 `SUM (count (dimindex(:'n))) 
	(\k. ((FCP k l. if l = j then A ' k ' i else A ' k ' l ):real['n]['n])' k ' j *
		ALG_COMP ((FCP k l. if l = j then A ' k ' i else A ' k ' l ):real['n]['n]) k j)` THEN
CONJ_TAC THENL[
	MATCH_MP_TAC SUM_EQ THEN SRW_TAC[FCP_ss][COLUMN_DEF, ALG_COMP_DEF] THEN
	DISJ2_TAC THEN AP_TERM_TAC THEN SRW_TAC[FCP_ss][], ALL_TAC] THEN
ASM_SIMP_TAC bool_ss[GSYM LAPLACE_COLUMN] THEN MATCH_MP_TAC DET_IDENTICAL_COLUMNS THEN
MAP_EVERY EXISTS_TAC [`i`, `j`] THEN SRW_TAC[FCP_ss][COLUMN_DEF]);


val LAPLACE_COROLLARY_LMUL = prove
 (`!A:real['n]['n].
    A ** ADJOINT_MATRIX A = DET A * MAT 1`,
  REWRITE_TAC[matrix_mul_def, ADJOINT_MATRIX_DEF] THEN GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `FCP i j. SUM (count (dimindex (:'n)))(\k. A ' i ' k * ALG_COMP A j k)` THEN
  CONJ_TAC THENL [
    SRW_TAC[FCP_ss][TRANSP_DEF] THEN MATCH_MP_TAC SUM_EQ, ALL_TAC] THEN
  SRW_TAC[FCP_ss][] THEN ASM_CASES_TAC `i = i'` THEN
  ASM_SIMP_TAC bool_ss[GSYM LAPLACE_ROW, LAPLACE_ROW_COROLLARY, MATRIX_CMUL_COMPONENT,
					   MAT_COMPONENT, REAL_MUL_RID, REAL_MUL_RZERO]);

val LAPLACE_COROLLARY_RMUL = prove
 (`!A:real['n]['n].
  ADJOINT_MATRIX A ** A = DET A * MAT 1`,
  REWRITE_TAC[matrix_mul_def, ADJOINT_MATRIX_DEF] THEN GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `FCP i j. SUM (count (dimindex (:'n)))(\k. ALG_COMP A k i * A ' k ' j)` THEN
  CONJ_TAC THENL [
    SRW_TAC[FCP_ss][TRANSP_DEF] THEN MATCH_MP_TAC SUM_EQ, ALL_TAC] THEN
  SRW_TAC[FCP_ss][] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_CASES_TAC `i = i'` THEN
  ASM_SIMP_TAC bool_ss[GSYM LAPLACE_COLUMN, LAPLACE_COLUMN_COROLLARY, MATRIX_CMUL_COMPONENT,
					   MAT_COMPONENT, REAL_MUL_RID, REAL_MUL_RZERO]);
					   
val MATRIX_INV_EXPLICIT = prove
 (`!A:real['n]['n].
    invertible A ==> (MATRIX_INV A = inv(DET A) * ADJOINT_MATRIX A)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MATRIX_EQ_LMUL THEN
  EXISTS_TAC `A:real['n]['n]` THEN
  ASM_SIMP_TAC bool_ss[MATRIX_INV, LAPLACE_COROLLARY_LMUL, MATRIX_VECTOR_MUL_ASSOC,
                       MATRIX_MUL_RMUL, MATRIX_CMUL_ASSOC] THEN
  MP_TAC(ISPEC `A:real['n]['n]` INVERTIBLE_DET_NZ) THEN
  ASM_SIMP_TAC bool_ss[REAL_MUL_LINV, MATRIX_CMUL_LID]);					   

(* ------------------------------------------------------------------------- *)
(* Orthogonality of a transformation and matrix.                             *)
(* ------------------------------------------------------------------------- *)

val orthogonal_transformation = new_definition
 `orthogonal_transformation(f:real['n]->real['n]) <=>
        linear f /\ !v w. f(v) dot f(w) = v dot w`;;

val ORTHOGONAL_TRANSFORMATION = prove
 (`!f. orthogonal_transformation f <=> linear f /\ !v. norm(f v) = norm(v)`,
  GEN_TAC THEN REWRITE_TAC[orthogonal_transformation] THEN EQ_TAC THENL
   [PROVE_TAC[vector_norm], SIMP_TAC[DOT_NORM] THEN PROVE_TAC[LINEAR_ADD]]);

val orthogonal_matrix = new_definition
 `orthogonal_matrix(Q:real['n]['n]) <=>
      TRANSP(Q) ** Q = MAT 1 /\ Q ** TRANSP(Q) = MAT 1`;;

val ORTHOGONAL_MATRIX = prove
 (`orthogonal_matrix(Q:real['n]['n]) <=> TRANSP(Q) ** Q = MAT 1`,
  PROVE_TAC[MATRIX_LEFT_RIGHT_INVERSE, orthogonal_matrix]);

val ORTHOGONAL_MATRIX_ID = prove
 (`orthogonal_matrix(MAT 1)`,
  REWRITE_TAC[orthogonal_matrix, TRANSP_MAT, MATRIX_MUL_LID]);

val ORTHOGONAL_MATRIX_MUL = prove
 (`!A B. orthogonal_matrix A /\ orthogonal_matrix B
         ==> orthogonal_matrix(A ** B)`,
  REWRITE_TAC[orthogonal_matrix, MATRIX_TRANSP_MUL] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_MUL_LID, MATRIX_MUL_RID]);

val ORTHOGONAL_TRANSFORMATION_MATRIX = prove
 (`!f:real['n]->real['n].
     orthogonal_transformation f <=> linear f /\ orthogonal_matrix(matrix f)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[orthogonal_transformation; ORTHOGONAL_MATRIX] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`basis i:real^N`; `basis j:real^N`]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    REWRITE_TAC[DOT_MATRIX_VECTOR_MUL] THEN
    ABBREV_TAC `A = TRANSP (matrix f) ** matrix(f:real^N->real^N)` THEN
    ASM_SIMP_TAC[matrix_mul; columnvector; rowvector; basis; LAMBDA_BETA;
             SUM_DELTA; DIMINDEX_1; LE_REFL; dot; IN_NUMSEG; MAT;
             MESON[REAL_MUL_LID; REAL_MUL_LZERO; REAL_MUL_RID; REAL_MUL_RZERO]
              `(if b then &1 else &0) * x = (if b then x else &0) /\
               x * (if b then &1 else &0) = (if b then x else &0)`];
    REWRITE_TAC[orthogonal_matrix; ORTHOGONAL_TRANSFORMATION; NORM_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
    ASM_REWRITE_TAC[DOT_MATRIX_VECTOR_MUL] THEN
    SIMP_TAC[DOT_MATRIX_PRODUCT; MATRIX_MUL_LID]]);;

val DET_ORTHOGONAL_MATRIX = prove
 (`!Q. orthogonal_matrix Q ==> DET(Q) = &1 \/ DET(Q) = -- &1`,
  GEN_TAC THEN REWRITE_TAC[REAL_RING `x = &1 \/ x = -- &1 <=> x * x = &1`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM DET_TRANSP] THEN
  SIMP_TAC[GSYM DET_MUL; orthogonal_matrix; DET_I]);;

val ORTHOGONAL_MATRIX_TRANSP = prove
 (`!A:real['n]['n]. orthogonal_matrix(TRANSP A) <=> orthogonal_matrix A`,
  REWRITE_TAC[orthogonal_matrix; TRANSP_TRANSP; CONJ_ACI]);;

val MATRIX_MUL_LTRANSP_DOT_COLUMN = prove
 (`!A:real['n]['n]. TRANSP A ** A = (FCP i j. (COLUMN i A) dot (COLUMN j A))`,
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; TRANSP; dot; column]);;

val MATRIX_MUL_RTRANSP_DOT_ROW = prove
 (`!A:real['n]['n]. A ** TRANSP A = (FCP i j. (ROW i A) dot (ROW j A))`,
  SIMP_TAC[matrix_mul; CART_EQ; LAMBDA_BETA; TRANSP; dot; ROW]);;

val ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS = prove
 (`!A:real['n]['n].
        orthogonal_matrix A <=>
        (!i. i < dimindex(:'n) ==> norm(column i A) = &1) /\
        (!i j. i < dimindex(:'n) /\
               j < dimindex(:'n) /\ ~(i = j)
               ==> orthogonal (COLUMN i A) (COLUMN j A))`,
  REWRITE_TAC[ORTHOGONAL_MATRIX] THEN
  SIMP_TAC[MATRIX_MUL_LTRANSP_DOT_COLUMN; CART_EQ; MAT; LAMBDA_BETA] THEN
  REWRITE_TAC[orthogonal; NORM_EQ_1] THEN MESON_TAC[]);;

val ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS = prove
 (`!A:real['n]['n].
        orthogonal_matrix A <=>
        (!i. i < dimindex(:N) ==> norm(ROW i A) = &1) /\
        (!i j. i < dimindex(:N) /\
               j < dimindex(:N) /\ ~(i = j)
               ==> orthogonal (ROW i A) (ROW j A))`,
  ONCE_REWRITE_TAC[GSYM ORTHOGONAL_MATRIX_TRANSP] THEN
  SIMP_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_COLUMNS; COLUMN_TRANSP]);;

