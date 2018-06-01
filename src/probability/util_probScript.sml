(* ------------------------------------------------------------------------- *)
(* Useful Theorems, some are taken from various theories by Hurd, Coble, ... *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib metisLib combinTheory pred_setTheory seqTheory
     res_quanTheory res_quanTools pairTheory arithmeticTheory realTheory realLib transcTheory
     real_sigmaTheory;

val _ = new_theory "util_prob";

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;
val Strip = S_TAC;

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

val Cond =
  MATCH_MP_TAC (PROVE [] ``!a b c. a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
  >> CONJ_TAC;

local
  val th = prove (``!a b. a /\ (a ==> b) ==> a /\ b``, PROVE_TAC [])
in
  val STRONG_CONJ_TAC :tactic = MATCH_MP_TAC th >> CONJ_TAC
end;

fun wrap a = [a];
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val std_ss' = std_ss ++ boolSimps.ETA_ss


(* ------------------------------------------------------------------------- *)
(* Auxiliary theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

val EQ_T_IMP = store_thm
  ("EQ_T_IMP",
   ``!x. x = T ==> x``,
   PROVE_TAC []);

(* ------------------------------------------------------------------------- *)
(* bool theory subtypes.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Subtype definitions *)

val _ = add_infix("->", 250, HOLgrammars.RIGHT);

val _ = overload_on
  ("->", ``FUNSET:('a->bool) -> ('b->bool) -> (('a->'b)->bool)``);
val _ = overload_on
  ("-->", ``DFUNSET : ('a->bool) -> ('a->'b->bool) -> (('a->'b)->bool)``);

val pair_def = Define
  `pair (X : 'a -> bool) (Y : 'b -> bool) = \ (x, y). x IN X /\ y IN Y`;

val IN_PAIR = store_thm
  ("IN_PAIR",
   ``!(x : 'a # 'b) X Y. x IN pair X Y = FST x IN X /\ SND x IN Y``,
   Cases
   >> RW_TAC std_ss [pair_def, SPECIFICATION]);

val PAIR_UNIV = store_thm
  ("PAIR_UNIV",
   ``pair UNIV UNIV = (UNIV : 'a # 'b -> bool)``,
   RW_TAC std_ss [EXTENSION,GSPECIFICATION, IN_PAIR, IN_UNIV]);

val PAIRED_BETA_THM = store_thm
  ("PAIRED_BETA_THM",
   ``!f z. UNCURRY f z = f (FST z) (SND z)``,
   STRIP_TAC
   >> Cases
   >> RW_TAC std_ss []);

val MAX_LE_X = store_thm
  ("MAX_LE_X",
   ``!m n k. MAX m n <= k = m <= k /\ n <= k``,
   RW_TAC arith_ss [MAX_DEF]);

val X_LE_MAX = store_thm
  ("X_LE_MAX",
   ``!m n k. k <= MAX m n = k <= m \/ k <= n``,
   RW_TAC arith_ss [MAX_DEF]);

val TRANSFORM_2D_NUM = store_thm
  ("TRANSFORM_2D_NUM",
   ``!P. (!m n : num. P m n ==> P n m) /\ (!m n. P m (m + n)) ==> (!m n. P m n)``,
   Strip
   >> Know `m <= n \/ n <= m` >- DECIDE_TAC
   >> RW_TAC std_ss [LESS_EQ_EXISTS]
   >> PROVE_TAC []);

val TRIANGLE_2D_NUM = store_thm
  ("TRIANGLE_2D_NUM",
   ``!P. (!d n. P n (d + n)) ==> (!m n : num. m <= n ==> P m n)``,
   RW_TAC std_ss [LESS_EQ_EXISTS]
   >> PROVE_TAC [ADD_COMM]);

(* ------------------------------------------------------------------------- *)
(* ----- Defining real-valued power, log, and log base 2 functions --------- *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "powr" (Infixr 700);

val powr_def = Define `x powr a = exp (a * ln x)`;

val logr_def = Define `logr a x = ln x / ln a`;

val lg_def = Define `lg x = logr 2 x`;

val lg_1 = store_thm
  ("lg_1", ``lg 1 = 0``,
   RW_TAC real_ss [lg_def, logr_def, LN_1]);

val logr_1 = store_thm
  ("logr_1", ``!b. logr b 1 = 0``,
   RW_TAC real_ss [logr_def, LN_1]);

val lg_nonzero = store_thm
  ("lg_nonzero",
   ``!x. (~(x = 0)) /\ (0 <= x) ==>
                ((~(lg x = 0)) = (~(x = 1)))``,
   RW_TAC std_ss [REAL_ARITH ``(~(x = 0)) /\ (0 <= x) = 0 < x``]
   >> RW_TAC std_ss [GSYM lg_1]
   >> RW_TAC std_ss [lg_def, logr_def, real_div, REAL_EQ_RMUL, REAL_INV_EQ_0]
   >> (MP_TAC o Q.SPECL [`2`, `1`]) LN_INJ >> RW_TAC real_ss [LN_1]
   >> RW_TAC std_ss [GSYM LN_1]
   >> MATCH_MP_TAC LN_INJ
   >> RW_TAC real_ss []);

val lg_mul = store_thm
  ("lg_mul",
   ``!x y. 0 < x /\ 0 < y ==> (lg (x * y) = lg x + lg y)``,
   RW_TAC real_ss [lg_def, logr_def, LN_MUL]);

val logr_mul = store_thm
  ("logr_mul",
   ``!b x y. 0 < x /\ 0 < y ==> (logr b (x * y) = logr b x + logr b y)``,
   RW_TAC real_ss [logr_def, LN_MUL]);

val lg_2 = store_thm
  ("lg_2",
   ``lg 2 = 1``,
   RW_TAC real_ss [lg_def, logr_def]
   >> MATCH_MP_TAC REAL_DIV_REFL
   >> (ASSUME_TAC o Q.SPECL [`1`, `2`]) LN_MONO_LT
   >> FULL_SIMP_TAC real_ss [LN_1]
   >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
   >> MATCH_MP_TAC REAL_LT_IMP_NE
   >> ASM_REWRITE_TAC []);

val lg_inv = store_thm
  ("lg_inv",
   ``!x. 0 < x ==> (lg (inv x) = ~ lg x)``,
   RW_TAC real_ss [lg_def, logr_def, LN_INV, real_div]);

val logr_inv = store_thm
  ("logr_inv",
   ``!b x. 0 < x ==> (logr b (inv x) = ~ logr b x)``,
   RW_TAC real_ss [logr_def, LN_INV, real_div]);


val logr_div = store_thm
  ("logr_div",
   ``!b x y. 0 < x /\ 0 < y ==>
        (logr b (x/y) = logr b x - logr b y)``,
   RW_TAC real_ss [real_div, logr_mul, logr_inv, GSYM real_sub]);

val neg_lg = store_thm
  ("neg_lg",
  ``!x. 0 < x ==> ((~(lg x)) = lg (inv x))``,
   RW_TAC real_ss [lg_def, logr_def, real_div]
   >> `~(ln x * inv (ln 2)) = (~ ln x) * inv (ln 2)` by REAL_ARITH_TAC
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> RW_TAC real_ss [REAL_EQ_RMUL]
   >> DISJ2_TAC >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC LN_INV
   >> RW_TAC std_ss []);

val neg_logr = store_thm
  ("neg_logr",
  ``!b x. 0 < x ==> ((~(logr b x)) = logr b (inv x))``,
   RW_TAC real_ss [logr_def, real_div]
   >> `~(ln x * inv (ln b)) = (~ ln x) * inv (ln b)` by REAL_ARITH_TAC
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> RW_TAC real_ss [REAL_EQ_RMUL]
   >> DISJ2_TAC >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC LN_INV
   >> RW_TAC std_ss []);

val lg_pow = store_thm
  ("lg_pow", ``!n. lg (2 pow n) = &n``,
   RW_TAC real_ss [lg_def, logr_def, LN_POW]
   >> `~(ln 2 = 0)`
        by (ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC REAL_LT_IMP_NE
            >> MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `ln 1`
            >> RW_TAC real_ss [LN_POS, LN_MONO_LT])
   >> RW_TAC real_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_RINV]);



(********************************************************************************************)
(********************************************************************************************)

val NUM_2D_BIJ = store_thm
  ("NUM_2D_BIJ",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS (UNIV : num -> bool))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   >> REVERSE CONJ_TAC
   >- (Q.EXISTS_TAC `FST`
       >> RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       >> Q.EXISTS_TAC `(x, 0)`
       >> RW_TAC std_ss [FST])
   >> Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   >> RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   >> Cases_on `x`
   >> Cases_on `y`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_INV = store_thm
  ("NUM_2D_BIJ_INV",
   ``?f.
       BIJ f (UNIV : num -> bool)
       ((UNIV : num -> bool) CROSS (UNIV : num -> bool))``,
   PROVE_TAC [NUM_2D_BIJ, BIJ_SYM]);

val NUM_2D_BIJ_NZ = store_thm
  ("NUM_2D_BIJ_NZ",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS ((UNIV : num -> bool) DIFF {0}))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   >> REVERSE CONJ_TAC
   >- (Q.EXISTS_TAC `FST`
       >> RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS,DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]
       >> Q.EXISTS_TAC `(x, 1)`
       >> RW_TAC std_ss [FST])
   >> Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   >> RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   >> Cases_on `x`
   >> Cases_on `y`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_NZ_INV = store_thm
  ("NUM_2D_BIJ_NZ_INV",
   ``?f.
       BIJ f (UNIV : num -> bool)
       ((UNIV : num -> bool) CROSS ((UNIV : num -> bool) DIFF {0}))``,
   PROVE_TAC [NUM_2D_BIJ_NZ, BIJ_SYM]);

val NUM_2D_BIJ_NZ_ALT = store_thm
  ("NUM_2D_BIJ_NZ_ALT",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS (UNIV : num -> bool))
       ((UNIV : num -> bool) DIFF {0})``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   >> REVERSE CONJ_TAC
   >- (Q.EXISTS_TAC `(\(x,y). x + 1:num)`
       >> RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
                >- (Cases_on `x` >> RW_TAC std_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING])
       >> Q.EXISTS_TAC `(x-1,1)`
       >> RW_TAC std_ss []
       >> MATCH_MP_TAC SUB_ADD
       >> FULL_SIMP_TAC real_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING])
   >> Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   >> RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   >- ( Cases_on `x`
        >> RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ,DIFF_DEF,
                          GSPECIFICATION,IN_UNIV,IN_SING]
        >> RW_TAC real_ss [ind_typeTheory.NUMPAIR])
   >> Cases_on `x`
   >> Cases_on `y`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_NZ_ALT_INV = store_thm
  ("NUM_2D_BIJ_NZ_ALT_INV",
   ``?f.
       BIJ f ((UNIV : num -> bool) DIFF {0})
       ((UNIV : num -> bool) CROSS (UNIV : num -> bool))``,
   PROVE_TAC [NUM_2D_BIJ_NZ_ALT, BIJ_SYM]);

val NUM_2D_BIJ_NZ_ALT2 = store_thm
  ("NUM_2D_BIJ_NZ_ALT2",
   ``?f.
       BIJ f (((UNIV : num -> bool) DIFF {0}) CROSS ((UNIV : num -> bool) DIFF {0}))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   >> REVERSE CONJ_TAC
   >- (Q.EXISTS_TAC `(\(x,y). x - 1:num)`
       >> RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       >> Q.EXISTS_TAC `(x+1,1)`
       >> RW_TAC std_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]
       )
   >> Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   >> RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   >> Cases_on `x`
   >> Cases_on `y`
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_NZ_ALT2_INV = store_thm
  ("NUM_2D_BIJ_NZ_ALT2_INV",
   ``?f.
       BIJ f (UNIV : num -> bool)
       (((UNIV : num -> bool) DIFF {0}) CROSS ((UNIV : num -> bool) DIFF {0}))``,
   PROVE_TAC [NUM_2D_BIJ_NZ_ALT2, BIJ_SYM]);

val prod_sets_def = Define `prod_sets a b = {s CROSS t | s IN a /\ t IN b}`;

val K_PARTIAL = store_thm
  ("K_PARTIAL",
   ``!x. K x = \z. x``,
   RW_TAC std_ss [K_DEF]);

val IN_o = store_thm
  ("IN_o",
   ``!x f s. x IN (s o f) = f x IN s``,
   RW_TAC std_ss [SPECIFICATION, o_THM]);

val IN_PROD_SETS = store_thm
  ("IN_PROD_SETS",
   ``!s a b. s IN prod_sets a b = ?t u. (s = t CROSS u) /\ t IN a /\ u IN b``,
   RW_TAC std_ss [prod_sets_def, GSPECIFICATION, UNCURRY]
   >> EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `(t, u)`
   >> RW_TAC std_ss []);

val NUM_2D_BIJ_SMALL_SQUARE = store_thm
  ("NUM_2D_BIJ_SMALL_SQUARE",
   ``!(f : num -> num # num) k.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?N. count k CROSS count k SUBSET IMAGE f (count N)``,
   Strip
   >> (MP_TAC o
       Q.SPECL [`f`, `UNIV CROSS UNIV`, `count k CROSS count k`] o
       INST_TYPE [``:'a`` |-> ``:num # num``]) BIJ_FINITE_SUBSET
   >> RW_TAC std_ss [CROSS_SUBSET, SUBSET_UNIV, FINITE_CROSS, FINITE_COUNT]
   >> Q.EXISTS_TAC `N`
   >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
   >> Q.PAT_X_ASSUM `BIJ a b c` MP_TAC
   >> RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
   >> POP_ASSUM (MP_TAC o Q.SPEC `x`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `y`
   >> RW_TAC std_ss []
   >> Suff `~(N <= y)` >- DECIDE_TAC
   >> PROVE_TAC []);

val NUM_2D_BIJ_BIG_SQUARE = store_thm
  ("NUM_2D_BIJ_BIG_SQUARE",
   ``!(f : num -> num # num) N.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?k. IMAGE f (count N) SUBSET count k CROSS count k``,
   RW_TAC std_ss [IN_CROSS, IN_COUNT, SUBSET_DEF, IN_IMAGE, IN_COUNT]
   >> Induct_on `N` >- RW_TAC arith_ss []
   >> Strip
   >> Cases_on `f N`
   >> REWRITE_TAC [prim_recTheory.LESS_THM]
   >> Q.EXISTS_TAC `SUC (MAX k (MAX q r))`
   >> Know `!a b. a < SUC b = a <= b`
   >- (KILL_TAC
       >> DECIDE_TAC)
   >> RW_TAC std_ss []
   >> RW_TAC std_ss []
   >> PROVE_TAC [X_LE_MAX, LESS_EQ_REFL, LESS_IMP_LESS_OR_EQ]);

val finite_enumeration_of_sets_has_max_non_empty = store_thm
  ("finite_enumeration_of_sets_has_max_non_empty",
   ``!f s. FINITE s /\ (!x. f x IN s) /\
            (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
            ?N. !n:num. n >= N ==> (f n = {})``,
        `!s. FINITE s ==>
        (\s.  !f. (!x. f x IN {} INSERT s) /\
                  (~({} IN s)) /\
                 (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
                 ?N. !n:num. n >= N ==> (f n = {})) s`
        by (MATCH_MP_TAC FINITE_INDUCT
            >> RW_TAC std_ss [NOT_IN_EMPTY, IN_INSERT]
            >> Q.PAT_X_ASSUM `!f. (!x. (f x = {}) \/ f x IN s) /\ ~({} IN s) /\
                                (!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
                                ?N:num. !n. n >= N ==> (f n = {})`
                (MP_TAC o Q.SPEC `(\x. if f x = e then {} else f x)`)
            >> `(!x. ((\x. (if f x = e then {} else f x)) x = {}) \/
                     (\x. (if f x = e then {} else f x)) x IN s) /\ ~({} IN s)`
                by METIS_TAC []
            >> ASM_SIMP_TAC std_ss []
            >> `(!m n. ~(m = n) ==> DISJOINT (if f m = e then {} else f m)
                        (if f n = e then {} else f n))`
                by (RW_TAC std_ss [IN_DISJOINT, NOT_IN_EMPTY]
                            >> METIS_TAC [IN_DISJOINT])
            >> ASM_SIMP_TAC std_ss []
            >> RW_TAC std_ss []
            >> Cases_on `?n. f n = e`
            >- (FULL_SIMP_TAC std_ss []
                >> Cases_on `n < N`
                >- (Q.EXISTS_TAC `N`
                    >> RW_TAC std_ss [GREATER_EQ]
                    >> `~(n' = n)`
                        by METIS_TAC [LESS_LESS_EQ_TRANS,
                                      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
                    >> Cases_on `f n' = f n`
                    >- (`DISJOINT (f n') (f n)` by METIS_TAC []
                        >> FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
                        >> METIS_TAC [])
                    >> Q.PAT_X_ASSUM
                                `!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
                                (MP_TAC o Q.SPEC `n'`)
                    >> ASM_SIMP_TAC std_ss [GREATER_EQ])
                >> Q.EXISTS_TAC `SUC n`
                >> RW_TAC std_ss [GREATER_EQ]
                >> FULL_SIMP_TAC std_ss [NOT_LESS]
                >> `~(n' = n)`
                        by METIS_TAC [LESS_LESS_EQ_TRANS,
                                      DECIDE ``!n:num. n < SUC n``,
                                      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
                >> Cases_on `f n' = f n`
                >- (`DISJOINT (f n') (f n)` by METIS_TAC []
                    >> FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
                    >> METIS_TAC [])
                >> `N <= n'` by METIS_TAC [LESS_EQ_IMP_LESS_SUC,
                                           LESS_LESS_EQ_TRANS,
                                           LESS_IMP_LESS_OR_EQ]
                >> Q.PAT_X_ASSUM
                                `!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
                                (MP_TAC o Q.SPEC `n'`)
                >> ASM_SIMP_TAC std_ss [GREATER_EQ])
        >> METIS_TAC [])
   >> REPEAT STRIP_TAC
   >> Cases_on `{} IN s`
   >- (Q.PAT_X_ASSUM `!s. FINITE s ==> P` (MP_TAC o Q.SPEC `s DELETE {}`)
       >> RW_TAC std_ss [FINITE_DELETE, IN_INSERT, IN_DELETE])
   >> METIS_TAC [IN_INSERT]);

val PREIMAGE_REAL_COMPL1 = store_thm
  ("PREIMAGE_REAL_COMPL1", ``!c:real. COMPL {x | c < x} = {x | x <= c}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]);

val PREIMAGE_REAL_COMPL2 = store_thm
  ("PREIMAGE_REAL_COMPL2", ``!c:real. COMPL {x | c <= x} = {x | x < c}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]);

val PREIMAGE_REAL_COMPL3 = store_thm
  ("PREIMAGE_REAL_COMPL3", ``!c:real. COMPL {x | x <= c} = {x | c < x}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]);

val PREIMAGE_REAL_COMPL4 = store_thm
  ("PREIMAGE_REAL_COMPL4", ``!c:real. COMPL {x | x < c} = {x | c <= x}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  >> RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]);

val GBIGUNION_IMAGE = store_thm
  ("GBIGUNION_IMAGE",
   ``!s p n. {s | ?n. p s n} = BIGUNION (IMAGE (\n. {s | p s n}) UNIV)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV]);

(********************************************************************************************
*********************************************************************************************)

val LT_SUC = store_thm
  ("LT_SUC",
   ``!a b. a < SUC b = a < b \/ (a = b)``,
   DECIDE_TAC);

val LE_SUC = store_thm
  ("LE_SUC",
   ``!a b. a <= SUC b = a <= b \/ (a = SUC b)``,
   DECIDE_TAC);

val HALF_POS = store_thm
  ("HALF_POS",
   ``0:real < 1/2``,
   PROVE_TAC [REAL_ARITH ``0:real < 1``, REAL_LT_HALF1]);

val HALF_LT_1 = store_thm
  ("HALF_LT_1",
   ``1 / 2 < 1:real``,
   ONCE_REWRITE_TAC [GSYM REAL_INV_1OVER, GSYM REAL_INV1]
   >> MATCH_MP_TAC REAL_LT_INV
   >> RW_TAC arith_ss [REAL_LT]);

val HALF_CANCEL = store_thm
  ("HALF_CANCEL",
   ``2 * (1 / 2) = 1:real``,
   Suff `2 * inv 2 = 1:real` >- PROVE_TAC [REAL_INV_1OVER]
   >> PROVE_TAC [REAL_MUL_RINV, REAL_ARITH ``~(2:real = 0)``]);

val X_HALF_HALF = store_thm
  ("X_HALF_HALF",
   ``!x:real. 1/2 * x + 1/2 * x = x``,
   STRIP_TAC
   >> MATCH_MP_TAC (REAL_ARITH ``(2 * (a:real) = 2 * b) ==> (a = b)``)
   >> RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
   >> REAL_ARITH_TAC);

val ONE_MINUS_HALF = store_thm
  ("ONE_MINUS_HALF",
   ``(1:real) - 1 / 2 = 1 / 2``,
   MP_TAC (Q.SPEC `1` X_HALF_HALF)
   >> RW_TAC real_ss []
   >> MATCH_MP_TAC (REAL_ARITH ``((x:real) + 1 / 2 = y + 1 / 2) ==> (x = y)``)
   >> RW_TAC std_ss [REAL_SUB_ADD]);

val POW_HALF_POS = store_thm
  ("POW_HALF_POS",
   ``!n. 0:real < (1/2) pow n``,
   STRIP_TAC
   >> Cases_on `n` >- PROVE_TAC [REAL_ARITH ``0:real < 1``, pow]
   >> PROVE_TAC [HALF_POS, POW_POS_LT]);

val POW_HALF_SMALL = store_thm
  ("POW_HALF_SMALL",
   ``!e:real. 0 < e ==> ?n. (1 / 2) pow n < e``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `1 / 2` SEQ_POWER)
   >> RW_TAC std_ss [abs, HALF_LT_1, HALF_POS, REAL_LT_IMP_LE, SEQ]
   >> POP_ASSUM (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss [REAL_SUB_RZERO, POW_HALF_POS, REAL_LT_IMP_LE,
                      GREATER_EQ]
   >> PROVE_TAC [LESS_EQ_REFL]);

val POW_HALF_MONO = store_thm
  ("POW_HALF_MONO",
   ``!m n. m <= n ==> ((1:real)/2) pow n <= (1/2) pow m``,
   REPEAT STRIP_TAC
   >> Induct_on `n` >|
   [STRIP_TAC
    >> Know `m:num = 0` >- DECIDE_TAC
    >> PROVE_TAC [REAL_ARITH ``a:real <= a``],
    Cases_on `m = SUC n` >- PROVE_TAC [REAL_ARITH ``a:real <= a``]
    >> ONCE_REWRITE_TAC [pow]
    >> STRIP_TAC
    >> Know `m:num <= n` >- DECIDE_TAC
    >> STRIP_TAC
    >> Suff `(2:real) * ((1/2) * (1/2) pow n) <= 2 * (1/2) pow m`
    >- PROVE_TAC [REAL_ARITH ``0:real < 2``, REAL_LE_LMUL]
    >> Suff `((1:real)/2) pow n <= 2 * (1/2) pow m`
    >- (KILL_TAC
        >> PROVE_TAC [GSYM REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID])
    >> PROVE_TAC [REAL_ARITH ``!x y. 0:real < x /\ x <= y ==> x <= 2 * y``,
                  POW_HALF_POS]]);

val REAL_LE_LT_MUL = store_thm
  ("REAL_LE_LT_MUL",
   ``!x y : real. 0 <= x /\ 0 < y ==> 0 <= x * y``,
   rpt STRIP_TAC
   >> MP_TAC (Q.SPECL [`0`, `x`, `y`] REAL_LE_RMUL)
   >> RW_TAC std_ss [REAL_MUL_LZERO]);

val REAL_LT_LE_MUL = store_thm
  ("REAL_LT_LE_MUL",
   ``!x y : real. 0 < x /\ 0 <= y ==> 0 <= x * y``,
   PROVE_TAC [REAL_LE_LT_MUL, REAL_MUL_SYM]);

val REAL_MUL_IDEMPOT = store_thm
  ("REAL_MUL_IDEMPOT",
   ``!r: real. (r * r = r) = (r = 0) \/ (r = 1)``,
   GEN_TAC
   >> REVERSE EQ_TAC
   >- (RW_TAC real_ss [] >> RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_LID])
   >> RW_TAC std_ss []
   >> Know `r * r = 1 * r` >- RW_TAC real_ss []
   >> RW_TAC std_ss [REAL_EQ_RMUL]);

val REAL_SUP_LE_X = store_thm
  ("REAL_SUP_LE_X",
   ``!P x:real. (?r. P r) /\ (!r. P r ==> r <= x) ==> sup P <= x``,
   RW_TAC real_ss []
   >> Suff `~(x < sup P)` >- REAL_ARITH_TAC
   >> STRIP_TAC
   >> MP_TAC (SPEC ``P:real->bool`` REAL_SUP_LE)
   >> RW_TAC real_ss [] >|
   [PROVE_TAC [],
    PROVE_TAC [],
    EXISTS_TAC ``x:real``
    >> RW_TAC real_ss []
    >> PROVE_TAC [real_lte]]);

val REAL_X_LE_SUP = store_thm
  ("REAL_X_LE_SUP",
   ``!P x:real. (?r. P r) /\ (?z. !r. P r ==> r <= z) /\ (?r. P r /\ x <= r)
           ==> x <= sup P``,
   RW_TAC real_ss []
   >> Suff `!y. P y ==> y <= sup P` >- PROVE_TAC [REAL_LE_TRANS]
   >> MATCH_MP_TAC REAL_SUP_UBOUND_LE
   >> PROVE_TAC []);

val INF_DEF_ALT = store_thm
  ("INF_DEF_ALT",
   ``!p. inf p = ~(sup (\r. ~r IN p)):real``,
   RW_TAC std_ss []
   >> PURE_REWRITE_TAC [inf_def, IMAGE_DEF]
   >> Suff `(\r. p (-r)) = (\r. -r IN p)`
   >- RW_TAC std_ss []
   >> RW_TAC std_ss [FUN_EQ_THM,SPECIFICATION]);

val LE_INF = store_thm
  ("LE_INF",
   ``!p r:real. (?x. x IN p) /\ (!x. x IN p ==> r <= x) ==> r <= inf p``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   >> Q.SPEC_TAC (`~r`, `r`)
   >> RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   >> MATCH_MP_TAC REAL_SUP_LE_X
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_NEGNEG]);

val INF_LE = store_thm
  ("INF_LE",
   ``!p r:real.
       (?z. !x. x IN p ==> z <= x) /\ (?x. x IN p /\ x <= r) ==> inf p <= r``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   >> Q.SPEC_TAC (`~r`, `r`)
   >> RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   >> MATCH_MP_TAC REAL_X_LE_SUP
   >> RW_TAC std_ss []
   >> PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

val INF_GREATER = store_thm
  ("INF_GREATER",
   ``!p z:real.
       (?x. x IN p) /\ inf p < z ==>
       (?x. x IN p /\ x < z)``,
   RW_TAC std_ss []
   >> Suff `~(!x. x IN p ==> ~(x < z))` >- PROVE_TAC []
   >> REWRITE_TAC [GSYM real_lte]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `inf p < z` MP_TAC
   >> RW_TAC std_ss [GSYM real_lte]
   >> MATCH_MP_TAC LE_INF
   >> PROVE_TAC []);

val INF_CLOSE = store_thm
  ("INF_CLOSE",
   ``!p e:real.
       (?x. x IN p) /\ 0 < e ==> (?x. x IN p /\ x < inf p + e)``,
   RW_TAC std_ss []
   >> MATCH_MP_TAC INF_GREATER
   >> CONJ_TAC >- PROVE_TAC []
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);



(************************************************************************************************)
(************************************************************************************************)

val INCREASING_SEQ = store_thm
  ("INCREASING_SEQ",
   ``!f l.
       (!n. f n <= f (SUC n)) /\
       (!n. f n <= l) /\
       (!e. 0 < e ==> ?n. l < f n + e) ==>
       f --> l``,
   RW_TAC std_ss [SEQ, GREATER_EQ]
   >> Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `n`
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> REVERSE (RW_TAC std_ss [abs])
   >- (Q.PAT_X_ASSUM `~x` MP_TAC
       >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n'`)
       >> REAL_ARITH_TAC)
   >> Know `?d. n' = n + d` >- PROVE_TAC [LESS_EQ_EXISTS]
   >> RW_TAC std_ss []
   >> Suff `l < f (n + d) + e` >- REAL_ARITH_TAC
   >> NTAC 2 (POP_ASSUM K_TAC)
   >> Induct_on `d` >- RW_TAC arith_ss []
   >> RW_TAC std_ss [ADD_CLAUSES]
   >> Q.PAT_X_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `n + d`)
   >> POP_ASSUM MP_TAC
   >> REAL_ARITH_TAC);

val SEQ_SANDWICH = store_thm
  ("SEQ_SANDWICH",
   ``!f g h l.
       f --> l /\ h --> l /\ (!n. f n <= g n /\ g n <= h n) ==> g --> l``,
   RW_TAC std_ss [SEQ, GREATER_EQ]
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `e`)
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `e`)
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `MAX N N'`
   >> RW_TAC std_ss [MAX_LE_X]
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `n`)
   >> Q.PAT_X_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `n`)
   >> RW_TAC std_ss []
   >> REPEAT (POP_ASSUM MP_TAC)
   >> DISCH_THEN (MP_TAC o Q.SPEC `n`)
   >> RW_TAC std_ss [abs]
   >> REPEAT (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val SER_POS = store_thm
  ("SER_POS",
   ``!f. summable f /\ (!n. 0 <= f n) ==> 0 <= suminf f``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPECL [`f`, `0`] SER_POS_LE)
   >> RW_TAC std_ss [sum]);

val SER_POS_MONO = store_thm
  ("SER_POS_MONO",
   ``!f. (!n. 0 <= f n) ==> mono (\n. sum (0, n) f)``,
   RW_TAC std_ss [mono]
   >> DISJ1_TAC
   >> HO_MATCH_MP_TAC TRIANGLE_2D_NUM
   >> Induct >- RW_TAC arith_ss [REAL_LE_REFL]
   >> RW_TAC std_ss [ADD_CLAUSES]
   >> MATCH_MP_TAC REAL_LE_TRANS
   >> Q.EXISTS_TAC `sum (0, d + n) f`
   >> RW_TAC real_ss [sum]
   >> Q.PAT_X_ASSUM `!n. 0 <= f n` (MP_TAC o Q.SPEC `d + n`)
   >> REAL_ARITH_TAC);

val POS_SUMMABLE = store_thm
  ("POS_SUMMABLE",
   ``!f. (!n. 0 <= f n) /\ (?x. !n. sum (0, n) f <= x) ==> summable f``,
   RW_TAC std_ss [summable, sums, GSYM convergent]
   >> MATCH_MP_TAC SEQ_BCONV
   >> RW_TAC std_ss [SER_POS_MONO, netsTheory.MR1_BOUNDED]
   >> Q.EXISTS_TAC `x + 1`
   >> Q.EXISTS_TAC `N`
   >> RW_TAC arith_ss []
   >> RW_TAC std_ss [abs, SUM_POS]
   >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`)
   >> REAL_ARITH_TAC);

val SUMMABLE_LE = store_thm
  ("SUMMABLE_LE",
   ``!f x. summable f /\ (!n. sum (0, n) f <= x) ==> suminf f <= x``,
   Strip
   >> Suff `0 < suminf f - x ==> F` >- REAL_ARITH_TAC
   >> Strip
   >> Know `(\n. sum (0, n) f) --> suminf f`
   >- RW_TAC std_ss [GSYM sums, SUMMABLE_SUM]
   >> RW_TAC std_ss [SEQ]
   >> Q.EXISTS_TAC `suminf f - x`
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `N`
   >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   >> RW_TAC real_ss []
   >> ONCE_REWRITE_TAC [ABS_SUB]
   >> Know `0 <= suminf f - sum (0, N) f`
   >- (rpt (POP_ASSUM MP_TAC)
       >> REAL_ARITH_TAC)
   >> RW_TAC std_ss [abs]
   >> rpt (POP_ASSUM MP_TAC)
   >> REAL_ARITH_TAC);

val SUMS_EQ = store_thm
  ("SUMS_EQ",
   ``!f x. f sums x = summable f /\ (suminf f = x)``,
   PROVE_TAC [SUM_SUMMABLE, SUM_UNIQ, summable]);

val SUMINF_POS = store_thm
  ("SUMINF_POS",
   ``!f. (!n. 0 <= f n) /\ summable f ==> 0 <= suminf f``,
   RW_TAC std_ss []
   >> Know `0 = sum (0, 0) f` >- RW_TAC std_ss [sum]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> MATCH_MP_TAC SER_POS_LE
   >> RW_TAC std_ss []);

 val SUM_PICK = store_thm
  ("SUM_PICK",
   ``!n k x. sum (0, n) (\m. if m = k then x else 0) = if k < n then x else 0``,
   Induct >- RW_TAC arith_ss [sum]
   >> RW_TAC arith_ss [sum, REAL_ADD_RID, REAL_ADD_LID]
   >> Suff `F` >- PROVE_TAC []
   >> NTAC 2 (POP_ASSUM MP_TAC)
   >> DECIDE_TAC);

val SUM_LT = store_thm
  ("SUM_LT",
   ``!f g m n.
       (!r. m <= r /\ r < n + m ==> f r < g r) /\ 0 < n ==>
       sum (m,n) f < sum (m,n) g``,
   RW_TAC std_ss []
   >> POP_ASSUM MP_TAC
   >> Cases_on `n` >- RW_TAC arith_ss []
   >> RW_TAC arith_ss []
   >> Induct_on `n'` >- RW_TAC arith_ss [sum, REAL_ADD_LID]
   >> ONCE_REWRITE_TAC [sum]
   >> Strip
   >> MATCH_MP_TAC REAL_LT_ADD2
   >> CONJ_TAC
   >- (Q.PAT_X_ASSUM `a ==> b` MATCH_MP_TAC
       >> RW_TAC arith_ss [])
   >> RW_TAC arith_ss []);

val SUM_CONST_R = store_thm
  ("SUM_CONST_R",
   ``!n r. sum (0,n) (K r) = &n * r``,
   Induct >- RW_TAC real_ss [sum]
   >> RW_TAC bool_ss [sum, ADD1, K_THM, GSYM REAL_ADD, REAL_ADD_RDISTRIB]
   >> RW_TAC real_ss []);

val SUMS_ZERO = store_thm
  ("SUMS_ZERO",
   ``(K 0) sums 0``,
   RW_TAC real_ss [sums, SEQ, SUM_CONST_R, abs, REAL_SUB_REFL, REAL_LE_REFL]);

val SUMINF_ADD = store_thm
  ("SUMINF_ADD",
   ``!f g.
       summable f /\ summable g ==>
       summable (\n. f n + g n) /\
       (suminf f + suminf g = suminf (\n. f n + g n))``,
    RW_TAC std_ss []
 >> ( Know `f sums suminf f /\ g sums suminf g` >- PROVE_TAC [SUMMABLE_SUM]
   >> STRIP_TAC
   >> Know `(\n. f n + g n) sums (suminf f + suminf g)`
   >- RW_TAC std_ss [SER_ADD]
   >> RW_TAC std_ss [SUMS_EQ] ));

val SUMINF_2D = store_thm
  ("SUMINF_2D",
   ``!f g h.
       (!m n. 0 <= f m n) /\ (!n. f n sums g n) /\ summable g /\
       BIJ h UNIV (UNIV CROSS UNIV) ==>
       (UNCURRY f o h) sums suminf g``,
   RW_TAC std_ss []
   >> RW_TAC std_ss [sums]
   >> Know `g sums suminf g` >- PROVE_TAC [SUMMABLE_SUM]
   >> Q.PAT_X_ASSUM `!n. P n` MP_TAC
   >> RW_TAC std_ss [SUMS_EQ, FORALL_AND_THM]
   >> MATCH_MP_TAC INCREASING_SEQ
   >> CONJ_TAC
   >- (RW_TAC std_ss [sum, o_THM, ADD_CLAUSES]
       >> Cases_on `h n`
       >> RW_TAC std_ss [UNCURRY_DEF]
       >> Q.PAT_X_ASSUM `!m n. 0 <= f m n` (MP_TAC o Q.SPECL [`q`, `r`])
       >> REAL_ARITH_TAC)
   >> Know `!m. 0 <= g m`
   >- (STRIP_TAC
       >> Suff `0 <= suminf (f m)` >- PROVE_TAC []
       >> MATCH_MP_TAC SER_POS
       >> PROVE_TAC [])
   >> STRIP_TAC
   >> CONJ_TAC
   >- (RW_TAC std_ss []
       >> MP_TAC (Q.SPECL [`h`, `n`] NUM_2D_BIJ_BIG_SQUARE)
       >> ASM_REWRITE_TAC []
       >> STRIP_TAC
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0,k) g`
       >> REVERSE CONJ_TAC
       >- (MATCH_MP_TAC SER_POS_LE
           >> PROVE_TAC [])
       >> MATCH_MP_TAC REAL_LE_TRANS
       >> Q.EXISTS_TAC `sum (0,k) (\m. sum (0,k) (f m))`
       >> REVERSE CONJ_TAC
       >- (MATCH_MP_TAC SUM_LE
           >> RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM)
           >> MATCH_MP_TAC SER_POS_LE
           >> PROVE_TAC [])
       >> Suff
          `!j.
             j <= n ==>
             (sum (0, j) (UNCURRY f o h) =
              sum (0, k)
              (\m. sum (0, k)
               (\n. if (?i. i < j /\ (h i = (m, n))) then f m n else 0)))`
       >- (DISCH_THEN (MP_TAC o Q.SPEC `n`)
           >> REWRITE_TAC [LESS_EQ_REFL]
           >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
           >> MATCH_MP_TAC SUM_LE
           >> RW_TAC std_ss []
           >> MATCH_MP_TAC SUM_LE
           >> RW_TAC std_ss [REAL_LE_REFL])
       >> Induct >- RW_TAC arith_ss [sum, SUM_0]
       >> RW_TAC std_ss [sum]
       >> Q.PAT_X_ASSUM `p ==> q` MP_TAC
       >> RW_TAC arith_ss []
       >> Know
          `!m n.
             (?i. i < SUC j /\ (h i = (m,n))) =
             (?i. i < j /\ (h i = (m,n))) \/ (h j = (m, n))`
       >- (RW_TAC std_ss []
           >> Suff `!i. i < SUC j = i < j \/ (i = j)`
           >- PROVE_TAC []
           >> DECIDE_TAC)
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> Know
          `!m n.
             (if (?i. i < j /\ (h i = (m,n))) \/ (h j = (m,n)) then f m n
              else 0) =
             (if (?i. i < j /\ (h i = (m,n))) then f m n else 0) +
             (if (h j = (m,n)) then f m n else 0)`
       >- (Strip
           >> Suff `(?i. i < j /\ (h i = (m,n'))) ==> ~(h j = (m,n'))`
           >- PROVE_TAC [REAL_ADD_LID, REAL_ADD_RID]
           >> RW_TAC std_ss []
           >> Q.PAT_X_ASSUM `BIJ a b c` MP_TAC
           >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV, IN_CROSS]
           >> PROVE_TAC [prim_recTheory.LESS_REFL])
       >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       >> RW_TAC std_ss [SUM_ADD]
       >> POP_ASSUM K_TAC
       >> Suff
          `(UNCURRY f o h) j =
           sum (0,k)
           (\m. sum (0,k) (\n. (if h j = (m,n) then f m n else 0)))`
       >- (KILL_TAC
           >> Q.SPEC_TAC
              (`(sum (0,k)
                 (\m.
                  sum (0,k)
                  (\n. if ?i. i < j /\ (h i = (m,n)) then f m n else 0)))`,
               `r1`)
           >> Q.SPEC_TAC
              (`sum (0,k)
                (\m. sum (0,k) (\n. (if h j = (m,n) then f m n else 0)))`,
               `r2`)
           >> RW_TAC std_ss [])
       >> Cases_on `h j`
       >> RW_TAC std_ss [o_THM, UNCURRY_DEF]
       >> Know
          `!m n.
             (if (q = m) /\ (r = n) then f m n else 0) =
             (if (n = r) then if (m = q) then f m n else 0 else 0)`
       >- PROVE_TAC []
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> Q.PAT_X_ASSUM `a SUBSET b` MP_TAC
       >> RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, IN_CROSS]
       >> Suff `q < k /\ r < k`
       >- RW_TAC std_ss [SUM_PICK]
       >> POP_ASSUM (MP_TAC o Q.SPEC `h (j:num)`)
       >> Suff `j < n`
       >- (RW_TAC std_ss []
           >> PROVE_TAC [])
       >> DECIDE_TAC)
   >> RW_TAC std_ss []
   >> Know `?M. 0 < M /\ suminf g < sum (0, M) g + e / 2`
   >- (Know `g sums suminf g` >- PROVE_TAC [SUMMABLE_SUM]
       >> RW_TAC std_ss [sums, SEQ]
       >> POP_ASSUM (MP_TAC o Q.SPEC `e / 2`)
       >> RW_TAC std_ss [REAL_LT_HALF1, GREATER_EQ]
       >> POP_ASSUM (MP_TAC o Q.SPEC `SUC N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> Know `sum (0, SUC N) g <= suminf g`
       >- (MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [])
       >> REVERSE (RW_TAC arith_ss [abs])
       >- (Suff `F` >- PROVE_TAC []
           >> POP_ASSUM K_TAC
           >> POP_ASSUM MP_TAC
           >> POP_ASSUM MP_TAC
           >> REAL_ARITH_TAC)
       >> Q.EXISTS_TAC `SUC N`
       >> CONJ_TAC >- DECIDE_TAC
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> RW_TAC std_ss []
   >> Suff `?k. sum (0, M) g < sum (0, k) (UNCURRY f o h) + e / 2`
   >- (Strip
       >> Q.EXISTS_TAC `k`
       >> Know
          `sum (0, M) g + e / 2 < sum (0, k) (UNCURRY f o h) + (e / 2 + e / 2)`
       >- (POP_ASSUM MP_TAC
           >> REAL_ARITH_TAC)
       >> POP_ASSUM K_TAC
       >> POP_ASSUM MP_TAC
       >> REWRITE_TAC [REAL_HALF_DOUBLE]
       >> REAL_ARITH_TAC)
   >> POP_ASSUM K_TAC
   >> Know `!m. ?N. g m < sum (0, N) (f m) + (e / 2) / & M`
   >- (Know `!m. f m sums g m`
       >- RW_TAC std_ss [SUMS_EQ]
       >> RW_TAC std_ss [sums, SEQ]
       >> POP_ASSUM (MP_TAC o Q.SPECL [`m`, `(e / 2) / & M`])
       >> Know `0 < (e / 2) / & M`
       >- RW_TAC arith_ss [REAL_LT_DIV, REAL_NZ_IMP_LT]
       >> DISCH_THEN (REWRITE_TAC o wrap)
       >> RW_TAC std_ss [GREATER_EQ]
       >> POP_ASSUM (MP_TAC o Q.SPEC `N`)
       >> ONCE_REWRITE_TAC [ABS_SUB]
       >> Know `sum (0, N) (f m) <= g m`
       >- (Q.PAT_X_ASSUM `!n. P n = Q n` (REWRITE_TAC o wrap o GSYM)
           >> MATCH_MP_TAC SER_POS_LE
           >> RW_TAC std_ss [])
       >> REVERSE (RW_TAC arith_ss [abs])
       >- (POP_ASSUM K_TAC
           >> Suff `F` >- PROVE_TAC []
           >> NTAC 2 (POP_ASSUM MP_TAC)
           >> REAL_ARITH_TAC)
       >> Q.EXISTS_TAC `N`
       >> POP_ASSUM MP_TAC
       >> REAL_ARITH_TAC)
   >> DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
   >> RW_TAC std_ss []
   >> Know `?c. M <= c /\ !m. m < M ==> N m <= c`
   >- (KILL_TAC
       >> Induct_on `M` >- RW_TAC arith_ss []
       >> Strip
       >> Q.EXISTS_TAC `MAX (SUC c) (N M)`
       >> RW_TAC arith_ss [X_LE_MAX, LT_SUC]
       >> PROVE_TAC [LESS_EQ_REFL, LE])
   >> Strip
   >> MP_TAC (Q.SPECL [`h`, `c`] NUM_2D_BIJ_SMALL_SQUARE)
   >> ASM_REWRITE_TAC []
   >> DISCH_THEN (Q.X_CHOOSE_TAC `k`)
   >> Q.EXISTS_TAC `k`
   >> MATCH_MP_TAC REAL_LTE_TRANS
   >> Q.EXISTS_TAC `sum (0, M) (\m. sum (0, N m) (f m) + e / 2 / &M)`
   >> CONJ_TAC
   >- (MATCH_MP_TAC SUM_LT
       >> RW_TAC arith_ss [])
   >> RW_TAC std_ss [SUM_ADD, GSYM K_PARTIAL, SUM_CONST_R]
   >> Know `!x:real. & M * (x / & M) = x`
   >- (RW_TAC std_ss [real_div]
       >> Suff `(& M * inv (& M)) * x = x`
       >- PROVE_TAC [REAL_MUL_ASSOC, REAL_MUL_SYM]
       >> Suff `~(& M = 0:real)` >- RW_TAC std_ss [REAL_MUL_RINV, REAL_MUL_LID]
       >> RW_TAC arith_ss [REAL_INJ])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [REAL_LE_RADD]
   >> Suff
      `sum (0,M) (\m. sum (0,N m) (f m)) =
       sum (0, k)
       (\k.
          if ?m n. m < M /\ n < N m /\ (h k = (m, n)) then (UNCURRY f o h) k
          else 0)`
   >- (RW_TAC std_ss []
       >> MATCH_MP_TAC SUM_LE
       >> RW_TAC std_ss [o_THM, REAL_LE_REFL]
       >> Cases_on `h r`
       >> RW_TAC std_ss [UNCURRY_DEF])
   >> NTAC 3 (POP_ASSUM MP_TAC)
   >> Q.PAT_X_ASSUM `BIJ h a b` MP_TAC
   >> KILL_TAC
   >> RW_TAC std_ss []
   >> Induct_on `M` >- RW_TAC arith_ss [sum, SUM_ZERO]
   >> RW_TAC arith_ss [sum, LT_SUC]
   >> Q.PAT_X_ASSUM `a ==> b` K_TAC
   >> Know
      `!k'.
         (?m n. (m < M \/ (m = M)) /\ n < N m /\ (h k' = (m, n))) =
         (?m n. m < M /\ n < N m /\ (h k' = (m, n))) \/
         (?n. n < N M /\ (h k' = (M, n)))`
   >- PROVE_TAC []
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Know
      `!k'.
         (if (?m n. m < M /\ n < N m /\ (h k' = (m,n))) \/
             (?n. n < N M /\ (h k' = (M,n)))
          then UNCURRY f (h k')
          else 0) =
         (if (?m n. m < M /\ n < N m /\ (h k' = (m,n))) then UNCURRY f (h k')
          else 0) +
         (if (?n. n < N M /\ (h k' = (M,n))) then UNCURRY f (h k')
          else 0)`
   >- (STRIP_TAC
       >> Suff
          `(?m n. m < M /\ n < N m /\ (h k' = (m,n))) ==>
           ~(?n. n < N M /\ (h k' = (M,n)))`
       >- PROVE_TAC [REAL_ADD_RID, REAL_ADD_LID]
       >> Cases_on `h k'`
       >> RW_TAC arith_ss [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [SUM_ADD, REAL_EQ_LADD]
   >> Know `N M <= c` >- PROVE_TAC []
   >> POP_ASSUM K_TAC
   >> Q.SPEC_TAC (`N M`, `l`)
   >> Induct >- RW_TAC real_ss [sum, SUM_0]
   >> RW_TAC arith_ss [sum, LT_SUC]
   >> Q.PAT_X_ASSUM `a ==> b` K_TAC
   >> Know
      `!k'.
         (?n. (n < l \/ (n = l)) /\ (h k' = (M,n))) =
         (?n. n < l /\ (h k' = (M,n))) \/ (h k' = (M, l))`
   >- PROVE_TAC []
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> Know
      `!k'.
         (if (?n. n < l /\ (h k' = (M,n))) \/ (h k' = (M, l)) then
            UNCURRY f (h k')
          else 0) =
         (if (?n. n < l /\ (h k' = (M,n))) then UNCURRY f (h k') else 0) +
         (if (h k' = (M, l)) then UNCURRY f (h k') else 0)`
   >- (STRIP_TAC
       >> Suff `(?n. n < l /\ (h k' = (M,n))) ==> ~(h k' = (M, l))`
       >- PROVE_TAC [REAL_ADD_LID, REAL_ADD_RID]
       >> Cases_on `h k'`
       >> RW_TAC arith_ss [])
   >> DISCH_THEN (REWRITE_TAC o wrap)
   >> RW_TAC std_ss [SUM_ADD, REAL_EQ_LADD]
   >> Q.PAT_X_ASSUM `a SUBSET b` MP_TAC
   >> RW_TAC std_ss [SUBSET_DEF, IN_CROSS, IN_COUNT, IN_IMAGE]
   >> POP_ASSUM (MP_TAC o Q.SPEC `(M, l)`)
   >> RW_TAC arith_ss []
   >> Suff `!k'. (h k' = (M, l)) = (k' = x')`
   >- (RW_TAC std_ss [SUM_PICK, o_THM]
       >> Q.PAT_X_ASSUM `(M,l) = a` (REWRITE_TAC o wrap o GSYM)
       >> RW_TAC std_ss [UNCURRY_DEF])
   >> Q.PAT_X_ASSUM `BIJ h a b` MP_TAC
   >> RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV, IN_CROSS]
   >> PROVE_TAC []);

val POW_HALF_SER = store_thm
  ("POW_HALF_SER",
   ``(\n. (1 / 2) pow (n + 1)) sums 1``,
   Know `(\n. (1 / 2) pow n) sums inv (1 - (1 / 2))`
   >- (MATCH_MP_TAC GP
       >> RW_TAC std_ss [abs, HALF_POS, REAL_LT_IMP_LE, HALF_LT_1])
   >> RW_TAC std_ss [ONE_MINUS_HALF, REAL_INV_INV, GSYM REAL_INV_1OVER,
                     GSYM ADD1, pow]
   >> Know `1 = inv 2 * 2:real`
   >- RW_TAC arith_ss [REAL_MUL_LINV, REAL_INJ]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> HO_MATCH_MP_TAC SER_CMUL
   >> RW_TAC std_ss []);

val SER_POS_COMPARE = store_thm
  ("SER_POS_COMPARE",
   ``!f g.
       (!n. 0 <= f n) /\ summable g /\ (!n. f n <= g n) ==>
       summable f /\ suminf f <= suminf g``,
   REVERSE (rpt (STRONG_CONJ_TAC ORELSE STRIP_TAC))
   >- PROVE_TAC [SER_LE]
   >> MATCH_MP_TAC SER_COMPAR
   >> Q.EXISTS_TAC `g`
   >> RW_TAC std_ss []
   >> Q.EXISTS_TAC `0`
   >> RW_TAC arith_ss [abs]);


(************************************************************************************************)
(************************************************************************************************)

val minimal_def = Define
  `minimal p = @(n:num). p n /\ (!m. m < n ==> ~(p m))`;

val MINIMAL_EXISTS0 = store_thm
  ("MINIMAL_EXISTS0",
   ``(?(n:num). P n) = (?n. P n /\ (!m. m < n ==> ~(P m)))``,
   REVERSE EQ_TAC >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> CCONTR_TAC
   >> Suff `!n. ~P n` >- PROVE_TAC []
   >> STRIP_TAC
   >> completeInduct_on `n'`
   >> PROVE_TAC []);

val MINIMAL_EXISTS = store_thm
  ("MINIMAL_EXISTS",
   ``!P. (?n. P n) = (P (minimal P) /\ !n. n < minimal P ==> ~P n)``,
   REWRITE_TAC [MINIMAL_EXISTS0, boolTheory.EXISTS_DEF]
   >> CONV_TAC (DEPTH_CONV BETA_CONV)
   >> REWRITE_TAC [GSYM minimal_def]);

val MINIMAL_EXISTS_IMP = store_thm
  ("MINIMAL_EXISTS_IMP",
   ``!P. (?n : num. P n) ==> ?m. (P m /\ !n. n < m ==> ~P n)``,
   PROVE_TAC [MINIMAL_EXISTS]);

val MINIMAL_EQ_IMP = store_thm
  ("MINIMAL_EQ_IMP",
   ``!m p. (p m) /\ (!n. n < m ==> ~p n) ==> (m = minimal p)``,
   RW_TAC std_ss []
   >> MP_TAC (Q.SPEC `p` MINIMAL_EXISTS)
   >> Know `?n. p n` >- PROVE_TAC []
   >> RW_TAC std_ss []
   >> Suff `~(m < minimal p) /\ ~(minimal p < m)` >- DECIDE_TAC
   >> PROVE_TAC []);

val MINIMAL_SUC = store_thm
  ("MINIMAL_SUC",
   ``!n p.
       (SUC n = minimal p) /\ p (SUC n) =
       ~p 0 /\ (n = minimal (p o SUC)) /\ p (SUC n)``,
   RW_TAC std_ss []
   >> EQ_TAC >|
   [RW_TAC std_ss [] >|
    [Know `0 < SUC n` >- DECIDE_TAC
     >> PROVE_TAC [MINIMAL_EXISTS],
     MATCH_MP_TAC MINIMAL_EQ_IMP
     >> RW_TAC std_ss [o_THM]
     >> Know `SUC n' < SUC n` >- DECIDE_TAC
     >> PROVE_TAC [MINIMAL_EXISTS]],
    RW_TAC std_ss []
    >> MATCH_MP_TAC MINIMAL_EQ_IMP
    >> RW_TAC std_ss []
    >> Cases_on `n` >- RW_TAC std_ss []
    >> Suff `~((p o SUC) n')` >- RW_TAC std_ss [o_THM]
    >> Know `n' < minimal (p o SUC)` >- DECIDE_TAC
    >> PROVE_TAC [MINIMAL_EXISTS]]);

val MINIMAL_EQ = store_thm
  ("MINIMAL_EQ",
   ``!p m. p m /\ (m = minimal p) = p m /\ (!n. n < m ==> ~p n)``,
   RW_TAC std_ss []
   >> REVERSE EQ_TAC >- PROVE_TAC [MINIMAL_EQ_IMP]
   >> RW_TAC std_ss []
   >> Know `?n. p n` >- PROVE_TAC []
   >> RW_TAC std_ss [MINIMAL_EXISTS]);

val MINIMAL_SUC_IMP = store_thm
  ("MINIMAL_SUC_IMP",
   ``!n p.
       p (SUC n) /\ ~p 0 /\ (n = minimal (p o SUC)) ==> (SUC n = minimal p)``,
   PROVE_TAC [MINIMAL_SUC]);

val _ = export_theory ();
