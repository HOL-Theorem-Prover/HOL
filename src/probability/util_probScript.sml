(* ------------------------------------------------------------------------- *)
(* Useful Theorems, some are taken from various theories by Hurd, Coble, ... *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib metisLib combinTheory seqTheory
     res_quanTools pairTheory arithmeticTheory realTheory realLib transcTheory
     real_sigmaTheory pred_setTheory pred_setLib;

val _ = new_theory "util_prob";
val _ = ParseExtras.temp_loose_equality()

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

(* ********************************************* *)
(*       Useful Theorems on Real Numbers         *)
(* ********************************************* *)

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

val REAL_NEG_NZ = store_thm
  ("REAL_NEG_NZ",``!x:real. x < 0 ==> x <> 0``,
 RW_TAC real_ss []
 >> `0 < -x` by RW_TAC real_ss [REAL_NEG_GT0]
 >> `-x <> 0` by FULL_SIMP_TAC real_ss [REAL_POS_NZ]
 >> `x <> 0` by (SPOSE_NOT_THEN ASSUME_TAC >> METIS_TAC [GSYM REAL_EQ_NEG,REAL_NEG_0]));

val REAL_LT_LMUL_0_NEG = store_thm
 ("REAL_LT_LMUL_0_NEG",``!x y:real. 0 < x * y /\ x < 0 ==> y < 0``,
 RW_TAC real_ss []
 >> SPOSE_NOT_THEN ASSUME_TAC
 >> FULL_SIMP_TAC real_ss [REAL_NOT_LT, GSYM REAL_NEG_GT0]
 >> METIS_TAC [REAL_MUL_LNEG, REAL_LT_IMP_LE, REAL_LE_MUL,
               REAL_NEG_GE0, REAL_NOT_LT]);

val REAL_LT_RMUL_0_NEG = store_thm
 ("REAL_LT_RMUL_0_NEG",``!x y:real. 0 < x * y /\ y < 0 ==> x < 0``,
 RW_TAC real_ss []
 >> SPOSE_NOT_THEN ASSUME_TAC
 >> FULL_SIMP_TAC real_ss [REAL_NOT_LT,GSYM REAL_NEG_GT0]
 >> METIS_TAC [REAL_MUL_RNEG, REAL_LT_IMP_LE, REAL_LE_MUL, REAL_NEG_GE0, REAL_NOT_LT]);

val REAL_LT_LMUL_NEG_0 = store_thm
 ("REAL_LT_LMUL_NEG_0",``!x y:real. x * y < 0 /\ 0 < x ==> y < 0``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_RMUL, REAL_LT_LMUL_0]);

val REAL_LT_RMUL_NEG_0 = store_thm
 ("REAL_LT_RMUL_NEG_0",``!x y:real. x * y < 0 /\ 0 < y ==> x < 0``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_LMUL, REAL_LT_RMUL_0]);

val REAL_LT_LMUL_NEG_0_NEG = store_thm
 ("REAL_LT_LMUL_NEG_0_NEG",``!x y:real. x * y < 0 /\ x < 0 ==> 0 < y``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_LMUL, REAL_LT_LMUL_0]);

val REAL_LT_RMUL_NEG_0_NEG = store_thm
 ("REAL_LT_RMUL_NEG_0_NEG",``!x y:real. x * y < 0 /\ y < 0 ==> 0 < x``,
 RW_TAC real_ss []
 >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_RMUL, REAL_LT_RMUL_0]);

val REAL_LT_RDIV_EQ_NEG = store_thm
 ("REAL_LT_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y /z < x <=> x * z < y)``,
  RW_TAC real_ss []
  >> `0<-z` by RW_TAC real_ss [REAL_NEG_GT0]
  >> `z<>0` by (METIS_TAC [REAL_LT_IMP_NE])
  >>EQ_TAC
  >- (RW_TAC real_ss []
      >> `y/z*(-z) < x*(-z)` by METIS_TAC [GSYM REAL_LT_RMUL]
      >> FULL_SIMP_TAC real_ss []
      >> METIS_TAC [REAL_DIV_RMUL, REAL_LT_NEG])
  >> RW_TAC real_ss []
  >> `-y < x*(-z)` by FULL_SIMP_TAC real_ss [REAL_LT_NEG]
  >> `-y * inv(-z) < x` by METIS_TAC [GSYM REAL_LT_LDIV_EQ, real_div]
  >> METIS_TAC [REAL_NEG_INV, REAL_NEG_MUL2, GSYM real_div]);

val REAL_LE_RDIV_EQ_NEG = store_thm
 ("REAL_LE_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y /z <= x <=> x * z <= y)``,
  RW_TAC real_ss []
  >> `0 < -z` by RW_TAC real_ss [REAL_NEG_GT0]
  >> `z <> 0` by (METIS_TAC [REAL_LT_IMP_NE])
  >>EQ_TAC
  >- (RW_TAC real_ss []
      >> `y / z * (-z) <= x * (-z)` by METIS_TAC [GSYM REAL_LE_RMUL]
      >> FULL_SIMP_TAC real_ss []
      >> METIS_TAC [REAL_DIV_RMUL,REAL_LE_NEG])
  >> RW_TAC real_ss []
  >> `-y <= x * (-z)` by FULL_SIMP_TAC real_ss [REAL_LE_NEG]
  >> `-y * inv (-z) <= x` by METIS_TAC [GSYM REAL_LE_LDIV_EQ, real_div]
  >> METIS_TAC [REAL_NEG_INV, REAL_NEG_MUL2, GSYM real_div]);

val POW_POS_EVEN = store_thm
 ("POW_POS_EVEN",``!x:real. x < 0 ==> ((0 < x pow n) = (EVEN n))``,
  Induct_on `n`
  >- RW_TAC std_ss [pow,REAL_LT_01,EVEN]
  >> RW_TAC std_ss [pow,EVEN]
  >> EQ_TAC
  >- METIS_TAC [REAL_LT_ANTISYM, REAL_LT_RMUL_0_NEG, REAL_MUL_COMM]
  >> RW_TAC std_ss []
  >> `x pow n <= 0` by METIS_TAC [real_lt]
  >> `x pow n <> 0` by METIS_TAC [POW_NZ, REAL_LT_IMP_NE]
  >> `x pow n < 0` by METIS_TAC [REAL_LT_LE]
  >> METIS_TAC [REAL_NEG_GT0, REAL_NEG_MUL2, REAL_LT_MUL]);

val POW_NEG_ODD = store_thm
 ("POW_NEG_ODD",``!x:real. x < 0 ==> ((x pow n < 0) = (ODD n))``,
  Induct_on `n`
  >- RW_TAC std_ss [pow,GSYM real_lte,REAL_LE_01]
  >> RW_TAC std_ss [pow,ODD]
  >> EQ_TAC
  >- METIS_TAC [REAL_LT_RMUL_NEG_0_NEG, REAL_MUL_COMM, REAL_LT_ANTISYM]
  >> RW_TAC std_ss []
  >> `0 <= x pow n` by METIS_TAC [real_lt]
  >> `x pow n <> 0` by METIS_TAC [POW_NZ, REAL_LT_IMP_NE]
  >> `0 < x pow n` by METIS_TAC [REAL_LT_LE]
  >> METIS_TAC [REAL_NEG_GT0, REAL_MUL_LNEG, REAL_LT_MUL]);

val LOGR_MONO_LE = store_thm
 ("LOGR_MONO_LE",``!x:real y b. 0 < x /\ 0 < y /\ 1 < b ==> (logr b x <= logr b y <=> x <= y)``,
  RW_TAC std_ss [logr_def,real_div]
  >> `0 < ln b` by METIS_TAC [REAL_LT_01, LN_1, REAL_LT_TRANS, LN_MONO_LT]
  >> METIS_TAC [REAL_LT_INV_EQ, REAL_LE_RMUL, LN_MONO_LE]);

val LOGR_MONO_LE_IMP = store_thm
 ("LOGR_MONO_LE_IMP",``!x:real y b. 0 < x /\ x <= y /\ 1 <= b ==> (logr b x <= logr b y)``,
  RW_TAC std_ss [logr_def,real_div]
  >> `0 <= ln b` by METIS_TAC [REAL_LT_01, LN_1, REAL_LTE_TRANS, LN_MONO_LE]
  >> METIS_TAC [REAL_LE_INV_EQ, REAL_LE_RMUL_IMP, LN_MONO_LE, REAL_LTE_TRANS]);

(* ********************************************* *)
(*   The mininal element in num sets             *)
(* ********************************************* *)

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

(* ------------------------------------------------------------------------- *)
(*   Disjoint subsets (from lebesgue_measureTheory)                          *)
(* ------------------------------------------------------------------------- *)

(* moved here from lebesgue_measureTheory *)
val disjoint_def = Define
   `disjoint A = !a b. a IN A /\ b IN A /\ (a <> b) ==> DISJOINT a b`;

val disjointI = store_thm
  ("disjointI",
  ``!A. (!a b . a IN A ==> b IN A ==> (a <> b) ==> DISJOINT a b) ==> disjoint A``,
    METIS_TAC [disjoint_def]);

val disjointD = store_thm
  ("disjointD",
  ``!A a b. disjoint A ==> a IN A ==> b IN A ==> (a <> b) ==> DISJOINT a b``,
    METIS_TAC [disjoint_def]);

val disjoint_empty = store_thm
  ("disjoint_empty", ``disjoint {}``,
    SET_TAC [disjoint_def]);

val disjoint_union = store_thm
  ("disjoint_union",
  ``!A B. disjoint A /\ disjoint B /\ (BIGUNION A INTER BIGUNION B = {}) ==>
          disjoint (A UNION B)``,
    SET_TAC [disjoint_def]);

val disjoint_sing = store_thm
  ("disjoint_sing", ``!a. disjoint {a}``,
    SET_TAC [disjoint_def]);

(* ------------------------------------------------------------------------- *)
(* Segment of natural numbers starting at a specific number                  *)
(* ------------------------------------------------------------------------- *)

val from_def = Define
   `from n = {m:num | n <= m}`;

val FROM_0 = store_thm ("FROM_0",
  ``from 0 = univ(:num)``,
    REWRITE_TAC [from_def, ZERO_LESS_EQ, GSPEC_T]);

val IN_FROM = store_thm ("IN_FROM",
  ``!m n. m IN from n <=> n <= m``,
    SIMP_TAC std_ss [from_def, GSPECIFICATION]);

val tail_not_empty = store_thm
  ("tail_not_empty", ``!A m:num. {A n | m <= n} <> {}``,
    RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, GSPECIFICATION]
 >> Q.EXISTS_TAC `(SUC m)` >> RW_TAC arith_ss []);

val tail_countable = store_thm
  ("tail_countable", ``!A m:num. countable {A n | m <= n}``,
    rpt GEN_TAC
 >> Suff `{A n | m <= n} = IMAGE A {n | m <= n}`
 >- PROVE_TAC [COUNTABLE_IMAGE_NUM]
 >> RW_TAC std_ss [EXTENSION, IN_IMAGE, GSPECIFICATION]);

val DISJOINT_COUNT_FROM = store_thm
  ("DISJOINT_COUNT_FROM", ``!n. DISJOINT (count n) (from n)``,
    RW_TAC arith_ss [from_def, count_def, DISJOINT_DEF, Once EXTENSION, NOT_IN_EMPTY,
                     GSPECIFICATION, IN_INTER]);

val DISJOINT_FROM_COUNT = store_thm
  ("DISJOINT_FROM_COUNT", ``!n. DISJOINT (from n) (count n)``,
    RW_TAC std_ss [Once DISJOINT_SYM, DISJOINT_COUNT_FROM]);

val UNION_COUNT_FROM = store_thm
  ("UNION_COUNT_FROM", ``!n. (count n) UNION (from n) = UNIV``,
    RW_TAC arith_ss [from_def, count_def, Once EXTENSION, NOT_IN_EMPTY,
                     GSPECIFICATION, IN_UNION, IN_UNIV]);

val UNION_FROM_COUNT = store_thm
  ("UNION_FROM_COUNT", ``!n. (from n) UNION (count n) = UNIV``,
    RW_TAC std_ss [Once UNION_COMM, UNION_COUNT_FROM]);

val _ = export_theory ();
