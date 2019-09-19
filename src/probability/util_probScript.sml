(* ------------------------------------------------------------------------- *)
(* Useful Theorems, some are taken from various theories by Hurd and Coble   *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(*                                                                           *)
(* Extended by Chun Tian (2019)                                              *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open metisLib pairTheory combinTheory pred_setTheory pred_setLib
     arithmeticTheory realTheory realLib transcTheory seqTheory
     real_sigmaTheory numpairTheory hurdUtils;

val _ = new_theory "util_prob";

(* ------------------------------------------------------------------------- *)
(* bool theory subtypes.                                                     *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "->" (Infixr 250);
val _ = overload_on ("->",
      ``FUNSET  :'a set -> 'b set -> ('a -> 'b) set``);

val _ = overload_on ("-->", (* "Pi" in Isabelle's FuncSet.thy *)
      ``DFUNSET :'a set -> ('a -> 'b set) -> ('a -> 'b) set``);

(* RIGHTWARDS ARROW *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x2192, tmnm = "->"};

(* LONG RIGHTWARDS ARROW *)
val _ = Unicode.unicode_version {u = UTF8.chr 0x27F6, tmnm = "-->"};

val pair_def = Define
   `pair (X :'a -> bool) (Y :'b -> bool) = \(x, y). x IN X /\ y IN Y`;

val IN_PAIR = store_thm
  ("IN_PAIR", ``!(x : 'a # 'b) X Y. x IN pair X Y <=> FST x IN X /\ SND x IN Y``,
    Cases >> RW_TAC std_ss [pair_def, SPECIFICATION]);

val PAIR_UNIV = store_thm
  ("PAIR_UNIV", ``pair UNIV UNIV = (UNIV :'a # 'b -> bool)``,
    RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_PAIR, IN_UNIV]);

val PAIRED_BETA_THM = store_thm
  ("PAIRED_BETA_THM", ``!f z. UNCURRY f z = f (FST z) (SND z)``,
    STRIP_TAC >> Cases >> RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* ----- Defining real-valued power, log, and log base 2 functions --------- *)
(* ------------------------------------------------------------------------- *)

val _ = set_fixity "powr" (Infixr 700);

val powr_def = Define `x powr a = exp (a * ln x)`;
val logr_def = Define `logr a x = ln x / ln a`;
val lg_def   = Define `lg x = logr 2 x`;

val lg_1 = store_thm
  ("lg_1", ``lg 1 = 0``,
   RW_TAC real_ss [lg_def, logr_def, LN_1]);

val logr_1 = store_thm
  ("logr_1", ``!b. logr b 1 = 0``,
   RW_TAC real_ss [logr_def, LN_1]);

val lg_nonzero = store_thm
  ("lg_nonzero", ``!x. x <> 0 /\ 0 <= x ==> (lg x <> 0 <=> x <> 1)``,
    RW_TAC std_ss [REAL_ARITH ``x <> 0 /\ 0 <= x <=> 0 < x``]
 >> RW_TAC std_ss [GSYM lg_1]
 >> RW_TAC std_ss [lg_def, logr_def, real_div, REAL_EQ_RMUL, REAL_INV_EQ_0]
 >> (MP_TAC o Q.SPECL [`2`, `1`]) LN_INJ >> RW_TAC real_ss [LN_1]
 >> RW_TAC std_ss [GSYM LN_1]
 >> MATCH_MP_TAC LN_INJ
 >> RW_TAC real_ss []);

val lg_mul = store_thm
  ("lg_mul", ``!x y. 0 < x /\ 0 < y ==> (lg (x * y) = lg x + lg y)``,
   RW_TAC real_ss [lg_def, logr_def, LN_MUL]);

val logr_mul = store_thm
  ("logr_mul", ``!b x y. 0 < x /\ 0 < y ==> (logr b (x * y) = logr b x + logr b y)``,
   RW_TAC real_ss [logr_def, LN_MUL]);

val lg_2 = store_thm
  ("lg_2", ``lg 2 = 1``,
   RW_TAC real_ss [lg_def, logr_def]
   >> MATCH_MP_TAC REAL_DIV_REFL
   >> (ASSUME_TAC o Q.SPECL [`1`, `2`]) LN_MONO_LT
   >> FULL_SIMP_TAC real_ss [LN_1]
   >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
   >> MATCH_MP_TAC REAL_LT_IMP_NE
   >> ASM_REWRITE_TAC []);

val lg_inv = store_thm
  ("lg_inv", ``!x. 0 < x ==> (lg (inv x) = ~lg x)``,
   RW_TAC real_ss [lg_def, logr_def, LN_INV, real_div]);

val logr_inv = store_thm
  ("logr_inv", ``!b x. 0 < x ==> (logr b (inv x) = ~ logr b x)``,
   RW_TAC real_ss [logr_def, LN_INV, real_div]);

val logr_div = store_thm
  ("logr_div", ``!b x y. 0 < x /\ 0 < y ==> (logr b (x/y) = logr b x - logr b y)``,
   RW_TAC real_ss [real_div, logr_mul, logr_inv, GSYM real_sub]);

val neg_lg = store_thm
  ("neg_lg", ``!x. 0 < x ==> ((~(lg x)) = lg (inv x))``,
   RW_TAC real_ss [lg_def, logr_def, real_div]
   >> `~(ln x * inv (ln 2)) = (~ ln x) * inv (ln 2)` by REAL_ARITH_TAC
   >> POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   >> RW_TAC real_ss [REAL_EQ_RMUL]
   >> DISJ2_TAC >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> MATCH_MP_TAC LN_INV
   >> RW_TAC std_ss []);

val neg_logr = store_thm
  ("neg_logr", ``!b x. 0 < x ==> ((~(logr b x)) = logr b (inv x))``,
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

val NUM_2D_BIJ = store_thm
  ("NUM_2D_BIJ",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS (UNIV : num -> bool))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   >> Reverse CONJ_TAC
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
   >> Reverse CONJ_TAC
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
   >> Reverse CONJ_TAC
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
   >> Reverse CONJ_TAC
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

(* Two concrete NUM_2D_BIJ lemmas using numpairTheory *)

val NUM_2D_BIJ_nfst_nsnd = store_thm
  ("NUM_2D_BIJ_nfst_nsnd", ``BIJ (\n. (nfst n, nsnd n)) UNIV (UNIV CROSS UNIV)``,
    REWRITE_TAC [BIJ_ALT, IN_CROSS, IN_FUNSET, IN_UNIV]
 >> BETA_TAC >> GEN_TAC >> Cases_on `y`
 >> SIMP_TAC std_ss [EXISTS_UNIQUE_ALT]
 >> Q.EXISTS_TAC `npair q r`
 >> GEN_TAC >> STRIP_ASSUME_TAC (Q.SPEC `x'` npair_cases)
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> REWRITE_TAC [nfst_npair, nsnd_npair, npair_11]);

val NUM_2D_BIJ_npair = store_thm
  ("NUM_2D_BIJ_npair", ``BIJ (UNCURRY npair) (UNIV CROSS UNIV) UNIV``,
    REWRITE_TAC [BIJ_ALT, IN_CROSS, IN_FUNSET, IN_UNIV, UNCURRY]
 >> GEN_TAC >> SIMP_TAC std_ss [EXISTS_UNIQUE_ALT]
 >> Q.EXISTS_TAC `nfst y, nsnd y`
 >> GEN_TAC >> STRIP_ASSUME_TAC (Q.SPEC `y` npair_cases)
 >> POP_ASSUM (REWRITE_TAC o wrap)
 >> REWRITE_TAC [nfst_npair, nsnd_npair, npair_11]
 >> Cases_on `x'` >> SIMP_TAC std_ss []);

val prod_sets_def = Define `
    prod_sets a b = {s CROSS t | s IN a /\ t IN b}`;

(* (not used anywhere)
val IN_o = store_thm
  ("IN_o", ``!x f s. x IN (s o f) = f x IN s``,
    RW_TAC std_ss [SPECIFICATION, o_THM]);
 *)

val IN_PROD_SETS = store_thm
  ("IN_PROD_SETS",
   ``!s a b. s IN prod_sets a b <=> ?t u. (s = t CROSS u) /\ t IN a /\ u IN b``,
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
        (\s. !f. (!x. f x IN {} INSERT s) /\
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
   ``!r: real. (r * r = r) <=> (r = 0) \/ (r = 1)``,
   GEN_TAC
   >> Reverse EQ_TAC
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

val INF_DEF_ALT = store_thm (* c.f. "inf_alt" in seqTheory *)
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

Theorem REAL_NEG_NZ :
    !x:real. x < 0 ==> x <> 0
Proof
    GEN_TAC >> DISCH_TAC
 >> MATCH_MP_TAC REAL_LT_IMP_NE
 >> ASM_REWRITE_TAC []
QED

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
  ("REAL_LT_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y / z < x <=> x * z < y)``,
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
  ("REAL_LE_RDIV_EQ_NEG", ``!x y z. z < 0:real ==> (y / z <= x <=> x * z <= y)``,
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
  ("POW_POS_EVEN",``!x:real. x < 0 ==> ((0 < x pow n) <=> (EVEN n))``,
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
  ("POW_NEG_ODD",``!x:real. x < 0 ==> ((x pow n < 0) <=> (ODD n))``,
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
  ("MINIMAL_EXISTS0", ``(?(n:num). P n) = (?n. P n /\ (!m. m < n ==> ~(P m)))``,
    Reverse EQ_TAC >- PROVE_TAC []
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
       (SUC n = minimal p) /\ p (SUC n) <=>
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
  ``!p m. p m /\ (m = minimal p) <=> p m /\ (!n. n < m ==> ~p n)``,
    RW_TAC std_ss []
 >> Reverse EQ_TAC >- PROVE_TAC [MINIMAL_EQ_IMP]
 >> RW_TAC std_ss []
 >> Know `?n. p n` >- PROVE_TAC []
 >> RW_TAC std_ss [MINIMAL_EXISTS]);

val MINIMAL_SUC_IMP = store_thm
  ("MINIMAL_SUC_IMP",
  ``!n p. p (SUC n) /\ ~p 0 /\ (n = minimal (p o SUC)) ==> (SUC n = minimal p)``,
    PROVE_TAC [MINIMAL_SUC]);

(* ------------------------------------------------------------------------- *)
(*   Disjoint subsets (from HVG's lebesgue_measureTheory)                    *)
(* ------------------------------------------------------------------------- *)

Theorem DISJOINT_RESTRICT_L :
  !s t c. DISJOINT s t ==> DISJOINT (s INTER c) (t INTER c)
Proof SET_TAC []
QED

Theorem DISJOINT_RESTRICT_R :
  !s t c. DISJOINT s t ==> DISJOINT (c INTER s) (c INTER t)
Proof SET_TAC []
QED

Theorem SUBSET_RESTRICT_L :
  !r s t. s SUBSET t ==> (s INTER r) SUBSET (t INTER r)
Proof SET_TAC []
QED

Theorem SUBSET_RESTRICT_R :
  !r s t. s SUBSET t ==> (r INTER s) SUBSET (r INTER t)
Proof SET_TAC []
QED

Theorem SUBSET_RESTRICT_DIFF :
  !r s t. s SUBSET t ==> (r DIFF t) SUBSET (r DIFF s)
Proof SET_TAC []
QED

Theorem SUBSET_INTER_SUBSET_L :
  !r s t. s SUBSET t ==> (s INTER r) SUBSET t
Proof SET_TAC []
QED

Theorem SUBSET_INTER_SUBSET_R :
  !r s t. s SUBSET t ==> (r INTER s) SUBSET t
Proof SET_TAC []
QED

Theorem SUBSET_MONO_DIFF :
  !r s t. s SUBSET t ==> (s DIFF r) SUBSET (t DIFF r)
Proof SET_TAC []
QED

Theorem SUBSET_DIFF_SUBSET :
  !r s t. s SUBSET t ==> (s DIFF r) SUBSET t
Proof SET_TAC []
QED

Theorem SUBSET_DIFF_DISJOINT :
  !s1 s2 s3. (s1 SUBSET (s2 DIFF s3)) ==> DISJOINT s1 s3
Proof
    PROVE_TAC [SUBSET_DIFF]
QED

val disjoint_def = Define
   `disjoint A = !a b. a IN A /\ b IN A /\ (a <> b) ==> DISJOINT a b`;

(* |- !A. disjoint A <=> !a b. a IN A /\ b IN A /\ a <> b ==> (a INTER b = {} ) *)
val disjoint = save_thm
  ("disjoint", REWRITE_RULE [DISJOINT_DEF] disjoint_def);

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

val disjoint_same = store_thm
  ("disjoint_same", ``!s t. (s = t) ==> disjoint {s; t}``,
    RW_TAC std_ss [IN_INSERT, IN_SING, disjoint_def]);

val disjoint_two = store_thm
  ("disjoint_two", ``!s t. s <> t /\ DISJOINT s t ==> disjoint {s; t}``,
    RW_TAC std_ss [IN_INSERT, IN_SING, disjoint_def] >- art []
 >> ASM_REWRITE_TAC [DISJOINT_SYM]);

val disjoint_image = store_thm (* new *)
  ("disjoint_image",
  ``!f. (!i j. i <> j ==> DISJOINT (f i) (f j)) ==> disjoint (IMAGE f UNIV)``,
    rpt STRIP_TAC
 >> MATCH_MP_TAC disjointI
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> METIS_TAC []);

val disjoint_insert_imp = store_thm (* new *)
  ("disjoint_insert_imp",
  ``!e c. disjoint (e INSERT c) ==> disjoint c``,
    RW_TAC std_ss [disjoint_def]
 >> FIRST_ASSUM MATCH_MP_TAC
 >> METIS_TAC [IN_INSERT]);

val disjoint_insert_notin = store_thm (* new *)
  ("disjoint_insert_notin",
  ``!e c. disjoint (e INSERT c) /\ e NOTIN c ==> !s. s IN c ==> DISJOINT e s``,
    RW_TAC std_ss [disjoint_def]
 >> FIRST_ASSUM MATCH_MP_TAC
 >> METIS_TAC [IN_INSERT]);

val disjoint_insert = store_thm (* new *)
  ("disjoint_insert",
  ``!e c. disjoint c /\ (!x. x IN c ==> DISJOINT x e) ==> disjoint (e INSERT c)``,
    rpt STRIP_TAC
 >> Know `e INSERT c = {e} UNION c` >- SET_TAC [] >> Rewr'
 >> MATCH_MP_TAC disjoint_union
 >> art [disjoint_sing, BIGUNION_SING]
 >> ASM_SET_TAC []);

val disjoint_restrict = store_thm (* new *)
  ("disjoint_restrict",
  ``!e c. disjoint c ==> disjoint (IMAGE ($INTER e) c)``,
    RW_TAC std_ss [disjoint_def, IN_IMAGE, o_DEF]
 >> MATCH_MP_TAC DISJOINT_RESTRICT_R
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
 >> CCONTR_TAC >> fs []);

(* ------------------------------------------------------------------------- *)
(*  Some lemmas needed by CARATHEODORY in measureTheory (author: Chun Tian)  *)
(* ------------------------------------------------------------------------- *)

val DINTER_IMP_FINITE_INTER = store_thm
  ("DINTER_IMP_FINITE_INTER",
  ``!sts f. (!s t. s IN sts /\ t IN sts ==> s INTER t IN sts) /\
            f IN (UNIV -> sts)
        ==> !n. 0 < n ==> BIGINTER (IMAGE f (count n)) IN sts``,
    rpt GEN_TAC
 >> STRIP_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> fs [IN_FUNSET, IN_UNIV]
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY,
                   BIGINTER_INSERT, IMAGE_EMPTY, BIGINTER_EMPTY, INTER_UNIV]
 >> fs [COUNT_SUC]);

(* Dual lemma of above, used in "ring_and_semiring" *)
val DUNION_IMP_FINITE_UNION = store_thm
  ("DUNION_IMP_FINITE_UNION",
  ``!sts f. (!s t. s IN sts /\ t IN sts ==> s UNION t IN sts) ==>
            !n. 0 < n /\ (!i. i < n ==> f i IN sts) ==>
                BIGUNION (IMAGE f (count n)) IN sts``,
    rpt GEN_TAC
 >> STRIP_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> fs [IN_FUNSET, IN_UNIV]
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY,
                   BIGUNION_INSERT, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
 >> fs [COUNT_SUC]);

val GEN_DIFF_INTER = store_thm
  ("GEN_DIFF_INTER",
  ``!sp s t. s SUBSET sp /\ t SUBSET sp ==> (s DIFF t = s INTER (sp DIFF t))``,
    rpt STRIP_TAC
 >> ASM_SET_TAC []);

val GEN_COMPL_UNION = store_thm
  ("GEN_COMPL_UNION",
  ``!sp s t. s SUBSET sp /\ t SUBSET sp ==>
             (sp DIFF (s UNION t) = (sp DIFF s) INTER (sp DIFF t))``,
    rpt STRIP_TAC
 >> ASM_SET_TAC [])

val GEN_COMPL_INTER = store_thm
  ("GEN_COMPL_INTER",
  ``!sp s t. s SUBSET sp /\ t SUBSET sp ==>
             (sp DIFF (s INTER t) = (sp DIFF s) UNION (sp DIFF t))``,
    rpt STRIP_TAC
 >> ASM_SET_TAC [])

val COMPL_BIGINTER_IMAGE = store_thm
  ("COMPL_BIGINTER_IMAGE",
  ``!f. COMPL (BIGINTER (IMAGE f univ(:num))) = BIGUNION (IMAGE (COMPL o f) univ(:num))``,
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]);

val COMPL_BIGUNION_IMAGE = store_thm
  ("COMPL_BIGUNION_IMAGE",
  ``!f. COMPL (BIGUNION (IMAGE f univ(:num))) = BIGINTER (IMAGE (COMPL o f) univ(:num))``,
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]);

val GEN_COMPL_BIGINTER_IMAGE = store_thm
  ("GEN_COMPL_BIGINTER_IMAGE",
  ``!sp f. (!n. f n SUBSET sp) ==>
           (sp DIFF (BIGINTER (IMAGE f univ(:num))) =
            BIGUNION (IMAGE (\n. sp DIFF (f n)) univ(:num)))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >- (Q.EXISTS_TAC `y` >> art [])
 >> Q.EXISTS_TAC `n` >> art []);

val GEN_COMPL_BIGUNION_IMAGE = store_thm
  ("GEN_COMPL_BIGUNION_IMAGE",
  ``!sp f. (!n. f n SUBSET sp) ==>
           (sp DIFF (BIGUNION (IMAGE f univ(:num))) =
            BIGINTER (IMAGE (\n. sp DIFF (f n)) univ(:num)))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >> METIS_TAC []);

val COMPL_BIGINTER = store_thm
  ("COMPL_BIGINTER",
  ``!c. COMPL (BIGINTER c) = BIGUNION (IMAGE COMPL c)``,
    RW_TAC std_ss [EXTENSION, IN_COMPL, IN_BIGINTER, IN_BIGUNION_IMAGE]);

val COMPL_BIGUNION = store_thm
  ("COMPL_BIGUNION",
  ``!c. c <> {} ==> (COMPL (BIGUNION c) = BIGINTER (IMAGE COMPL c))``,
    RW_TAC std_ss [NOT_IN_EMPTY, EXTENSION, IN_COMPL, IN_BIGUNION, IN_BIGINTER_IMAGE]
 >> EQ_TAC >> rpt STRIP_TAC
 >> PROVE_TAC []);

val GEN_COMPL_BIGINTER = store_thm
  ("GEN_COMPL_BIGINTER",
  ``!sp c. (!x. x IN c ==> x SUBSET sp) ==>
           (sp DIFF (BIGINTER c) = BIGUNION (IMAGE (\x. sp DIFF x) c))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER, IN_BIGUNION_IMAGE]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >- (Q.EXISTS_TAC `P` >> art [])
 >> Q.EXISTS_TAC `x'` >> art []);

val GEN_COMPL_BIGUNION = store_thm
  ("GEN_COMPL_BIGUNION",
  ``!sp c. c <> {} /\ (!x. x IN c ==> x SUBSET sp) ==>
           (sp DIFF (BIGUNION c) = BIGINTER (IMAGE (\x. sp DIFF x) c))``,
    RW_TAC std_ss [EXTENSION, IN_DIFF, IN_BIGINTER, IN_BIGUNION, IN_BIGINTER_IMAGE,
                   NOT_IN_EMPTY]
 >> EQ_TAC >> rpt STRIP_TAC >> art []
 >> METIS_TAC []);

val GEN_COMPL_FINITE_UNION = store_thm
  ("GEN_COMPL_FINITE_UNION",
  ``!sp f n. 0 < n ==> (sp DIFF BIGUNION (IMAGE f (count n)) =
                        BIGINTER (IMAGE (\i. sp DIFF f i) (count n)))``,
    NTAC 2 GEN_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY, BIGINTER_SING,
                   BIGUNION_INSERT, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
 >> fs [COUNT_SUC]
 >> ONCE_REWRITE_TAC [UNION_COMM]
 >> ASM_REWRITE_TAC [DIFF_UNION]
 >> REWRITE_TAC [DIFF_INTER]
 >> Suff `(BIGINTER (IMAGE (\i. sp DIFF f i) (count n)) DIFF f n) SUBSET sp`
 >- (KILL_TAC >> DISCH_THEN (ASSUME_TAC o (MATCH_MP SUBSET_INTER2)) >> ASM_SET_TAC [])
 >> MATCH_MP_TAC SUBSET_TRANS
 >> Q.EXISTS_TAC `BIGINTER (IMAGE (\i. sp DIFF f i) (count n))`
 >> REWRITE_TAC [DIFF_SUBSET]
 >> REWRITE_TAC [SUBSET_DEF, IN_BIGINTER_IMAGE, IN_COUNT] >> BETA_TAC
 >> RW_TAC std_ss [IN_DIFF]
 >> RES_TAC);

val BIGINTER_PAIR = store_thm
  ("BIGINTER_PAIR",
  ``!s t. BIGINTER {s; t} = s INTER t``,
    RW_TAC std_ss [EXTENSION, IN_BIGINTER, IN_INTER, IN_INSERT, NOT_IN_EMPTY]
 >> PROVE_TAC []);

val DIFF_INTER_PAIR = store_thm
  ("DIFF_INTER_PAIR",
  ``!sp x y. sp DIFF (x INTER y) = (sp DIFF x) UNION (sp DIFF y)``,
    rpt GEN_TAC
 >> REWRITE_TAC [REWRITE_RULE [BIGINTER_PAIR] (Q.SPECL [`sp`, `{x; y}`] DIFF_BIGINTER1)]
 >> REWRITE_TAC [EXTENSION, IN_UNION, IN_BIGUNION_IMAGE]
 >> BETA_TAC
 >> GEN_TAC >> EQ_TAC >> rpt STRIP_TAC
 >| [ fs [IN_INSERT] >> PROVE_TAC [],
      Q.EXISTS_TAC `x` >> ASM_REWRITE_TAC [IN_INSERT],
      Q.EXISTS_TAC `y` >> ASM_REWRITE_TAC [IN_INSERT] ]);

val GEN_COMPL_FINITE_INTER = store_thm
  ("GEN_COMPL_FINITE_INTER",
  ``!sp f n. 0 < n ==> (sp DIFF BIGINTER (IMAGE f (count n)) =
                        BIGUNION (IMAGE (\i. sp DIFF f i) (count n)))``,
    NTAC 2 GEN_TAC
 >> Induct_on `n`
 >> RW_TAC arith_ss []
 >> STRIP_ASSUME_TAC (Q.SPEC `n` LESS_0_CASES)
 >- RW_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, IMAGE_EMPTY, BIGINTER_SING,
                   BIGUNION_INSERT, IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY]
 >> fs [COUNT_SUC]
 >> ASM_REWRITE_TAC [DIFF_INTER_PAIR]);

(* This proof is provided by Thomas Tuerk, needed by SETS_TO_DISJOINT_SETS *)
val BIGUNION_IMAGE_COUNT_IMP_UNIV = store_thm
  ("BIGUNION_IMAGE_COUNT_IMP_UNIV",
  ``!f g. (!n. BIGUNION (IMAGE g (count n)) = BIGUNION (IMAGE f (count n))) ==>
          (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
 (* proof *)
   `!f g. (!n. BIGUNION (IMAGE g (count n)) = BIGUNION (IMAGE f (count n))) ==>
          (BIGUNION (IMAGE f UNIV) SUBSET BIGUNION (IMAGE g UNIV))`
       suffices_by PROVE_TAC [SUBSET_ANTISYM]
 >> REWRITE_TAC [SUBSET_DEF]
 >> REPEAT STRIP_TAC
 >> rename1 `e IN BIGUNION _`
 >> Know `?n. e IN BIGUNION (IMAGE f (count n))`
 >- (FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_COUNT] \\
     rename1 `e IN f n'` \\
     Q.EXISTS_TAC `SUC n'` \\
     Q.EXISTS_TAC `n'` \\
     ASM_SIMP_TAC arith_ss [])
 >> STRIP_TAC
 >> `e IN BIGUNION (IMAGE g (count n))` by PROVE_TAC []
 >> FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, PULL_EXISTS, IN_UNIV]
 >> METIS_TAC []);

val BIGUNION_OVER_INTER_L = store_thm
  ("BIGUNION_OVER_INTER_L",
  ``!f d. BIGUNION (IMAGE f univ(:num)) INTER d =
          BIGUNION (IMAGE (\i. f i INTER d) univ(:num))``,
    rpt GEN_TAC
 >> REWRITE_TAC [EXTENSION]
 >> GEN_TAC >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [IN_BIGUNION, IN_INTER, IN_IMAGE] \\
      `x IN (f x' INTER d)` by PROVE_TAC [IN_INTER] \\
      Q.EXISTS_TAC `f x' INTER d` >> art [] \\
      Q.EXISTS_TAC `x'` >> art [],
      (* goal 2 (of 2) *)
      RW_TAC std_ss [IN_BIGUNION, IN_INTER, IN_IMAGE] >|
      [ fs [IN_INTER] >> Q.EXISTS_TAC `f i` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `i` >> REWRITE_TAC [],
        PROVE_TAC [IN_INTER] ] ]);

val BIGUNION_OVER_INTER_R = store_thm
  ("BIGUNION_OVER_INTER_R",
  ``!f d. d INTER BIGUNION (IMAGE f univ(:num)) =
          BIGUNION (IMAGE (\i. d INTER f i) univ(:num))``,
    rpt GEN_TAC
 >> REWRITE_TAC [EXTENSION]
 >> GEN_TAC >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV] \\
      `x IN (d INTER f x')` by PROVE_TAC [IN_INTER] \\
      Q.EXISTS_TAC `d INTER f x'` >> art [] \\
      Q.EXISTS_TAC `x'` >> art [],
      (* goal 2 (of 2) *)
      RW_TAC std_ss [IN_BIGUNION, IN_INTER, IN_IMAGE, IN_UNIV] >|
      [ fs [IN_INTER] >> Q.EXISTS_TAC `f i` >> ASM_REWRITE_TAC [] \\
        Q.EXISTS_TAC `i` >> REWRITE_TAC [],
        PROVE_TAC [IN_INTER] ] ]);

val BIGUNION_OVER_DIFF = store_thm
  ("BIGUNION_OVER_DIFF",
  ``!f d. BIGUNION (IMAGE f univ(:num)) DIFF d =
          BIGUNION (IMAGE (\i. f i DIFF d) univ(:num))``,
    rpt GEN_TAC
 >> REWRITE_TAC [EXTENSION]
 >> GEN_TAC >> EQ_TAC
 >| [ (* goal 1 (of 2) *)
      RW_TAC std_ss [IN_BIGUNION, IN_DIFF, IN_IMAGE, IN_UNIV] \\
      `x IN (f x' DIFF d)` by PROVE_TAC [IN_DIFF] \\
      Q.EXISTS_TAC `f x' DIFF d` >> art [] \\
      Q.EXISTS_TAC `x'` >> art [],
      (* goal 2 (of 2) *)
      RW_TAC std_ss [IN_BIGUNION, IN_DIFF, IN_IMAGE, IN_UNIV] >|
      [ fs [IN_DIFF] >> Q.EXISTS_TAC `f i` >> art [] \\
        Q.EXISTS_TAC `i` >> REWRITE_TAC [],
        PROVE_TAC [IN_DIFF] ] ]);

val BIGUNION_IMAGE_OVER_INTER_L = store_thm
  ("BIGUNION_IMAGE_OVER_INTER_L",
  ``!f n d. BIGUNION (IMAGE f (count n)) INTER d =
            BIGUNION (IMAGE (\i. f i INTER d) (count n))``,
    rpt GEN_TAC
 >> REWRITE_TAC [EXTENSION]
 >> GEN_TAC >> EQ_TAC
 >| [ RW_TAC std_ss [IN_BIGUNION, IN_INTER, IN_IMAGE] \\
      `x IN (f x' INTER d)` by PROVE_TAC [IN_INTER] \\
      Q.EXISTS_TAC `f x' INTER d` >> art [] \\
      Q.EXISTS_TAC `x'` >> art [],
      RW_TAC std_ss [IN_BIGUNION, IN_INTER, IN_IMAGE] >|
      [ fs [IN_INTER] >> Q.EXISTS_TAC `f i` >> art [] \\
        Q.EXISTS_TAC `i` >> art [],
        PROVE_TAC [IN_INTER] ] ]);

val BIGUNION_IMAGE_OVER_INTER_R = store_thm
  ("BIGUNION_IMAGE_OVER_INTER_R",
  ``!f n d. d INTER BIGUNION (IMAGE f (count n)) =
            BIGUNION (IMAGE (\i. d INTER f i) (count n))``,
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [INTER_COMM]
 >> REWRITE_TAC [BIGUNION_IMAGE_OVER_INTER_L]);

val BIGINTER_IMAGE_OVER_INTER_L = store_thm
  ("BIGINTER_IMAGE_OVER_INTER_L",
  ``!f n d. 0 < n ==>
           (BIGINTER (IMAGE f (count n)) INTER d =
            BIGINTER (IMAGE (\i. f i INTER d) (count n)))``,
    rpt STRIP_TAC
 >> REWRITE_TAC [EXTENSION]
 >> GEN_TAC >> EQ_TAC
 >| [ RW_TAC std_ss [IN_BIGINTER_IMAGE, IN_INTER, IN_COUNT],
      RW_TAC std_ss [IN_BIGINTER_IMAGE, IN_INTER, IN_COUNT] >> RES_TAC ]);

val BIGINTER_IMAGE_OVER_INTER_R = store_thm
  ("BIGINTER_IMAGE_OVER_INTER_R",
  ``!f n d. 0 < n ==>
           (d INTER BIGINTER (IMAGE f (count n)) =
            BIGINTER (IMAGE (\i. d INTER f i) (count n)))``,
    rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [INTER_COMM]
 >> MATCH_MP_TAC BIGINTER_IMAGE_OVER_INTER_L >> art []);

(* any finite set can be decomposed into a finite sequence of sets *)
val finite_decomposition_simple = store_thm (* new *)
  ("finite_decomposition_simple",
  ``!c. FINITE c ==> ?f n. (!x. x < n ==> f x IN c) /\ (c = IMAGE f (count n))``,
    GEN_TAC
 >> REWRITE_TAC [FINITE_BIJ_COUNT_EQ]
 >> rpt STRIP_TAC
 >> rename1 `BIJ f (count n) c`
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `n`
 >> CONJ_TAC >- (rpt STRIP_TAC >> PROVE_TAC [BIJ_DEF, INJ_DEF, IN_COUNT])
 >> PROVE_TAC [BIJ_IMAGE]);

(* any finite set can be decomposed into a finite (non-repeated) sequence of sets *)
val finite_decomposition = store_thm (* new *)
  ("finite_decomposition",
  ``!c. FINITE c ==>
        ?f n. (!x. x < n ==> f x IN c) /\ (c = IMAGE f (count n)) /\
              (!i j. i < n /\ j < n /\ i <> j ==> f i <> f j)``,
    GEN_TAC
 >> REWRITE_TAC [FINITE_BIJ_COUNT_EQ]
 >> rpt STRIP_TAC
 >> rename1 `BIJ f (count n) c`
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `n`
 >> CONJ_TAC >- (rpt STRIP_TAC >> PROVE_TAC [BIJ_DEF, INJ_DEF, IN_COUNT])
 >> CONJ_TAC >- PROVE_TAC [BIJ_IMAGE]
 >> rpt STRIP_TAC
 >> fs [BIJ_ALT, IN_FUNSET, IN_COUNT]
 >> METIS_TAC []);

(* any finite disjoint set can be decomposed into a finite pair-wise
   disjoint sequence of sets *)
val finite_disjoint_decomposition = store_thm (* new *)
  ("finite_disjoint_decomposition",
  ``!c. FINITE c /\ disjoint c ==>
        ?f n. (!i. i < n ==> f i IN c) /\ (c = IMAGE f (count n)) /\
              (!i j. i < n /\ j < n /\ i <> j ==> f i <> f j) /\
              (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j))``,
    GEN_TAC
 >> REWRITE_TAC [FINITE_BIJ_COUNT_EQ]
 >> rpt STRIP_TAC
 >> rename1 `BIJ f (count n) c`
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `n`
 >> STRONG_CONJ_TAC
 >- (rpt STRIP_TAC >> PROVE_TAC [BIJ_DEF, INJ_DEF, IN_COUNT])
 >> DISCH_TAC
 >> CONJ_TAC >- PROVE_TAC [BIJ_IMAGE]
 >> STRONG_CONJ_TAC
 >- (rpt STRIP_TAC \\
     fs [BIJ_ALT, IN_FUNSET, IN_COUNT] >> METIS_TAC [])
 >> rpt STRIP_TAC
 >> fs [disjoint_def]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> METIS_TAC []);

val countable_disjoint_decomposition = store_thm (* new *)
  ("countable_disjoint_decomposition",
  ``!c. FINITE c /\ disjoint c ==>
        ?f n. (!i. i < n ==> f i IN c) /\ (!i. n <= i ==> (f i = {})) /\
              (c = IMAGE f (count n)) /\
              (BIGUNION c = BIGUNION (IMAGE f univ(:num))) /\
              (!i j. i < n /\ j < n /\ i <> j ==> f i <> f j) /\
              (!i j. i < n /\ j < n /\ i <> j ==> DISJOINT (f i) (f j))``,
    rpt STRIP_TAC
 >> STRIP_ASSUME_TAC
        (MATCH_MP finite_disjoint_decomposition
                  (CONJ (ASSUME ``FINITE (c :'a set set)``)
                        (ASSUME ``disjoint (c :'a set set)``)))
 >> Q.EXISTS_TAC `\i. if i < n then f i else {}`
 >> Q.EXISTS_TAC `n`
 >> BETA_TAC
 >> CONJ_TAC >- METIS_TAC []
 >> CONJ_TAC >- METIS_TAC [NOT_LESS]
 >> CONJ_TAC
 >- (art [] >> MATCH_MP_TAC IMAGE_CONG >> RW_TAC std_ss [IN_COUNT])
 >> Reverse CONJ_TAC >- METIS_TAC []
 >> art [] >> KILL_TAC
 >> SIMP_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_COUNT, IN_UNIV]
 >> GEN_TAC >> EQ_TAC >> rpt STRIP_TAC
 >| [ Q.EXISTS_TAC `x'` >> METIS_TAC [],
      Cases_on `i < n` >- (Q.EXISTS_TAC `i` >> METIS_TAC []) \\
      fs [NOT_IN_EMPTY] ]);

(* any union of two sets can be decomposed into 3 disjoint unions *)
val UNION_TO_3_DISJOINT_UNIONS = store_thm (* new *)
  ("UNION_TO_3_DISJOINT_UNIONS",
  ``!s t. (s UNION t = (s DIFF t) UNION (s INTER t) UNION (t DIFF s)) /\
          disjoint {(s DIFF t); (s INTER t); (t DIFF s)}``,
    NTAC 2 GEN_TAC
 >> CONJ_TAC >- SET_TAC []
 >> REWRITE_TAC [disjoint_def, DISJOINT_DEF]
 >> RW_TAC std_ss [IN_INSERT]
 >> ASM_SET_TAC []);

val BIGUNION_IMAGE_BIGUNION_IMAGE_UNIV = store_thm
  ("BIGUNION_IMAGE_BIGUNION_IMAGE_UNIV",
  ``!f. BIGUNION (IMAGE (\n. BIGUNION (IMAGE (f n) univ(:num))) univ(:num)) =
        BIGUNION (IMAGE (UNCURRY f) univ(:num # num))``,
    GEN_TAC
 >> RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_CROSS, UNCURRY]
 >> EQ_TAC >> STRIP_TAC
 >- (Q.EXISTS_TAC `(n, x')` >> art [FST, SND])
 >> Q.EXISTS_TAC `FST x'`
 >> Q.EXISTS_TAC `SND x'` >> art []);

val BIGUNION_IMAGE_UNIV_CROSS_UNIV = store_thm
  ("BIGUNION_IMAGE_UNIV_CROSS_UNIV",
  ``!f (h :num -> num # num). BIJ h UNIV (UNIV CROSS UNIV) ==>
       (BIGUNION (IMAGE (UNCURRY f) univ(:num # num)) =
        BIGUNION (IMAGE (UNCURRY f o h) univ(:num)))``,
    rpt STRIP_TAC
 >> RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_CROSS, UNCURRY, o_DEF]
 >> fs [BIJ_ALT, IN_FUNSET, IN_UNIV]
 >> EQ_TAC >> STRIP_TAC
 >- (Q.PAT_X_ASSUM `!y. ?!x. y = h x` (MP_TAC o (Q.SPEC `x'`)) >> METIS_TAC [])
 >> Q.EXISTS_TAC `h x'` >> art []);


(* ------------------------------------------------------------------------- *)
(*  Three series of lemmas on bigunion-equivalent sequences of sets          *)
(* ------------------------------------------------------------------------- *)

(* 1. for any sequence of sets, there is an increasing sequence of the same bigunion. *)
val SETS_TO_INCREASING_SETS = store_thm
  ("SETS_TO_INCREASING_SETS",
  ``!f :num->'a set.
       ?g. (g 0 = f 0) /\ (!n. g n = BIGUNION (IMAGE f (count (SUC n)))) /\
           (!n. g n SUBSET g (SUC n)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. BIGUNION (IMAGE f (count (SUC n)))`
 >> BETA_TAC
 >> RW_TAC bool_ss []
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [COUNT_SUC, COUNT_ZERO, IMAGE_SING, BIGUNION_SING],
      (* goal 2 (of 3) *)
     `count (SUC (SUC n)) = (SUC n) INSERT (count (SUC n))`
          by PROVE_TAC [COUNT_SUC] >> POP_ORW \\
      REWRITE_TAC [IMAGE_INSERT, BIGUNION_INSERT] \\
      REWRITE_TAC [SUBSET_UNION],
      (* goal 3 (of 3) *)
      MATCH_MP_TAC BIGUNION_IMAGE_COUNT_IMP_UNIV \\
      Induct_on `n` >- REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
     `count (SUC n) = n INSERT (count n)` by PROVE_TAC [COUNT_SUC] \\
      POP_ORW >> REWRITE_TAC [IMAGE_INSERT, BIGUNION_INSERT] \\
      POP_ASSUM (REWRITE_TAC o wrap) \\
      BETA_TAC \\
      Cases_on `n = 0` >> fs [COUNT_SUC, COUNT_ZERO, IMAGE_SING, BIGUNION_SING] \\
      REWRITE_TAC [GSYM UNION_ASSOC, UNION_IDEMPOT] ]);

(* another version with `g 0 = {}` *)
val SETS_TO_INCREASING_SETS' = store_thm
  ("SETS_TO_INCREASING_SETS'",
  ``!f :num -> 'a set.
       ?g. (g 0 = {}) /\ (!n. g n = BIGUNION (IMAGE f (count n))) /\
           (!n. g n SUBSET g (SUC n)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. BIGUNION (IMAGE f (count n))`
 >> BETA_TAC
 >> RW_TAC bool_ss []
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY],
      (* goal 2 (of 3) *)
     `count (SUC n) = n INSERT (count n)` by PROVE_TAC [COUNT_SUC] \\
      POP_ORW >> REWRITE_TAC [IMAGE_INSERT, BIGUNION_INSERT] \\
      REWRITE_TAC [SUBSET_UNION],
      (* goal 3 (of 3) *)
      REWRITE_TAC [EXTENSION] \\
      GEN_TAC >> SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, IN_COUNT] \\
      EQ_TAC >> RW_TAC std_ss [] >|
      [ Q.EXISTS_TAC `SUC x'` \\
        Q.EXISTS_TAC `x'` >> ASM_SIMP_TAC arith_ss [],
        Q.EXISTS_TAC `x'` >> art [] ] ]);

(* 2. (hard) for any sequence of sets in a space, there is a disjoint family with
      the same bigunion. This lemma is needed by DYNKIN_LEMMA *)
val SETS_TO_DISJOINT_SETS = store_thm
  ("SETS_TO_DISJOINT_SETS",
  ``!sp sts f. (!s. s IN sts ==> s SUBSET sp) /\ (!n. f n IN sts) ==>
       ?g. (g 0 = f 0) /\
           (!n. 0 < n ==> (g n = f n INTER (BIGINTER (IMAGE (\i. sp DIFF f i) (count n))))) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. if n = 0:num then f n
                      else f n INTER (BIGINTER (IMAGE (\i. sp DIFF f i) (count n)))`
 >> BETA_TAC >> SIMP_TAC arith_ss []
 >> CONJ_TAC >> RW_TAC arith_ss []
 >| [ (* goal 1 (of 4)
        `DISJOINT (f 0) (f j INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count j)))` *)
      `0 IN (count j)` by PROVE_TAC [NOT_ZERO_LT_ZERO, IN_COUNT] \\
      POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
      REWRITE_TAC [INTER_ASSOC] \\
      `f j INTER (sp DIFF f 0) = (sp DIFF f 0) INTER f j` by PROVE_TAC [INTER_COMM] \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF],
      (* goal 2 (of 4),
        `DISJOINT (f i INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count i))) (f 0)` *)
     `0 IN (count i)` by PROVE_TAC [NOT_ZERO_LT_ZERO, IN_COUNT] \\
      POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
      DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
      REWRITE_TAC [INTER_ASSOC] \\
     `f i INTER (sp DIFF f 0) = (sp DIFF f 0) INTER f i` by PROVE_TAC [INTER_COMM] \\
      POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
      REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF],
      (* goal 3 (of 4),
        `DISJOINT (f i INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count i)))
                  (f j INTER BIGINTER (IMAGE (\i. sp DIFF f i) (count j)))` *)
      STRIP_ASSUME_TAC (Q.SPECL [`i`, `j`] LESS_LESS_CASES) >| (* 2 subgoals *)
      [ (* goal 3.1 (of 2) *)
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f i` >> REWRITE_TAC [INTER_SUBSET] \\
       `i IN (count j)` by PROVE_TAC [IN_COUNT] \\
        POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
        DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
        REWRITE_TAC [INTER_ASSOC] \\
       `f j INTER (sp DIFF f i) = (sp DIFF f i) INTER f j` by PROVE_TAC [INTER_COMM] \\
        POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF],
        (* goal 3.2 (of 2) *)
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f j` >> REWRITE_TAC [INTER_SUBSET] \\
       `j IN (count i)` by PROVE_TAC [IN_COUNT] \\
        POP_ASSUM (MP_TAC o SYM o (MATCH_MP INSERT_DELETE)) \\
        DISCH_THEN (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [IMAGE_INSERT, BIGINTER_INSERT] >> BETA_TAC \\
        REWRITE_TAC [INTER_ASSOC] \\
       `f i INTER (sp DIFF f j) = (sp DIFF f j) INTER f i` by PROVE_TAC [INTER_COMM] \\
        POP_ASSUM (ONCE_REWRITE_TAC o wrap) \\
        REWRITE_TAC [DIFF_INTER, DISJOINT_DIFF] ],
      (* goal 4 (of 4) *)
      MATCH_MP_TAC BIGUNION_IMAGE_COUNT_IMP_UNIV \\
      Induct_on `n` >- REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
      REWRITE_TAC [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
      POP_ASSUM (REWRITE_TAC o wrap) >> BETA_TAC \\
      Cases_on `n = 0` >> fs [] (* now ``n <> 0`` *) \\
      REWRITE_TAC [Once UNION_COMM, INTER_OVER_UNION] \\
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [UNION_COMM] \\
      Suff `BIGUNION (IMAGE f (count n)) UNION (BIGINTER (IMAGE (\i. sp DIFF f i) (count n))) = sp`
      >- (DISCH_THEN (REWRITE_TAC o wrap) \\
          REWRITE_TAC [INTER_SUBSET_EQN, UNION_SUBSET] \\
          Reverse CONJ_TAC >- PROVE_TAC [] \\
          REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] >> PROVE_TAC []) \\
      (* BIGUNION (IMAGE f (count n)) UNION BIGINTER (IMAGE (\i. sp DIFF f i) (count n)) = sp *)
     `0 < n` by PROVE_TAC [NOT_ZERO_LT_ZERO] \\
      POP_ASSUM (REWRITE_TAC o wrap o GSYM o (MATCH_MP GEN_COMPL_FINITE_UNION)) \\
      Suff `BIGUNION (IMAGE f (count n)) SUBSET sp` >- ASM_SET_TAC [] \\
      REWRITE_TAC [BIGUNION_SUBSET, IN_IMAGE] >> PROVE_TAC [] ]);

(* A specific version without sts and sp *)
val SETS_TO_DISJOINT_SETS' = store_thm
  ("SETS_TO_DISJOINT_SETS'",
  ``!f. ?g. (g 0 = f 0) /\
            (!n. 0 < n ==> (g n = f n INTER (BIGINTER (IMAGE (COMPL o f) (count n))))) /\
            (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
            (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    GEN_TAC
 >> STRIP_ASSUME_TAC (Q.SPECL [`UNIV`, `UNIV`, `f`] SETS_TO_DISJOINT_SETS)
 >> fs [SUBSET_UNIV, o_DEF, COMPL_DEF]
 >> Q.EXISTS_TAC `g` >> art []);

(* 3. (hard) for any sequence of (straightly) increasing sets, there is a disjoint
      family with the same bigunion. *)
val INCREASING_TO_DISJOINT_SETS = store_thm
  ("INCREASING_TO_DISJOINT_SETS",
  ``!f :num -> 'a set. (!n. f n SUBSET f (SUC n)) ==>
       ?g. (g 0 = f 0) /\ (!n. 0 < n ==> (g n = f n DIFF f (PRE n))) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. if n = (0 :num) then f n else f n DIFF f (PRE n)`
 >> BETA_TAC
 (* preliminaries *)
 >> Know `!n. 0 < n ==> f 0 SUBSET (f n)`
 >- (Induct_on `n` >- RW_TAC arith_ss [] \\
     RW_TAC arith_ss [] \\
     Cases_on `n = 0` >- art [] \\
     IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f n` >> art [])
 >> DISCH_TAC
 >> Know `!n. 0 < n ==> f 0 SUBSET (f (PRE n))`
 >- (Induct_on `n` >- RW_TAC arith_ss [] \\
     RW_TAC arith_ss [] \\
     Cases_on `n = 0` >- art [SUBSET_REFL] \\
     IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC)
 >> DISCH_TAC
 >> Know `!i j. i < j ==> f (SUC i) SUBSET (f j)`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f j` \\
     CONJ_TAC >- RES_TAC >> art [])
 >> DISCH_TAC
 >> Know `!n. 0 < n ==> f (PRE n) SUBSET f n`
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM `!n. f n SUBSET f (SUC n)` (STRIP_ASSUME_TAC o (Q.SPEC `PRE n`)) \\
     PROVE_TAC [SUC_PRE])
 >> DISCH_TAC
 >> Know `!i j. i < j ==> f i SUBSET f (PRE j)`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f (PRE j)` \\
     CONJ_TAC >- RES_TAC \\
     Cases_on `j = 0` >- (RW_TAC arith_ss [SUBSET_REFL]) \\
     IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC)
 >> DISCH_TAC
 >> RW_TAC arith_ss []
 >| [ (* goal 1 (of 4): DISJOINT (f 0) (f (SUC j) DIFF f j) *)
      MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
      Q.EXISTS_TAC `f j` \\
      IMP_RES_TAC NOT_ZERO_LT_ZERO \\
     `f j DIFF (f j DIFF f (PRE j)) = f (PRE j)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC,
      (* goal 2 (of 4): DISJOINT (f (SUC i) DIFF f i) (f 0) *)
      ONCE_REWRITE_TAC [DISJOINT_SYM] \\
      MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
      Q.EXISTS_TAC `f i` \\
      IMP_RES_TAC NOT_ZERO_LT_ZERO \\
     `f i DIFF (f i DIFF f (PRE i)) = f (PRE i)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW \\
      IMP_RES_TAC NOT_ZERO_LT_ZERO >> RES_TAC,
      (* goal 3 (of 4): DISJOINT (f (SUC i) DIFF f i) (f (SUC j) DIFF f j) *)
      STRIP_ASSUME_TAC (Q.SPECL [`i`, `j`] LESS_LESS_CASES) >| (* 2 subgoals *)
      [ (* goal 3.1 (of 2) *)
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f i` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f j` \\
        IMP_RES_TAC NOT_ZERO_LT_ZERO \\
       `f j DIFF (f j DIFF f (PRE j)) = f (PRE j)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC,
        (* goal 3.2 (of 2) *)
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f j` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f i` \\
        IMP_RES_TAC NOT_ZERO_LT_ZERO \\
       `f i DIFF (f i DIFF f (PRE i)) = f (PRE i)`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC ],
      (* goal 4 (of 4): BIGUNION (IMAGE f univ(:num)) = ... *)
      MATCH_MP_TAC BIGUNION_IMAGE_COUNT_IMP_UNIV \\
      Induct_on `n` >- REWRITE_TAC [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY] \\
      REWRITE_TAC [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
      POP_ASSUM (REWRITE_TAC o wrap) >> BETA_TAC \\
      Cases_on `n = 0` >> fs [] (* now ``n <> 0`` *) \\
      RW_TAC arith_ss [EXTENSION, IN_UNION, IN_BIGUNION_IMAGE, IN_COUNT, IN_DIFF] \\
      EQ_TAC >> rpt STRIP_TAC >| (* 4 subgoals *)
      [ DISJ1_TAC >> art [],
        DISJ2_TAC >> Q.EXISTS_TAC `x'` >> art [],
        Cases_on `x IN f (PRE n)` >- (DISJ2_TAC >> Q.EXISTS_TAC `PRE n` \\
                                      ASM_SIMP_TAC arith_ss []) \\
        DISJ1_TAC >> art [],
        DISJ2_TAC >> Q.EXISTS_TAC `x'` >> art [] ] ]);

(* Surprisingly, this variant of INCREASING_TO_DISJOINT_SETS cannot be
   easily proved without using the non-trivial SETS_TO_DISJOINT_SETS *)
val INCREASING_TO_DISJOINT_SETS' = store_thm
  ("INCREASING_TO_DISJOINT_SETS'",
  ``!f :num -> 'a set. (f 0 = {}) /\ (!n. f n SUBSET f (SUC n)) ==>
       ?g. (!n. g n = f (SUC n) DIFF f n) /\
           (!i j :num. i <> j ==> DISJOINT (g i) (g j)) /\
           (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE g UNIV))``,
    rpt STRIP_TAC
 >> Q.EXISTS_TAC `\n. f (SUC n) DIFF f n`
 >> BETA_TAC
 (* preliminaries *)
 >> Know `!i j. i < j ==> f i SUBSET f j`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f j` >> art [] \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ])
 >> DISCH_TAC
 >> Know `!i j. i < j ==> f (SUC i) SUBSET f j`
 >- (GEN_TAC >> Induct_on `j` >- RW_TAC arith_ss [] \\
     STRIP_TAC \\
     Cases_on `i = j` >- PROVE_TAC [SUBSET_REFL] \\
     MATCH_MP_TAC SUBSET_TRANS >> Q.EXISTS_TAC `f j` >> art [] \\
     fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ])
 >> DISCH_TAC
 >> RW_TAC arith_ss [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2): DISJOINT (f (SUC i) DIFF f i) (f (SUC j) DIFF f j) *)
      STRIP_ASSUME_TAC (Q.SPECL [`i`, `j`] LESS_LESS_CASES) >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f (SUC i)` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f (SUC j)` \\
        `f (SUC j) DIFF (f (SUC j) DIFF f j) = f j`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC,
        (* goal 1.2 (of 2) *)
        MATCH_MP_TAC DISJOINT_SUBSET \\
        Q.EXISTS_TAC `f (SUC j)` >> REWRITE_TAC [DIFF_SUBSET] \\
        ONCE_REWRITE_TAC [DISJOINT_SYM] \\
        MATCH_MP_TAC SUBSET_DIFF_DISJOINT \\
        Q.EXISTS_TAC `f (SUC i)` \\
       `f (SUC i) DIFF (f (SUC i) DIFF f i) = f i`
          by PROVE_TAC [DIFF_DIFF_SUBSET] >> POP_ORW >> RES_TAC ],
      (* goal 2 (of 2): BIGUNION (IMAGE f univ(:num)) = ... *)
      STRIP_ASSUME_TAC (Q.SPEC `f` SETS_TO_DISJOINT_SETS') >> art [] \\
      RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_DIFF] \\
      EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        Cases_on `x' = 0` >- PROVE_TAC [NOT_IN_EMPTY] \\
        IMP_RES_TAC NOT_ZERO_LT_ZERO \\
        Q.EXISTS_TAC `PRE x'` \\
       `SUC (PRE x') = x'` by PROVE_TAC [SUC_PRE] >> POP_ORW \\
        Q.PAT_X_ASSUM `x IN g x'` MP_TAC \\
        Q.PAT_X_ASSUM `!n. 0 < n ==> X`
            (fn th => REWRITE_TAC [MATCH_MP th (ASSUME ``0:num < x'``)]) \\
        RW_TAC std_ss [IN_INTER, IN_BIGINTER_IMAGE, IN_COUNT, o_DEF, IN_COMPL] \\
        FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC arith_ss [],
        (* goal 2.2 (of 2) *)
        Q.EXISTS_TAC `SUC n` \\
       `0 < SUC n` by REWRITE_TAC [prim_recTheory.LESS_0] \\
        Q.PAT_X_ASSUM `!n. 0 < n ==> X`
            (fn th => REWRITE_TAC [MATCH_MP th (ASSUME ``0:num < SUC n``)]) \\
        RW_TAC std_ss [IN_INTER, IN_BIGINTER_IMAGE, IN_COUNT, o_DEF, IN_COMPL] \\
        fs [GSYM LESS_EQ_IFF_LESS_SUC, LESS_OR_EQ] \\
        CCONTR_TAC >> fs [] \\
       `x IN f n` by PROVE_TAC [SUBSET_DEF] ] ]);


(******************************************************************************)
(*  liminf and limsup [1, p.74] [2, p.76] - the set-theoretic version         *)
(******************************************************************************)

(* this lemma is provided by Konrad Slind *)
val set_ss = arith_ss ++ PRED_SET_ss;

val lemma = Q.prove
  (`!P. ~(?N. INFINITE N /\ !n. N n ==> P n) <=> !N. N SUBSET P ==> FINITE N`,
  rw_tac set_ss [EQ_IMP_THM, SUBSET_DEF, IN_DEF]
  >- (`FINITE P \/ ?n. P n /\ ~P n` by metis_tac []
       >> imp_res_tac SUBSET_FINITE
       >> full_simp_tac std_ss [SUBSET_DEF, IN_DEF])
  >- metis_tac[]);

(* TODO: use above lemma to simplify this proof with the following hints:

   "From this and the original assumption, you should be able to get that P is finite,
    so has a maximum element." -- Konrad Slind, Feb 17, 2019.
 *)
val infinitely_often_lemma = store_thm
  ("infinitely_often_lemma",
  ``!P. ~(?N. INFINITE N /\ !n:num. n IN N ==> P n) <=> ?m. !n. m <= n ==> ~(P n)``,
    GEN_TAC
 >> `!N. (!n. n IN N ==> P n) <=> N SUBSET P` by PROVE_TAC [SUBSET_DEF, IN_APP]
 >> ASM_REWRITE_TAC []
 >> SIMP_TAC std_ss []
 >> Reverse EQ_TAC >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Cases_on `~(N SUBSET P)` >- art [] >> fs [] \\
      Suff `FINITE P` >- PROVE_TAC [SUBSET_FINITE_I] \\
      Know `P SUBSET {n | ~(m <= n)}`
      >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_APP] \\
          METIS_TAC []) \\
      DISCH_TAC \\
      Suff `FINITE {n | ~(m <= n)}` >- PROVE_TAC [SUBSET_FINITE_I] \\
      REWRITE_TAC [FINITE_WEAK_ENUMERATE] \\
      Q.EXISTS_TAC `I` \\
      Q.EXISTS_TAC `m` \\
      RW_TAC arith_ss [I_THM, GSPECIFICATION],
      (* goal 2 (of 2) *)
      POP_ASSUM (MP_TAC o (Q.SPEC `P`)) \\
      RW_TAC std_ss [SUBSET_REFL] \\
      IMP_RES_TAC finite_decomposition_simple \\
      Q.EXISTS_TAC `SUC (MAX_SET P)` \\
      Q.X_GEN_TAC `m` >> DISCH_TAC \\
      CCONTR_TAC >> fs [EXTENSION, IN_IMAGE, IN_COUNT, IN_APP] \\
     `P <> {}` by METIS_TAC [IN_APP, NOT_IN_EMPTY] \\
     `!y. y IN P ==> y <= MAX_SET P` by PROVE_TAC [MAX_SET_DEF] \\
     `m <= MAX_SET P` by PROVE_TAC [IN_APP] \\
     `MAX_SET P < m` by RW_TAC arith_ss [] \\
      FULL_SIMP_TAC arith_ss [] ]);

(* this proof is provided by Konrad Slind, slightly shorter than mine. *)
val infinity_bound_lemma = store_thm
  ("infinity_bound_lemma",
  ``!N m. INFINITE N ==> ?n:num. m <= n /\ n IN N``,
    spose_not_then strip_assume_tac
 >> `FINITE (count m)` by metis_tac [FINITE_COUNT]
 >> `N SUBSET (count m)`
      by (rw_tac set_ss [SUBSET_DEF]
           >> `~(m <= x)` by metis_tac []
           >> decide_tac)
 >> metis_tac [SUBSET_FINITE]);

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

(* TODO: restate this lemma by "from" *)
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

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales. Cambridge University Press (2005).
  [2] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
 *)
