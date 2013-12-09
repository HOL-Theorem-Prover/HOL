(* ------------------------------------------------------------------------- *)
(* Useful Theorems, some are taken from various theories by Hurd, Coble, ... *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar                         *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib metisLib combinTheory pred_setTheory seqTheory
     res_quanTheory res_quanTools pairTheory arithmeticTheory realTheory realLib transcTheory
     real_sigmaTheory;

val _ = new_theory "util_prob";

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;
val Strip = S_TAC;

fun K_TAC _ = ALL_TAC;
val KILL_TAC = POP_ASSUM_LIST K_TAC;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);


val Cond =
  MATCH_MP_TAC (PROVE [] ``!a b c. a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
  ++ CONJ_TAC;

local
  val th = prove (``!a b. a /\ (a ==> b) ==> a /\ b``, PROVE_TAC [])
in
  val STRONG_CONJ_TAC :tactic = MATCH_MP_TAC th ++ CONJ_TAC
end;

fun wrap a = [a];
val Rewr = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);


(* ------------------------------------------------------------------------- *)
(* Auxiliary theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

val EQ_T_IMP = store_thm
  ("EQ_T_IMP",
   ``!x. x = T ==> x``,
   PROVE_TAC []);

val EQ_SUBSET_SUBSET = store_thm
  ("EQ_SUBSET_SUBSET",
   ``!(s : 'a -> bool) t. (s = t) ==> s SUBSET t /\ t SUBSET s``,
   RW_TAC std_ss [SUBSET_DEF, EXTENSION]);

val IN_EQ_UNIV_IMP = store_thm
  ("IN_EQ_UNIV_IMP",
   ``!s. (s = UNIV) ==> !v. (v : 'a) IN s``,
   RW_TAC std_ss [IN_UNIV]);

(* ------------------------------------------------------------------------- *)
(* bool theory subtypes.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Subtype definitions *)

val FUNSET_def = Define
  `FUNSET (P:'a->bool) (Q:'b->bool) = \f. !x. x IN P ==> f x IN Q`;

val DFUNSET_def = Define
  `DFUNSET (P:'a->bool) (Q:'a->'b->bool) = \f. !x. x IN P ==> f x IN Q x`;

val _ = add_infix("->", 250, HOLgrammars.RIGHT);

val _ = overload_on
  ("->", ``FUNSET:('a->bool) -> ('b->bool) -> (('a->'b)->bool)``);
val _ = overload_on
  ("-->", ``DFUNSET : ('a->bool) -> ('a->'b->bool) -> (('a->'b)->bool)``);

val pair_def = Define
  `pair (X : 'a -> bool) (Y : 'b -> bool) = \ (x, y). x IN X /\ y IN Y`;

val IN_FUNSET = store_thm
  ("IN_FUNSET",
   ``!(f:'a->'b) P Q. f IN (P -> Q) = !x. x IN P ==> f x IN Q``,
   RW_TAC std_ss [SPECIFICATION, FUNSET_def]);

val IN_DFUNSET = store_thm
  ("IN_DFUNSET",
   ``!(f:'a->'b) (P:'a->bool) Q. f IN (P --> Q) = !x. x IN P ==> f x IN Q x``,
   RW_TAC std_ss [SPECIFICATION, DFUNSET_def]);

val IN_PAIR = store_thm
  ("IN_PAIR",
   ``!(x : 'a # 'b) X Y. x IN pair X Y = FST x IN X /\ SND x IN Y``,
   Cases
   ++ RW_TAC std_ss [pair_def, SPECIFICATION]);

val FUNSET_THM = store_thm
  ("FUNSET_THM",
   ``!s t (f:'a->'b) x. f IN (s -> t) /\ x IN s ==> f x IN t``,
    RW_TAC std_ss [IN_FUNSET] ++ PROVE_TAC []);

val UNIV_FUNSET_UNIV = store_thm
  ("UNIV_FUNSET_UNIV",
   ``((UNIV : 'a -> bool) -> (UNIV : 'b -> bool)) = UNIV``,
   RW_TAC std_ss [EXTENSION,IN_UNIV,IN_FUNSET]);

val FUNSET_DFUNSET = store_thm
  ("FUNSET_DFUNSET",
   ``!(x : 'a -> bool) (y : 'b -> bool). (x -> y) = (x --> K y)``,
   RW_TAC std_ss [EXTENSION,GSPECIFICATION, IN_FUNSET, IN_DFUNSET, K_DEF]);

val PAIR_UNIV = store_thm
  ("PAIR_UNIV",
   ``pair UNIV UNIV = (UNIV : 'a # 'b -> bool)``,
   RW_TAC std_ss [EXTENSION,GSPECIFICATION, IN_PAIR, IN_UNIV]);

val SUBSET_INTER = store_thm
  ("SUBSET_INTER",
   ``!(s : 'a -> bool) t u.
   s SUBSET (t INTER u) = s SUBSET t /\ s SUBSET u``,
   RW_TAC std_ss [SUBSET_DEF, IN_INTER]
   ++ PROVE_TAC []);

val K_SUBSET = store_thm
  ("K_SUBSET",
   ``!x y. K x SUBSET y = ~x \/ (UNIV SUBSET y)``,
   RW_TAC std_ss [K_DEF, SUBSET_DEF, IN_UNIV]
   ++ RW_TAC std_ss [SPECIFICATION]
   ++ PROVE_TAC []);

val SUBSET_K = store_thm
  ("SUBSET_K",
   ``!x y. x SUBSET K y = (x SUBSET EMPTY) \/ y``,
   RW_TAC std_ss [K_DEF, SUBSET_DEF, NOT_IN_EMPTY]
   ++ RW_TAC std_ss [SPECIFICATION]
   ++ PROVE_TAC []);

val SUBSET_THM = store_thm
  ("SUBSET_THM",
   ``!(P : 'a -> bool) Q. P SUBSET Q ==> (!x. x IN P ==> x IN Q)``,
    RW_TAC std_ss [SUBSET_DEF]);

val PAIRED_BETA_THM = store_thm
  ("PAIRED_BETA_THM",
   ``!f z. UNCURRY f z = f (FST z) (SND z)``,
   STRIP_TAC
   ++ Cases
   ++ RW_TAC std_ss []);

val EMPTY_FUNSET = store_thm
  ("EMPTY_FUNSET",
   ``!s. ({} -> s) = (UNIV : ('a -> 'b) -> bool)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_FUNSET, NOT_IN_EMPTY, IN_UNIV]);

val FUNSET_EMPTY = store_thm
  ("FUNSET_EMPTY",
   ``!s (f : 'a -> 'b). f IN (s -> {}) = (s = {})``,
   RW_TAC std_ss [IN_FUNSET, NOT_IN_EMPTY, EXTENSION,GSPECIFICATION]);

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
   ++ Know `m <= n \/ n <= m` >> DECIDE_TAC
   ++ RW_TAC std_ss [LESS_EQ_EXISTS]
   ++ PROVE_TAC []);

val TRIANGLE_2D_NUM = store_thm
  ("TRIANGLE_2D_NUM",
   ``!P. (!d n. P n (d + n)) ==> (!m n : num. m <= n ==> P m n)``,
   RW_TAC std_ss [LESS_EQ_EXISTS]
   ++ PROVE_TAC [ADD_COMM]);

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
   ++ RW_TAC std_ss [GSYM lg_1]
   ++ RW_TAC std_ss [lg_def, logr_def, real_div, REAL_EQ_RMUL, REAL_INV_EQ_0]
   ++ (MP_TAC o Q.SPECL [`2`, `1`]) LN_INJ ++ RW_TAC real_ss [LN_1]
   ++ RW_TAC std_ss [GSYM LN_1]
   ++ MATCH_MP_TAC LN_INJ
   ++ RW_TAC real_ss []);

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
   ++ MATCH_MP_TAC REAL_DIV_REFL
   ++ (ASSUME_TAC o Q.SPECL [`1`, `2`]) LN_MONO_LT
   ++ FULL_SIMP_TAC real_ss [LN_1]
   ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
   ++ MATCH_MP_TAC REAL_LT_IMP_NE
   ++ ASM_REWRITE_TAC []);

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
   ++ `~(ln x * inv (ln 2)) = (~ ln x) * inv (ln 2)` by REAL_ARITH_TAC
   ++ POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   ++ RW_TAC real_ss [REAL_EQ_RMUL]
   ++ DISJ2_TAC ++ ONCE_REWRITE_TAC [EQ_SYM_EQ] ++ MATCH_MP_TAC LN_INV
   ++ RW_TAC std_ss []);

val neg_logr = store_thm
  ("neg_logr",
  ``!b x. 0 < x ==> ((~(logr b x)) = logr b (inv x))``,
   RW_TAC real_ss [logr_def, real_div]
   ++ `~(ln x * inv (ln b)) = (~ ln x) * inv (ln b)` by REAL_ARITH_TAC
   ++ POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm])
   ++ RW_TAC real_ss [REAL_EQ_RMUL]
   ++ DISJ2_TAC ++ ONCE_REWRITE_TAC [EQ_SYM_EQ] ++ MATCH_MP_TAC LN_INV
   ++ RW_TAC std_ss []);

val lg_pow = store_thm
  ("lg_pow", ``!n. lg (2 pow n) = &n``,
   RW_TAC real_ss [lg_def, logr_def, LN_POW]
   ++ `~(ln 2 = 0)`
	by (ONCE_REWRITE_TAC [EQ_SYM_EQ] ++ MATCH_MP_TAC REAL_LT_IMP_NE
	    ++ MATCH_MP_TAC REAL_LET_TRANS ++ Q.EXISTS_TAC `ln 1`
	    ++ RW_TAC real_ss [LN_POS, LN_MONO_LT])
   ++ RW_TAC real_ss [real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_RINV]);



(********************************************************************************************)
(********************************************************************************************)

val countable_def = Define
  `countable s = ?f. !x : 'a. x IN s ==> ?n : num. f n = x`;

val enumerate_def = Define `enumerate s = @f : num -> 'a. BIJ f UNIV s`;

val schroeder_close_def = Define
  `schroeder_close f s x = ?n. x IN FUNPOW (IMAGE f) n s`;

val SCHROEDER_CLOSE = store_thm
  ("SCHROEDER_CLOSE",
   ``!f s. x IN schroeder_close f s = ?n. x IN FUNPOW (IMAGE f) n s``,
   RW_TAC std_ss [SPECIFICATION, schroeder_close_def]);

val SCHROEDER_CLOSED = store_thm
  ("SCHROEDER_CLOSED",
   ``!f s. IMAGE f (schroeder_close f s) SUBSET schroeder_close f s``,
   RW_TAC std_ss [SCHROEDER_CLOSE, IN_IMAGE, SUBSET_DEF]
   ++ Q.EXISTS_TAC `SUC n`
   ++ RW_TAC std_ss [FUNPOW_SUC, IN_IMAGE]
   ++ PROVE_TAC []);

val SCHROEDER_CLOSE_SUBSET = store_thm
  ("SCHROEDER_CLOSE_SUBSET",
   ``!f s. s SUBSET schroeder_close f s``,
   RW_TAC std_ss [SCHROEDER_CLOSE, IN_IMAGE, SUBSET_DEF]
   ++ Q.EXISTS_TAC `0`
   ++ RW_TAC std_ss [FUNPOW]);

val SCHROEDER_CLOSE_SET = store_thm
  ("SCHROEDER_CLOSE_SET",
   ``!f s t. f IN (s -> s) /\ t SUBSET s ==> schroeder_close f t SUBSET s``,
   RW_TAC std_ss [SCHROEDER_CLOSE, SUBSET_DEF, IN_FUNSET]
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`x`, `x`)
   ++ Induct_on `n` >> RW_TAC std_ss [FUNPOW]
   ++ RW_TAC std_ss [FUNPOW_SUC, IN_IMAGE]
   ++ PROVE_TAC []);

val SCHROEDER_BERNSTEIN_AUTO = store_thm
  ("SCHROEDER_BERNSTEIN_AUTO",
   ``!s t. t SUBSET s /\ (?f. INJ f s t) ==> ?g. BIJ g s t``,
   RW_TAC std_ss [INJ_DEF]
   ++ Q.EXISTS_TAC `\x. if x IN schroeder_close f (s DIFF t) then f x else x`
   ++ Know `s DIFF schroeder_close f (s DIFF t) SUBSET t`
   >> (RW_TAC std_ss [SUBSET_DEF, IN_DIFF]
       ++ Suff `~(x IN s DIFF t)` >> RW_TAC std_ss [IN_DIFF]
       ++ PROVE_TAC [SCHROEDER_CLOSE_SUBSET, SUBSET_DEF])
   ++ Know `schroeder_close f (s DIFF t) SUBSET s`
   >> (MATCH_MP_TAC SCHROEDER_CLOSE_SET
       ++ RW_TAC std_ss [SUBSET_DEF, IN_DIFF, IN_FUNSET]
       ++ PROVE_TAC [SUBSET_DEF])
   ++ Q.PAT_ASSUM `t SUBSET s` MP_TAC
   ++ RW_TAC std_ss [SUBSET_DEF, IN_DIFF]
   ++ RW_TAC std_ss [BIJ_DEF]
   >> (BasicProvers.NORM_TAC std_ss [INJ_DEF] <<
       [PROVE_TAC [SCHROEDER_CLOSED, SUBSET_DEF, IN_IMAGE],
        PROVE_TAC [SCHROEDER_CLOSED, SUBSET_DEF, IN_IMAGE]])
   ++ RW_TAC std_ss [SURJ_DEF]
   ++ REVERSE (Cases_on `x IN schroeder_close f (s DIFF t)`) >> PROVE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [SCHROEDER_CLOSE]
   ++ Cases_on `n` >> (POP_ASSUM MP_TAC ++ RW_TAC std_ss [FUNPOW, IN_DIFF])
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [FUNPOW_SUC, IN_IMAGE]
   ++ Q.EXISTS_TAC `x'`
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`n'`, `n`)
   ++ CONV_TAC FORALL_IMP_CONV
   ++ REWRITE_TAC [GSYM SCHROEDER_CLOSE]
   ++ RW_TAC std_ss []);

val INJ_IMAGE_BIJ = store_thm
  ("INJ_IMAGE_BIJ",
   ``!s f. (?t. INJ f s t) ==> BIJ f s (IMAGE f s)``,
   RW_TAC std_ss [INJ_DEF, BIJ_DEF, SURJ_DEF, IN_IMAGE]
   ++ PROVE_TAC []);

val BIJ_SYM_IMP = store_thm
  ("BIJ_SYM_IMP",
   ``!s t. (?f. BIJ f s t) ==> (?g. BIJ g t s)``,
   RW_TAC std_ss [BIJ_DEF, SURJ_DEF, INJ_DEF]
   ++ Suff `?(g : 'b -> 'a). !x. x IN t ==> g x IN s /\ (f (g x) = x)`
   >> (Strip
       ++ Q.EXISTS_TAC `g`
       ++ RW_TAC std_ss []
       ++ PROVE_TAC [])
   ++ POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [boolTheory.EXISTS_DEF])
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `\x. @y. y IN s /\ (f y = x)`
   ++ RW_TAC std_ss []);

val BIJ_SYM = store_thm
  ("BIJ_SYM",
   ``!s t. (?f. BIJ f s t) = (?g. BIJ g t s)``,
   PROVE_TAC [BIJ_SYM_IMP]);

val BIJ_TRANS = store_thm
  ("BIJ_TRANS",
   ``!s t u.
       (?f. BIJ f s t) /\ (?g. BIJ g t u) ==> (?h : 'a -> 'b. BIJ h s u)``,
   RW_TAC std_ss []
   ++ Q.EXISTS_TAC `g o f`
   ++ PROVE_TAC [BIJ_COMPOSE]);

val SCHROEDER_BERNSTEIN = store_thm
  ("SCHROEDER_BERNSTEIN",
   ``!s t. (?f. INJ f s t) /\ (?g. INJ g t s) ==> (?h. BIJ h s t)``,
   Strip
   ++ MATCH_MP_TAC (INST_TYPE [``:'c`` |-> ``:'a``] BIJ_TRANS)
   ++ Q.EXISTS_TAC `IMAGE g t`
   ++ CONJ_TAC <<
   [MATCH_MP_TAC SCHROEDER_BERNSTEIN_AUTO
    ++ CONJ_TAC
    >> (POP_ASSUM MP_TAC
        ++ RW_TAC std_ss [INJ_DEF, SUBSET_DEF, IN_IMAGE]
        ++ PROVE_TAC [])
    ++ Q.EXISTS_TAC `g o f`
    ++ !! (POP_ASSUM MP_TAC)
    ++ RW_TAC std_ss [INJ_DEF, SUBSET_DEF, IN_IMAGE, o_DEF]
    ++ PROVE_TAC [],
    MATCH_MP_TAC BIJ_SYM_IMP
    ++ Q.EXISTS_TAC `g`
    ++ PROVE_TAC [INJ_IMAGE_BIJ]]);

val SURJ_IMP_INJ = store_thm
  ("SURJ_IMP_INJ",
   ``!s t. (?f. SURJ f s t) ==> (?g. INJ g t s)``,
   RW_TAC std_ss [SURJ_DEF, INJ_DEF]
   ++ Suff `?g. !x. x IN t ==> g x IN s /\ (f (g x) = x)`
   >> PROVE_TAC []
   ++ Q.EXISTS_TAC `\y. @x. x IN s /\ (f x = y)`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [boolTheory.EXISTS_DEF]);

val BIJ_INJ_SURJ = store_thm
  ("BIJ_INJ_SURJ",
   ``!s t. (?f. INJ f s t) /\ (?g. SURJ g s t) ==> (?h. BIJ h s t)``,
   Strip
   ++ MATCH_MP_TAC SCHROEDER_BERNSTEIN
   ++ CONJ_TAC >> PROVE_TAC []
   ++ PROVE_TAC [SURJ_IMP_INJ]);

val BIJ_INV = store_thm
  ("BIJ_INV", ``!f s t. BIJ f s t ==>
       ?g.
         BIJ g t s /\
         (!x. x IN s ==> ((g o f) x = x)) /\
         (!x. x IN t ==> ((f o g) x = x))``,
   RW_TAC std_ss []
   ++ FULL_SIMP_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, o_THM]
   ++ POP_ASSUM
      (MP_TAC o
       CONV_RULE
       (DEPTH_CONV RIGHT_IMP_EXISTS_CONV
        THENC SKOLEM_CONV
        THENC REWRITE_CONV [EXISTS_DEF]
        THENC DEPTH_CONV BETA_CONV))
   ++ Q.SPEC_TAC (`@y. !x. x IN t ==> y x IN s /\ (f (y x) = x)`, `g`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `g`
   ++ RW_TAC std_ss []
   ++ PROVE_TAC []);

val NUM_2D_BIJ = store_thm
  ("NUM_2D_BIJ",
   ``?f.
       BIJ f ((UNIV : num -> bool) CROSS (UNIV : num -> bool))
       (UNIV : num -> bool)``,
   MATCH_MP_TAC BIJ_INJ_SURJ
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `FST`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       ++ Q.EXISTS_TAC `(x, 0)`
       ++ RW_TAC std_ss [FST])
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

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
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `FST`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS,DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]
       ++ Q.EXISTS_TAC `(x, 1)`
       ++ RW_TAC std_ss [FST])
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

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
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `(\(x,y). x + 1:num)`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       		>> (Cases_on `x` ++ RW_TAC std_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING])
       ++ Q.EXISTS_TAC `(x-1,1)`
       ++ RW_TAC std_ss []
       ++ MATCH_MP_TAC SUB_ADD
       ++ FULL_SIMP_TAC real_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING])
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   >> ( Cases_on `x`
        ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ,DIFF_DEF,
	   	  	  GSPECIFICATION,IN_UNIV,IN_SING]
        ++ RW_TAC real_ss [ind_typeTheory.NUMPAIR])
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

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
   ++ REVERSE CONJ_TAC
   >> (Q.EXISTS_TAC `(\(x,y). x - 1:num)`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV, IN_CROSS]
       ++ Q.EXISTS_TAC `(x+1,1)`
       ++ RW_TAC std_ss [DIFF_DEF,GSPECIFICATION,IN_UNIV,IN_SING]
       )
   ++ Q.EXISTS_TAC `UNCURRY ind_type$NUMPAIR`
   ++ RW_TAC std_ss [INJ_DEF, IN_UNIV, IN_CROSS]
   ++ Cases_on `x`
   ++ Cases_on `y`
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [UNCURRY_DEF, ind_typeTheory.NUMPAIR_INJ]);

val NUM_2D_BIJ_NZ_ALT2_INV = store_thm
  ("NUM_2D_BIJ_NZ_ALT2_INV",
   ``?f.
       BIJ f (UNIV : num -> bool)
       (((UNIV : num -> bool) DIFF {0}) CROSS ((UNIV : num -> bool) DIFF {0}))``,
   PROVE_TAC [NUM_2D_BIJ_NZ_ALT2, BIJ_SYM]);

val BIGUNION_PAIR = store_thm
  ("BIGUNION_PAIR",
   ``!s t. BIGUNION {s; t} = s UNION t``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_UNION, IN_INSERT, NOT_IN_EMPTY]
   ++ PROVE_TAC []);

val FINITE_COUNTABLE = store_thm
  ("FINITE_COUNTABLE",
   ``!s. FINITE s ==> countable s``,
   REWRITE_TAC [countable_def]
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [NOT_IN_EMPTY]
   ++ Q.EXISTS_TAC `\n. if n = 0 then e else f (n - 1)`
   ++ RW_TAC std_ss [IN_INSERT] >> PROVE_TAC []
   ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `SUC n`
   ++ RW_TAC std_ss [SUC_SUB1]);

val BIJ_NUM_COUNTABLE = store_thm
  ("BIJ_NUM_COUNTABLE",
   ``!s. (?f : num -> 'a. BIJ f UNIV s) ==> countable s``,
   RW_TAC std_ss [countable_def, BIJ_DEF, SURJ_DEF, IN_UNIV]
   ++ PROVE_TAC []);

val COUNTABLE_EMPTY = store_thm
  ("COUNTABLE_EMPTY",
   ``countable {}``,
   PROVE_TAC [FINITE_COUNTABLE, FINITE_EMPTY]);

val COUNTABLE_IMAGE = store_thm
  ("COUNTABLE_IMAGE",
   ``!s f. countable s ==> countable (IMAGE f s)``,
   RW_TAC std_ss [countable_def, IN_IMAGE]
   ++ Q.EXISTS_TAC `f o f'`
   ++ RW_TAC std_ss [o_THM]
   ++ PROVE_TAC []);

val COUNTABLE_BIGUNION = store_thm
  ("COUNTABLE_BIGUNION",
   ``!c.
       countable c /\ (!s. s IN c ==> countable s) ==> countable (BIGUNION c)``,
   RW_TAC std_ss [countable_def]
   ++ POP_ASSUM
      (MP_TAC o CONV_RULE (DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV))
   ++ MP_TAC NUM_2D_BIJ_INV
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(\ (a : num, b : num). f'' (f a) b) o f'`
   ++ RW_TAC std_ss [IN_BIGUNION]
   ++ Q.PAT_ASSUM `!x. P x ==> ?y. Q x y` (MP_TAC o Q.SPEC `s`)
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `f (n : num)`)
   ++ RW_TAC std_ss []
   ++ POP_ASSUM (MP_TAC o Q.SPEC `x`)
   ++ RW_TAC std_ss []
   ++ Q.PAT_ASSUM `BIJ f' X Y` MP_TAC
   ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `(n, n')`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `y`
   ++ RW_TAC std_ss [o_THM]);

val COUNTABLE_UNION = store_thm
  ("COUNTABLE_UNION",
   ``!s t. countable s /\ countable t ==> countable (s UNION t)``,
   RW_TAC std_ss [GSYM BIGUNION_PAIR]
   ++ MATCH_MP_TAC COUNTABLE_BIGUNION
   ++ (RW_TAC std_ss [IN_INSERT, NOT_IN_EMPTY]
       ++ RW_TAC std_ss [])
   ++ MATCH_MP_TAC FINITE_COUNTABLE
   ++ RW_TAC std_ss [FINITE_INSERT, FINITE_EMPTY]);

val FINITE_INJ = store_thm
  ("FINITE_INJ",
   ``!f s t. INJ f s t /\ FINITE t ==> FINITE s``,
   STRIP_TAC
   ++ Suff `!t. FINITE t ==> !s. INJ f s t ==> FINITE s`
   >> PROVE_TAC []
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [INJ_EMPTY, FINITE_EMPTY]
   ++ REVERSE (Cases_on `?x. x IN s /\ (f x = e)`)
   >> (Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
       ++ Q.PAT_ASSUM `INJ f p q` MP_TAC
       ++ RW_TAC std_ss [INJ_DEF, IN_INSERT]
       ++ PROVE_TAC [])
   ++ POP_ASSUM MP_TAC
   ++ STRIP_TAC
   ++ Suff `FINITE (s DELETE x)` >> PROVE_TAC [FINITE_DELETE]
   ++ Q.PAT_ASSUM `!s. P s` MATCH_MP_TAC
   ++ Q.PAT_ASSUM `INJ f p q` MP_TAC
   ++ RW_TAC std_ss [INJ_DEF, IN_INSERT, IN_DELETE]
   ++ PROVE_TAC []);

val INFINITE_INJ = store_thm
  ("INFINITE_INJ",
   ``!f s t. INJ f s t /\ INFINITE s ==> INFINITE t``,
   PROVE_TAC [INFINITE_DEF, FINITE_INJ]);

val ENUMERATE = store_thm
  ("ENUMERATE",
   ``!s. (?f : num -> 'a. BIJ f UNIV s) = BIJ (enumerate s) UNIV s``,
   RW_TAC std_ss [boolTheory.EXISTS_DEF, enumerate_def]);

val FINITE_REST = store_thm
  ("FINITE_REST",
   ``!s. FINITE (REST s) = FINITE s``,
   RW_TAC std_ss [REST_DEF, FINITE_DELETE]);

val EXPLICIT_ENUMERATE_MONO = store_thm
  ("EXPLICIT_ENUMERATE_MONO",
   ``!n s. FUNPOW REST n s SUBSET s``,
   Induct >> RW_TAC std_ss [FUNPOW, SUBSET_DEF]
   ++ RW_TAC std_ss [FUNPOW_SUC]
   ++ PROVE_TAC [SUBSET_TRANS, REST_SUBSET]);

val EXPLICIT_ENUMERATE_NOT_EMPTY = store_thm
  ("EXPLICIT_ENUMERATE_NOT_EMPTY",
   ``!n s. INFINITE s ==> ~(FUNPOW REST n s = {})``,
   REWRITE_TAC [INFINITE_DEF]
   ++ Induct >> (RW_TAC std_ss [FUNPOW] ++ PROVE_TAC [FINITE_EMPTY])
   ++ RW_TAC std_ss [FUNPOW]
   ++ Q.PAT_ASSUM `!s. P s` (MP_TAC o Q.SPEC `REST s`)
   ++ PROVE_TAC [FINITE_REST]);

val INFINITE_EXPLICIT_ENUMERATE = store_thm
  ("INFINITE_EXPLICIT_ENUMERATE",
   ``!s. INFINITE s ==> INJ (\n : num. CHOICE (FUNPOW REST n s)) UNIV s``,
   RW_TAC std_ss [INJ_DEF, IN_UNIV]
   >> (Suff `CHOICE (FUNPOW REST n s) IN FUNPOW REST n s`
       >> PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
       ++ RW_TAC std_ss [GSYM CHOICE_DEF, EXPLICIT_ENUMERATE_NOT_EMPTY])
   ++ !! (POP_ASSUM MP_TAC)
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ Q.SPEC_TAC (`n'`, `y`)
   ++ Q.SPEC_TAC (`n`, `x`)
   ++ (Induct ++ Cases) <<
   [PROVE_TAC [],
    !! STRIP_TAC
    ++ Suff `~(CHOICE (FUNPOW REST 0 s) IN FUNPOW REST (SUC n) s)`
    >> (RW_TAC std_ss []
        ++ MATCH_MP_TAC CHOICE_DEF
        ++ PROVE_TAC [EXPLICIT_ENUMERATE_NOT_EMPTY])
    ++ POP_ASSUM K_TAC
    ++ RW_TAC std_ss [FUNPOW]
    ++ Suff `~(CHOICE s IN REST s)`
    >> PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
    ++ PROVE_TAC [CHOICE_NOT_IN_REST],
    !! STRIP_TAC
    ++ POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
    ++ Suff `~(CHOICE (FUNPOW REST 0 s) IN FUNPOW REST (SUC x) s)`
    >> (RW_TAC std_ss []
        ++ MATCH_MP_TAC CHOICE_DEF
        ++ PROVE_TAC [EXPLICIT_ENUMERATE_NOT_EMPTY])
    ++ POP_ASSUM K_TAC
    ++ RW_TAC std_ss [FUNPOW]
    ++ Suff `~(CHOICE s IN REST s)`
    >> PROVE_TAC [SUBSET_DEF, EXPLICIT_ENUMERATE_MONO]
    ++ PROVE_TAC [CHOICE_NOT_IN_REST],
    RW_TAC std_ss [FUNPOW]
    ++ Q.PAT_ASSUM `!y. P y` (MP_TAC o Q.SPECL [`n`, `REST s`])
    ++ PROVE_TAC [INFINITE_DEF, FINITE_REST]]);

val COUNTABLE_ALT = store_thm
  ("COUNTABLE_ALT",
   ``!s. countable s = FINITE s \/ BIJ (enumerate s) UNIV s``,
   Strip
   ++ REVERSE EQ_TAC >> PROVE_TAC [FINITE_COUNTABLE, BIJ_NUM_COUNTABLE]
   ++ RW_TAC std_ss [countable_def]
   ++ Cases_on `FINITE s` >> PROVE_TAC []
   ++ RW_TAC std_ss [GSYM ENUMERATE]
   ++ MATCH_MP_TAC BIJ_INJ_SURJ
   ++ REVERSE CONJ_TAC
   >> (Know `~(s = {})` >> PROVE_TAC [FINITE_EMPTY]
       ++ RW_TAC std_ss [GSYM MEMBER_NOT_EMPTY]
       ++ Q.EXISTS_TAC `\n. if f n IN s then f n else x`
       ++ RW_TAC std_ss [SURJ_DEF, IN_UNIV]
       ++ PROVE_TAC [])
   ++ MP_TAC (Q.SPEC `s` INFINITE_EXPLICIT_ENUMERATE)
   ++ RW_TAC std_ss [INFINITE_DEF]
   ++ PROVE_TAC []);

val DISJOINT_COUNT = store_thm
  ("DISJOINT_COUNT",
   ``!f.
       (!m n : num. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
       (!n. DISJOINT (f n) (BIGUNION (IMAGE f (count n))))``,
   RW_TAC arith_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
                    IN_BIGUNION, IN_IMAGE, IN_COUNT]
   ++ REVERSE (Cases_on `x IN f n`) >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ REVERSE (Cases_on `x IN s`) >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ REVERSE (Cases_on `x' < n`) >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Know `~(x':num = n)` >> DECIDE_TAC
   ++ PROVE_TAC []);

val PREIMAGE_def = Define `PREIMAGE f s = {x | f x IN s}`;
val prod_sets_def = Define `prod_sets a b = {s CROSS t | s IN a /\ t IN b}`;

val K_PARTIAL = store_thm
  ("K_PARTIAL",
   ``!x. K x = \z. x``,
   RW_TAC std_ss [K_DEF]);

val IN_o = store_thm
  ("IN_o",
   ``!x f s. x IN (s o f) = f x IN s``,
   RW_TAC std_ss [SPECIFICATION, o_THM]);


val PREIMAGE_ALT = store_thm
  ("PREIMAGE_ALT",
   ``!f s. PREIMAGE f s = s o f``,
   RW_TAC std_ss [PREIMAGE_def, EXTENSION, GSPECIFICATION, IN_o]);

val IN_PREIMAGE = store_thm
  ("IN_PREIMAGE",
   ``!f s x. x IN PREIMAGE f s = f x IN s``,
   RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]);

val IN_BIGUNION_IMAGE = store_thm
  ("IN_BIGUNION_IMAGE",
   ``!f s y. y IN BIGUNION (IMAGE f s) = ?x. x IN s /\ y IN f x``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE]
   ++ PROVE_TAC []);

val IN_BIGINTER_IMAGE = store_thm
  ("IN_BIGINTER_IMAGE",
   ``!x f s. x IN BIGINTER (IMAGE f s) = (!y. y IN s ==> x IN f y)``,
   RW_TAC std_ss [IN_BIGINTER, IN_IMAGE]
   ++ PROVE_TAC []);

val PREIMAGE_EMPTY = store_thm
  ("PREIMAGE_EMPTY",
   ``!f. PREIMAGE f {} = {}``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, NOT_IN_EMPTY]);

val PREIMAGE_UNIV = store_thm
  ("PREIMAGE_UNIV",
   ``!f. PREIMAGE f UNIV = UNIV``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_UNIV]);

val PREIMAGE_COMPL = store_thm
  ("PREIMAGE_COMPL",
   ``!f s. PREIMAGE f (COMPL s) = COMPL (PREIMAGE f s)``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_COMPL]);

val PREIMAGE_UNION = store_thm
  ("PREIMAGE_UNION",
   ``!f s t. PREIMAGE f (s UNION t) = PREIMAGE f s UNION PREIMAGE f t``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_UNION]);

val PREIMAGE_INTER = store_thm
  ("PREIMAGE_INTER",
   ``!f s t. PREIMAGE f (s INTER t) = PREIMAGE f s INTER PREIMAGE f t``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_INTER]);

val PREIMAGE_BIGUNION = store_thm
  ("PREIMAGE_BIGUNION",
   ``!f s. PREIMAGE f (BIGUNION s) = BIGUNION (IMAGE (PREIMAGE f) s)``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_BIGUNION_IMAGE]
   ++ RW_TAC std_ss [IN_BIGUNION]
   ++ PROVE_TAC []);

val PREIMAGE_COMP = store_thm
  ("PREIMAGE_COMP",
   ``!f g s. PREIMAGE f (PREIMAGE g s) = PREIMAGE (g o f) s``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, o_THM]);

val PREIMAGE_DIFF = store_thm
  ("PREIMAGE_DIFF",
   ``!f s t. PREIMAGE f (s DIFF t) = PREIMAGE f s DIFF PREIMAGE f t``,
   RW_TAC std_ss [Once EXTENSION, IN_PREIMAGE, IN_DIFF]);

val PREIMAGE_I = store_thm
  ("PREIMAGE_I",
   ``PREIMAGE I = I``,
  METIS_TAC [EXTENSION,IN_PREIMAGE, I_THM]);

val IMAGE_I = store_thm
  ("IMAGE_I",
   ``IMAGE I = I``,
  RW_TAC std_ss [FUN_EQ_THM]
  ++ METIS_TAC [SPECIFICATION,IN_IMAGE,I_THM]);

val PREIMAGE_K = store_thm
  ("PREIMAGE_K",
   ``!x s. PREIMAGE (K x) s = if x IN s then UNIV else {}``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, K_THM, IN_UNIV, NOT_IN_EMPTY]);

val PREIMAGE_DISJOINT = store_thm
  ("PREIMAGE_DISJOINT",
   ``!f s t. DISJOINT s t ==> DISJOINT (PREIMAGE f s) (PREIMAGE f t)``,
   RW_TAC std_ss [DISJOINT_DEF, GSYM PREIMAGE_INTER, PREIMAGE_EMPTY]);

val PREIMAGE_SUBSET = store_thm
  ("PREIMAGE_SUBSET",
   ``!f s t. s SUBSET t ==> PREIMAGE f s SUBSET PREIMAGE f t``,
   RW_TAC std_ss [SUBSET_DEF, PREIMAGE_def, GSPECIFICATION]);

val SUBSET_ADD = store_thm
  ("SUBSET_ADD",
   ``!f n d.
       (!n. f n SUBSET f (SUC n)) ==>
       f n SUBSET f (n + d)``,
   RW_TAC std_ss []
   ++ Induct_on `d` >> RW_TAC arith_ss [SUBSET_REFL]
   ++ RW_TAC std_ss [ADD_CLAUSES]
   ++ MATCH_MP_TAC SUBSET_TRANS
   ++ Q.EXISTS_TAC `f (n + d)`
   ++ RW_TAC std_ss []);

val DISJOINT_DIFFS = store_thm
  ("DISJOINT_DIFFS",
   ``!f m n.
       (!n. f n SUBSET f (SUC n)) /\
       (!n. g n = f (SUC n) DIFF f n) /\ ~(m = n) ==>
       DISJOINT (g m) (g n)``,
   RW_TAC std_ss []
   ++ Know `SUC m <= n \/ SUC n <= m` >> DECIDE_TAC
   ++ REWRITE_TAC [LESS_EQ_EXISTS]
   ++ STRIP_TAC <<
   [Know `f (SUC m) SUBSET f n` >> PROVE_TAC [SUBSET_ADD]
    ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER,
                      NOT_IN_EMPTY, IN_DIFF, SUBSET_DEF]
    ++ PROVE_TAC [],
    Know `f (SUC n) SUBSET f m` >> PROVE_TAC [SUBSET_ADD]
    ++ RW_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER,
                      NOT_IN_EMPTY, IN_DIFF, SUBSET_DEF]
    ++ PROVE_TAC []]);

val IMAGE_IMAGE = store_thm
  ("IMAGE_IMAGE",
   ``!f g s. IMAGE f (IMAGE g s) = IMAGE (f o g) s``,
   RW_TAC std_ss [EXTENSION, IN_IMAGE, o_THM]
   ++ PROVE_TAC []);

val IN_PROD_SETS = store_thm
  ("IN_PROD_SETS",
   ``!s a b. s IN prod_sets a b = ?t u. (s = t CROSS u) /\ t IN a /\ u IN b``,
   RW_TAC std_ss [prod_sets_def, GSPECIFICATION, UNCURRY]
   ++ EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `(t, u)`
   ++ RW_TAC std_ss []);

val PREIMAGE_CROSS = store_thm
  ("PREIMAGE_CROSS",
   ``!f a b.
       PREIMAGE f (a CROSS b) =
       PREIMAGE (FST o f) a INTER PREIMAGE (SND o f) b``,
   RW_TAC std_ss [EXTENSION, IN_PREIMAGE, IN_CROSS, IN_INTER, o_THM]);

val FUNSET_INTER = store_thm
  ("FUNSET_INTER",
   ``!a b c. (a -> b INTER c) = (a -> b) INTER (a -> c)``,
   RW_TAC std_ss [EXTENSION, IN_FUNSET, IN_INTER]
   ++ PROVE_TAC []);

val UNIV_NEQ_EMPTY = store_thm
  ("UNIV_NEQ_EMPTY",
   ``~(UNIV={})``,
   RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_UNIV]);

val COUNTABLE_NUM = store_thm
  ("COUNTABLE_NUM",
   ``!s : num -> bool. countable s``,
   RW_TAC std_ss [countable_def]
   ++ Q.EXISTS_TAC `I`
   ++ RW_TAC std_ss [I_THM]);

val COUNTABLE_IMAGE_NUM = store_thm
  ("COUNTABLE_IMAGE_NUM",
   ``!f : num -> 'a. !s. countable (IMAGE f s)``,
   PROVE_TAC [COUNTABLE_NUM, COUNTABLE_IMAGE]);

val COUNTABLE_ENUM = store_thm
  ("COUNTABLE_ENUM",
   ``!c. countable c = (c = {}) \/ (?f : num -> 'a. c = IMAGE f UNIV)``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC
   >> (NTAC 2 (RW_TAC std_ss [COUNTABLE_EMPTY])
       ++ RW_TAC std_ss [countable_def]
       ++ Q.EXISTS_TAC `f`
       ++ RW_TAC std_ss [IN_IMAGE, IN_UNIV]
       ++ PROVE_TAC [])
   ++ REVERSE (RW_TAC std_ss [COUNTABLE_ALT])
   >> (DISJ2_TAC
       ++ Q.EXISTS_TAC `enumerate c`
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [IN_UNIV, IN_IMAGE, BIJ_DEF, SURJ_DEF, EXTENSION]
       ++ PROVE_TAC [])
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`c`, `c`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss []
   >> (DISJ2_TAC
       ++ Q.EXISTS_TAC `K e`
       ++ RW_TAC std_ss [EXTENSION, IN_SING, IN_IMAGE, IN_UNIV, K_THM])
   ++ DISJ2_TAC
   ++ Q.EXISTS_TAC `\n. num_CASE n e f`
   ++ RW_TAC std_ss [IN_INSERT, IN_IMAGE, EXTENSION, IN_UNIV]
   ++ EQ_TAC <<
   [RW_TAC std_ss [] <<
    [Q.EXISTS_TAC `0`
     ++ RW_TAC std_ss [num_case_def],
     Q.EXISTS_TAC `SUC x'`
     ++ RW_TAC std_ss [num_case_def]],
    RW_TAC std_ss [] ++
    METIS_TAC [num_case_def, TypeBase.nchotomy_of ``:num``]]
    );

val BIGUNION_IMAGE_UNIV = store_thm
  ("BIGUNION_IMAGE_UNIV",
   ``!f N.
       (!n. N <= n ==> (f n = {})) ==>
       (BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f (count N)))``,
   RW_TAC std_ss [EXTENSION, IN_BIGUNION, IN_IMAGE, IN_UNIV, IN_COUNT,
                  NOT_IN_EMPTY]
   ++ REVERSE EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [NOT_LESS]);

val BIJ_ALT = store_thm
  ("BIJ_ALT",
   ``!f s t. BIJ f s t = f IN (s -> t) /\ (!y :: t. ?!x :: s. y = f x)``,
   RW_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, RES_EXISTS_UNIQUE_ALT]
   ++ RESQ_TAC
   ++ RW_TAC std_ss [IN_FUNSET, IN_DFUNSET, GSYM CONJ_ASSOC]
   ++ Know `!a b c. (a ==> (b = c)) ==> (a /\ b = a /\ c)` >> PROVE_TAC []
   ++ DISCH_THEN MATCH_MP_TAC
   ++ REPEAT (STRIP_TAC ORELSE EQ_TAC) <<
   [PROVE_TAC [],
    Q.PAT_ASSUM `!x. P x`
    (fn th =>
     MP_TAC (Q.SPEC `(f:'a->'b) x` th)
     ++ MP_TAC (Q.SPEC `(f:'a->'b) y` th))
    ++ Cond >> PROVE_TAC []
    ++ STRIP_TAC
    ++ Cond >> PROVE_TAC []
    ++ STRIP_TAC
    ++ PROVE_TAC [],
    PROVE_TAC [],
    PROVE_TAC []]);

val BIJ_FINITE_SUBSET = store_thm
  ("BIJ_FINITE_SUBSET",
   ``!(f : num -> 'a) s t.
       BIJ f UNIV s /\ FINITE t /\ t SUBSET s ==>
       ?N. !n. N <= n ==> ~(f n IN t)``,
   RW_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Q.SPEC_TAC (`t`, `t`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [EMPTY_SUBSET, NOT_IN_EMPTY, INSERT_SUBSET, IN_INSERT]
   ++ Know `?!k. f k = e`
   >> (Q.PAT_ASSUM `BIJ a b c` MP_TAC
       ++ RW_TAC std_ss [BIJ_ALT, RES_EXISTS_UNIQUE_UNIV, RES_FORALL]
       ++ PROVE_TAC [])
   ++ CONV_TAC (DEPTH_CONV EXISTS_UNIQUE_CONV)
   ++ RW_TAC std_ss []
   ++ RES_TAC
   ++ Q.EXISTS_TAC `MAX N (SUC k)`
   ++ RW_TAC std_ss [MAX_LE_X]
   ++ STRIP_TAC
   ++ Know `n = k` >> PROVE_TAC []
   ++ DECIDE_TAC);

val NUM_2D_BIJ_SMALL_SQUARE = store_thm
  ("NUM_2D_BIJ_SMALL_SQUARE",
   ``!(f : num -> num # num) k.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?N. count k CROSS count k SUBSET IMAGE f (count N)``,
   Strip
   ++ (MP_TAC o
       Q.SPECL [`f`, `UNIV CROSS UNIV`, `count k CROSS count k`] o
       INST_TYPE [``:'a`` |-> ``:num # num``]) BIJ_FINITE_SUBSET
   ++ RW_TAC std_ss [CROSS_SUBSET, SUBSET_UNIV, FINITE_CROSS, FINITE_COUNT]
   ++ Q.EXISTS_TAC `N`
   ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT]
   ++ Q.PAT_ASSUM `BIJ a b c` MP_TAC
   ++ RW_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_UNIV, IN_CROSS]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `x`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `y`
   ++ RW_TAC std_ss []
   ++ Suff `~(N <= y)` >> DECIDE_TAC
   ++ PROVE_TAC []);

val NUM_2D_BIJ_BIG_SQUARE = store_thm
  ("NUM_2D_BIJ_BIG_SQUARE",
   ``!(f : num -> num # num) N.
       BIJ f UNIV (UNIV CROSS UNIV) ==>
       ?k. IMAGE f (count N) SUBSET count k CROSS count k``,
   RW_TAC std_ss [IN_CROSS, IN_COUNT, SUBSET_DEF, IN_IMAGE, IN_COUNT]
   ++ Induct_on `N` >> RW_TAC arith_ss []
   ++ Strip
   ++ Cases_on `f N`
   ++ REWRITE_TAC [prim_recTheory.LESS_THM]
   ++ Q.EXISTS_TAC `SUC (MAX k (MAX q r))`
   ++ Know `!a b. a < SUC b = a <= b`
   >> (KILL_TAC
       ++ DECIDE_TAC)
   ++ RW_TAC std_ss []
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [X_LE_MAX, LESS_EQ_REFL, LESS_IMP_LESS_OR_EQ]);

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
	    ++ RW_TAC std_ss [NOT_IN_EMPTY, IN_INSERT]
	    ++ Q.PAT_ASSUM `!f. (!x. (f x = {}) \/ f x IN s) /\ ~({} IN s) /\
				(!m n. ~(m = n) ==> DISJOINT (f m) (f n)) ==>
            			?N:num. !n. n >= N ==> (f n = {})`
		(MP_TAC o Q.SPEC `(\x. if f x = e then {} else f x)`)
	    ++ `(!x. ((\x. (if f x = e then {} else f x)) x = {}) \/
		     (\x. (if f x = e then {} else f x)) x IN s) /\ ~({} IN s)`
		by METIS_TAC []
	    ++ ASM_SIMP_TAC std_ss []
	    ++ `(!m n. ~(m = n) ==> DISJOINT (if f m = e then {} else f m)
			(if f n = e then {} else f n))`
		by (RW_TAC std_ss [IN_DISJOINT, NOT_IN_EMPTY]
			    ++ METIS_TAC [IN_DISJOINT])
	    ++ ASM_SIMP_TAC std_ss []
	    ++ RW_TAC std_ss []
	    ++ Cases_on `?n. f n = e`
	    >> (FULL_SIMP_TAC std_ss []
		++ Cases_on `n < N`
		>> (Q.EXISTS_TAC `N`
		    ++ RW_TAC std_ss [GREATER_EQ]
		    ++ `~(n' = n)`
			by METIS_TAC [LESS_LESS_EQ_TRANS,
				      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
		    ++ Cases_on `f n' = f n`
		    >> (`DISJOINT (f n') (f n)` by METIS_TAC []
			++ FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
			++ METIS_TAC [])
		    ++ Q.PAT_ASSUM
				`!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
				(MP_TAC o Q.SPEC `n'`)
		    ++ ASM_SIMP_TAC std_ss [GREATER_EQ])
		++ Q.EXISTS_TAC `SUC n`
		++ RW_TAC std_ss [GREATER_EQ]
		++ FULL_SIMP_TAC std_ss [NOT_LESS]
		++ `~(n' = n)`
			by METIS_TAC [LESS_LESS_EQ_TRANS,
				      DECIDE ``!n:num. n < SUC n``,
				      DECIDE ``!m (n:num). m < n ==> ~(m=n)``]
		++ Cases_on `f n' = f n`
		>> (`DISJOINT (f n') (f n)` by METIS_TAC []
		    ++ FULL_SIMP_TAC std_ss [IN_DISJOINT, EXTENSION, NOT_IN_EMPTY]
		    ++ METIS_TAC [])
		++ `N <= n'` by METIS_TAC [LESS_EQ_IMP_LESS_SUC,
				           LESS_LESS_EQ_TRANS,
				           LESS_IMP_LESS_OR_EQ]
		++ Q.PAT_ASSUM
				`!n'. n' >= N ==> ((if f n' = f n then {} else f n') = {})`
				(MP_TAC o Q.SPEC `n'`)
		++ ASM_SIMP_TAC std_ss [GREATER_EQ])
	++ METIS_TAC [])
   ++ REPEAT STRIP_TAC
   ++ Cases_on `{} IN s`
   >> (Q.PAT_ASSUM `!s. FINITE s ==> P` (MP_TAC o Q.SPEC `s DELETE {}`)
       ++ RW_TAC std_ss [FINITE_DELETE, IN_INSERT, IN_DELETE])
   ++ METIS_TAC [IN_INSERT]);

val SUBSET_INTER1 = store_thm
  ("SUBSET_INTER1",
   ``!s t. s SUBSET t ==> (s INTER t = s)``,
   RW_TAC std_ss [EXTENSION,GSPECIFICATION,SUBSET_DEF, IN_INTER]
   ++ PROVE_TAC []);

val SUBSET_INTER2 = store_thm
  ("SUBSET_INTER2",
   ``!s t. s SUBSET t ==> (t INTER s = s)``,
   RW_TAC std_ss [EXTENSION,GSPECIFICATION,SUBSET_DEF, IN_INTER]
   ++ PROVE_TAC []);

val DIFF_DIFF_SUBSET = store_thm
  ("DIFF_DIFF_SUBSET", ``!s t. (t SUBSET s) ==> (s DIFF (s DIFF t) = t)``,
  RW_TAC std_ss [DIFF_DEF,IN_INTER,EXTENSION,GSPECIFICATION,SUBSET_DEF]
  ++ EQ_TAC >> RW_TAC std_ss []
  ++ RW_TAC std_ss []);

val BIGINTER_SUBSET = store_thm
  ("BIGINTER_SUBSET", ``!sp s. (!t. t IN s ==> t SUBSET sp)  /\ (~(s = {}))
                       ==> (BIGINTER s) SUBSET sp``,
  RW_TAC std_ss [SUBSET_DEF,IN_BIGINTER]
  ++ `?u. u IN s` by METIS_TAC [CHOICE_DEF]
  ++ METIS_TAC []);

val DIFF_BIGINTER1 = store_thm
  ("DIFF_BIGINTER1",
    ``!sp s. sp DIFF (BIGINTER s) = BIGUNION (IMAGE (\u. sp DIFF u) s)``,
  SRW_TAC [][EXTENSION]
  ++ EQ_TAC >> METIS_TAC [IN_DIFF]
  ++ RW_TAC std_ss []
  ++ METIS_TAC []);

val DIFF_BIGINTER = store_thm
   ("DIFF_BIGINTER", ``!sp s. (!t. t IN s ==> t SUBSET sp)  /\ (~(s = {}))
         ==> ( BIGINTER s = sp DIFF (BIGUNION (IMAGE (\u. sp DIFF u) s)) )``,
  RW_TAC std_ss []
  ++ `(BIGINTER s SUBSET sp)` by RW_TAC std_ss [BIGINTER_SUBSET]
  ++ ASSUME_TAC (Q.SPECL [`sp`,`s`] DIFF_BIGINTER1)
  ++ `sp DIFF (sp DIFF (BIGINTER s)) = (BIGINTER s)` by RW_TAC std_ss [DIFF_DIFF_SUBSET]
  ++ METIS_TAC []);

val DIFF_INTER = store_thm
  ("DIFF_INTER", ``!s t g. (s DIFF t) INTER g = s INTER g DIFF t``,
  RW_TAC std_ss [DIFF_DEF,INTER_DEF,EXTENSION]
  ++ RW_TAC std_ss [GSPECIFICATION]
  ++ EQ_TAC >> RW_TAC std_ss [] ++ RW_TAC std_ss []);

val DIFF_INTER2 = store_thm
  ("DIFF_INTER2", ``!s t. s DIFF (t INTER s) = s DIFF t``,
  RW_TAC std_ss [DIFF_DEF,INTER_DEF,EXTENSION]
  ++ RW_TAC std_ss [GSPECIFICATION,LEFT_AND_OVER_OR]);

val PREIMAGE_COMPL_INTER = store_thm
  ("PREIMAGE_COMPL_INTER", ``!f t sp. PREIMAGE f (COMPL t) INTER sp = sp DIFF (PREIMAGE f t)``,
  RW_TAC std_ss [COMPL_DEF]
  ++ MP_TAC (REWRITE_RULE [PREIMAGE_UNIV] (Q.SPECL [`f`,`UNIV`,`t`] PREIMAGE_DIFF))
  ++ STRIP_TAC
  ++ `(PREIMAGE f (UNIV DIFF t)) INTER sp = (UNIV DIFF PREIMAGE f t) INTER sp` by METIS_TAC []
  ++ METIS_TAC [DIFF_INTER,INTER_UNIV]);

val PREIMAGE_REAL_COMPL1 = store_thm
  ("PREIMAGE_REAL_COMPL1", ``!c:real. COMPL {x | c < x} = {x | x <= c}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  ++ RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]);

val PREIMAGE_REAL_COMPL2 = store_thm
  ("PREIMAGE_REAL_COMPL2", ``!c:real. COMPL {x | c <= x} = {x | x < c}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  ++ RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]);


val PREIMAGE_REAL_COMPL3 = store_thm
  ("PREIMAGE_REAL_COMPL3", ``!c:real. COMPL {x | x <= c} = {x | c < x}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  ++ RW_TAC real_ss [GSPECIFICATION,GSYM real_lt,SPECIFICATION]);

val PREIMAGE_REAL_COMPL4 = store_thm
  ("PREIMAGE_REAL_COMPL4", ``!c:real. COMPL {x | x < c} = {x | c <= x}``,
  RW_TAC real_ss [COMPL_DEF,UNIV_DEF,DIFF_DEF,EXTENSION]
  ++ RW_TAC real_ss [GSPECIFICATION,GSYM real_lte,SPECIFICATION]);

val ELT_IN_DELETE = store_thm
  ("ELT_IN_DELETE",
   ``!x s. ~(x IN (s DELETE x))``,
   RW_TAC std_ss [IN_DELETE]);

val DELETE_THEN_INSERT = store_thm
  ("DELETE_THEN_INSERT",
   ``!s. !x :: s. x INSERT (s DELETE x) = s``,
   RESQ_TAC
   ++ RW_TAC std_ss [INSERT_DELETE]);

val BIJ_INSERT = store_thm
  ("BIJ_INSERT",
   ``!f e s t.
       ~(e IN s) /\ BIJ f (e INSERT s) t ==>
       ?u. (f e INSERT u = t) /\ ~(f e IN u) /\ BIJ f s u``,
   RW_TAC std_ss [BIJ_ALT]
   ++ Q.EXISTS_TAC `t DELETE f e`
   ++ FULL_SIMP_TAC std_ss [IN_FUNSET, DELETE_THEN_INSERT, ELT_IN_DELETE, IN_INSERT,
              DISJ_IMP_THM]
   ++ RESQ_TAC
   ++ SIMP_TAC std_ss [IN_DELETE]
   ++ REPEAT STRIP_TAC
   ++ METIS_TAC [IN_INSERT]);

val FINITE_BIJ = store_thm
  ("FINITE_BIJ",
   ``!f s t. FINITE s /\ BIJ f s t ==> FINITE t /\ (CARD s = CARD t)``,
   Suff `!s. FINITE s ==> !f t. BIJ f s t ==> FINITE t /\ (CARD s = CARD t)`
   >> PROVE_TAC []
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ CONJ_TAC >>
	(RW_TAC std_ss [BIJ_ALT, FINITE_EMPTY, CARD_EMPTY, IN_FUNSET, NOT_IN_EMPTY]
	 ++ RESQ_TAC
	 ++ FULL_SIMP_TAC std_ss [NOT_IN_EMPTY]
	 ++ `t = {}`
		by RW_TAC std_ss [EXTENSION, NOT_IN_EMPTY]
	 ++ RW_TAC std_ss [FINITE_EMPTY, CARD_EMPTY])
   ++ NTAC 7 STRIP_TAC
   ++ MP_TAC (Q.SPECL [`f`, `e`, `s`, `t`] BIJ_INSERT)
   ++ ASM_REWRITE_TAC []
   ++ STRIP_TAC
   ++ Know `FINITE u` >> PROVE_TAC []
   ++ STRIP_TAC
   ++ CONJ_TAC >> PROVE_TAC [FINITE_INSERT]
   ++ Q.PAT_ASSUM `f e INSERT u = t` (fn th => RW_TAC std_ss [SYM th])
   ++ RW_TAC std_ss [CARD_INSERT]
   ++ PROVE_TAC []);

val FINITE_BIJ_COUNT = store_thm
  ("FINITE_BIJ_COUNT",
   ``!s. FINITE s = ?c n. BIJ c (count n) s``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC >> PROVE_TAC [FINITE_COUNT, FINITE_BIJ]
   ++ Q.SPEC_TAC (`s`, `s`)
   ++ HO_MATCH_MP_TAC FINITE_INDUCT
   ++ RW_TAC std_ss [BIJ_DEF, INJ_DEF, SURJ_DEF, NOT_IN_EMPTY]
   >> (Q.EXISTS_TAC `c`
       ++ Q.EXISTS_TAC `0`
       ++ RW_TAC std_ss [COUNT_ZERO, NOT_IN_EMPTY])
   ++ Q.EXISTS_TAC `\m. if m = n then e else c m`
   ++ Q.EXISTS_TAC `SUC n`
   ++ Know `!x. x IN count n ==> ~(x = n)`
   >> RW_TAC arith_ss [IN_COUNT]
   ++ RW_TAC std_ss [COUNT_SUC, IN_INSERT]
   ++ PROVE_TAC []);

val GBIGUNION_IMAGE = store_thm
  ("GBIGUNION_IMAGE",
   ``!s p n. {s | ?n. p s n} = BIGUNION (IMAGE (\n. {s | p s n}) UNIV)``,
   RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV]);

val DISJOINT_ALT = store_thm
  ("DISJOINT_ALT",
   ``!s t. DISJOINT s t = !x. x IN s ==> ~(x IN t)``,
   RW_TAC std_ss [IN_DISJOINT]
   ++ PROVE_TAC []);

val DISJOINT_DIFF = store_thm
 ("DISJOINT_DIFF", ``!s t. DISJOINT t (s DIFF t) /\ DISJOINT (s DIFF t) t``,
  RW_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, IN_DIFF]
  ++ METIS_TAC []);

val COUNTABLE_COUNT = store_thm
  ("COUNTABLE_COUNT",
   ``!n. countable (count n)``,
   PROVE_TAC [FINITE_COUNT, FINITE_COUNTABLE]);

val COUNTABLE_SUBSET = store_thm
  ("COUNTABLE_SUBSET",
   ``!s t. s SUBSET t /\ countable t ==> countable s``,
   RW_TAC std_ss [countable_def, SUBSET_DEF]
   ++ Q.EXISTS_TAC `f`
   ++ PROVE_TAC []);


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
   ++ MATCH_MP_TAC REAL_LT_INV
   ++ RW_TAC arith_ss [REAL_LT]);

val HALF_CANCEL = store_thm
  ("HALF_CANCEL",
   ``2 * (1 / 2) = 1:real``,
   Suff `2 * inv 2 = 1:real` >> PROVE_TAC [REAL_INV_1OVER]
   ++ PROVE_TAC [REAL_MUL_RINV, REAL_ARITH ``~(2:real = 0)``]);

val X_HALF_HALF = store_thm
  ("X_HALF_HALF",
   ``!x:real. 1/2 * x + 1/2 * x = x``,
   STRIP_TAC
   ++ MATCH_MP_TAC (REAL_ARITH ``(2 * (a:real) = 2 * b) ==> (a = b)``)
   ++ RW_TAC std_ss [REAL_ADD_LDISTRIB, REAL_MUL_ASSOC, HALF_CANCEL]
   ++ REAL_ARITH_TAC);

val ONE_MINUS_HALF = store_thm
  ("ONE_MINUS_HALF",
   ``(1:real) - 1 / 2 = 1 / 2``,
   MP_TAC (Q.SPEC `1` X_HALF_HALF)
   ++ RW_TAC real_ss []
   ++ MATCH_MP_TAC (REAL_ARITH ``((x:real) + 1 / 2 = y + 1 / 2) ==> (x = y)``)
   ++ RW_TAC std_ss [REAL_SUB_ADD]);

val POW_HALF_POS = store_thm
  ("POW_HALF_POS",
   ``!n. 0:real < (1/2) pow n``,
   STRIP_TAC
   ++ Cases_on `n` >> PROVE_TAC [REAL_ARITH ``0:real < 1``, pow]
   ++ PROVE_TAC [HALF_POS, POW_POS_LT]);

val POW_HALF_SMALL = store_thm
  ("POW_HALF_SMALL",
   ``!e:real. 0 < e ==> ?n. (1 / 2) pow n < e``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPEC `1 / 2` SEQ_POWER)
   ++ RW_TAC std_ss [abs, HALF_LT_1, HALF_POS, REAL_LT_IMP_LE, SEQ]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `e`)
   ++ RW_TAC std_ss [REAL_SUB_RZERO, POW_HALF_POS, REAL_LT_IMP_LE,
                      GREATER_EQ]
   ++ PROVE_TAC [LESS_EQ_REFL]);

val POW_HALF_MONO = store_thm
  ("POW_HALF_MONO",
   ``!m n. m <= n ==> ((1:real)/2) pow n <= (1/2) pow m``,
   REPEAT STRIP_TAC
   ++ Induct_on `n` <<
   [STRIP_TAC
    ++ Know `m:num = 0` >> DECIDE_TAC
    ++ PROVE_TAC [REAL_ARITH ``a:real <= a``],
    Cases_on `m = SUC n` >> PROVE_TAC [REAL_ARITH ``a:real <= a``]
    ++ ONCE_REWRITE_TAC [pow]
    ++ STRIP_TAC
    ++ Know `m:num <= n` >> DECIDE_TAC
    ++ STRIP_TAC
    ++ Suff `(2:real) * ((1/2) * (1/2) pow n) <= 2 * (1/2) pow m`
    >> PROVE_TAC [REAL_ARITH ``0:real < 2``, REAL_LE_LMUL]
    ++ Suff `((1:real)/2) pow n <= 2 * (1/2) pow m`
    >> (KILL_TAC
        ++ PROVE_TAC [GSYM REAL_MUL_ASSOC, HALF_CANCEL, REAL_MUL_LID])
    ++ PROVE_TAC [REAL_ARITH ``!x y. 0:real < x /\ x <= y ==> x <= 2 * y``,
                  POW_HALF_POS]]);

val REAL_LE_LT_MUL = store_thm
  ("REAL_LE_LT_MUL",
   ``!x y : real. 0 <= x /\ 0 < y ==> 0 <= x * y``,
   !! STRIP_TAC
   ++ MP_TAC (Q.SPECL [`0`, `x`, `y`] REAL_LE_RMUL)
   ++ RW_TAC std_ss [REAL_MUL_LZERO]);

val REAL_LT_LE_MUL = store_thm
  ("REAL_LT_LE_MUL",
   ``!x y : real. 0 < x /\ 0 <= y ==> 0 <= x * y``,
   PROVE_TAC [REAL_LE_LT_MUL, REAL_MUL_SYM]);

val REAL_MUL_IDEMPOT = store_thm
  ("REAL_MUL_IDEMPOT",
   ``!r: real. (r * r = r) = (r = 0) \/ (r = 1)``,
   GEN_TAC
   ++ REVERSE EQ_TAC
   >> (RW_TAC real_ss [] ++ RW_TAC std_ss [REAL_MUL_LZERO, REAL_MUL_LID])
   ++ RW_TAC std_ss []
   ++ Know `r * r = 1 * r` >> RW_TAC real_ss []
   ++ RW_TAC std_ss [REAL_EQ_RMUL]);

val REAL_SUP_LE_X = store_thm
  ("REAL_SUP_LE_X",
   ``!P x:real. (?r. P r) /\ (!r. P r ==> r <= x) ==> sup P <= x``,
   RW_TAC real_ss []
   ++ Suff `~(x < sup P)` >> REAL_ARITH_TAC
   ++ STRIP_TAC
   ++ MP_TAC (SPEC ``P:real->bool`` REAL_SUP_LE)
   ++ RW_TAC real_ss [] <<
   [PROVE_TAC [],
    PROVE_TAC [],
    EXISTS_TAC ``x:real``
    ++ RW_TAC real_ss []
    ++ PROVE_TAC [real_lte]]);

val REAL_X_LE_SUP = store_thm
  ("REAL_X_LE_SUP",
   ``!P x:real. (?r. P r) /\ (?z. !r. P r ==> r <= z) /\ (?r. P r /\ x <= r)
           ==> x <= sup P``,
   RW_TAC real_ss []
   ++ Suff `!y. P y ==> y <= sup P` >> PROVE_TAC [REAL_LE_TRANS]
   ++ MATCH_MP_TAC REAL_SUP_UBOUND_LE
   ++ PROVE_TAC []);

val INF_DEF_ALT = store_thm
  ("INF_DEF_ALT",
   ``!p. inf p = ~(sup (\r. ~r IN p)):real``,
   RW_TAC std_ss []
   ++ PURE_REWRITE_TAC [inf_def, IMAGE_DEF]
   ++ Suff `(\r. p (-r)) = (\r. -r IN p)`
   >> RW_TAC std_ss []
   ++ RW_TAC std_ss [FUN_EQ_THM,SPECIFICATION]);

val LE_INF = store_thm
  ("LE_INF",
   ``!p r:real. (?x. x IN p) /\ (!x. x IN p ==> r <= x) ==> r <= inf p``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   ++ POP_ASSUM MP_TAC
   ++ ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   ++ Q.SPEC_TAC (`~r`, `r`)
   ++ RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   ++ MATCH_MP_TAC REAL_SUP_LE_X
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [REAL_NEGNEG]);

val INF_LE = store_thm
  ("INF_LE",
   ``!p r:real.
       (?z. !x. x IN p ==> z <= x) /\ (?x. x IN p /\ x <= r) ==> inf p <= r``,
   RW_TAC std_ss [INF_DEF_ALT, SPECIFICATION]
   ++ POP_ASSUM MP_TAC
   ++ ONCE_REWRITE_TAC [GSYM REAL_NEGNEG]
   ++ Q.SPEC_TAC (`~r`, `r`)
   ++ RW_TAC real_ss [REAL_NEGNEG, REAL_LE_NEG]
   ++ MATCH_MP_TAC REAL_X_LE_SUP
   ++ RW_TAC std_ss []
   ++ PROVE_TAC [REAL_NEGNEG, REAL_LE_NEG]);

val INF_GREATER = store_thm
  ("INF_GREATER",
   ``!p z:real.
       (?x. x IN p) /\ inf p < z ==>
       (?x. x IN p /\ x < z)``,
   RW_TAC std_ss []
   ++ Suff `~(!x. x IN p ==> ~(x < z))` >> PROVE_TAC []
   ++ REWRITE_TAC [GSYM real_lte]
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `inf p < z` MP_TAC
   ++ RW_TAC std_ss [GSYM real_lte]
   ++ MATCH_MP_TAC LE_INF
   ++ PROVE_TAC []);

val INF_CLOSE = store_thm
  ("INF_CLOSE",
   ``!p e:real.
       (?x. x IN p) /\ 0 < e ==> (?x. x IN p /\ x < inf p + e)``,
   RW_TAC std_ss []
   ++ MATCH_MP_TAC INF_GREATER
   ++ CONJ_TAC >> PROVE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ REAL_ARITH_TAC);



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
   ++ Q.PAT_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `n`
   ++ ONCE_REWRITE_TAC [ABS_SUB]
   ++ REVERSE (RW_TAC std_ss [abs])
   >> (Q.PAT_ASSUM `~x` MP_TAC
       ++ Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n'`)
       ++ REAL_ARITH_TAC)
   ++ Know `?d. n' = n + d` >> PROVE_TAC [LESS_EQ_EXISTS]
   ++ RW_TAC std_ss []
   ++ Suff `l < f (n + d) + e` >> REAL_ARITH_TAC
   ++ NTAC 2 (POP_ASSUM K_TAC)
   ++ Induct_on `d` >> RW_TAC arith_ss []
   ++ RW_TAC std_ss [ADD_CLAUSES]
   ++ Q.PAT_ASSUM `!n. f n <= f (SUC n)` (MP_TAC o Q.SPEC `n + d`)
   ++ POP_ASSUM MP_TAC
   ++ REAL_ARITH_TAC);

val SEQ_SANDWICH = store_thm
  ("SEQ_SANDWICH",
   ``!f g h l.
       f --> l /\ h --> l /\ (!n. f n <= g n /\ g n <= h n) ==> g --> l``,
   RW_TAC std_ss [SEQ, GREATER_EQ]
   ++ Q.PAT_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `e`)
   ++ Q.PAT_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `e`)
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `MAX N N'`
   ++ RW_TAC std_ss [MAX_LE_X]
   ++ Q.PAT_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `n`)
   ++ Q.PAT_ASSUM `!e. P e ==> Q e` (MP_TAC o Q.SPEC `n`)
   ++ RW_TAC std_ss []
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ DISCH_THEN (MP_TAC o Q.SPEC `n`)
   ++ RW_TAC std_ss [abs]
   ++ REPEAT (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC);

val SER_POS = store_thm
  ("SER_POS",
   ``!f. summable f /\ (!n. 0 <= f n) ==> 0 <= suminf f``,
   RW_TAC std_ss []
   ++ MP_TAC (Q.SPECL [`f`, `0`] SER_POS_LE)
   ++ RW_TAC std_ss [sum]);

val SER_POS_MONO = store_thm
  ("SER_POS_MONO",
   ``!f. (!n. 0 <= f n) ==> mono (\n. sum (0, n) f)``,
   RW_TAC std_ss [mono]
   ++ DISJ1_TAC
   ++ HO_MATCH_MP_TAC TRIANGLE_2D_NUM
   ++ Induct >> RW_TAC arith_ss [REAL_LE_REFL]
   ++ RW_TAC std_ss [ADD_CLAUSES]
   ++ MATCH_MP_TAC REAL_LE_TRANS
   ++ Q.EXISTS_TAC `sum (0, d + n) f`
   ++ RW_TAC real_ss [sum]
   ++ Q.PAT_ASSUM `!n. 0 <= f n` (MP_TAC o Q.SPEC `d + n`)
   ++ REAL_ARITH_TAC);

val POS_SUMMABLE = store_thm
  ("POS_SUMMABLE",
   ``!f. (!n. 0 <= f n) /\ (?x. !n. sum (0, n) f <= x) ==> summable f``,
   RW_TAC std_ss [summable, sums, GSYM convergent]
   ++ MATCH_MP_TAC SEQ_BCONV
   ++ RW_TAC std_ss [SER_POS_MONO, netsTheory.MR1_BOUNDED]
   ++ Q.EXISTS_TAC `x + 1`
   ++ Q.EXISTS_TAC `N`
   ++ RW_TAC arith_ss []
   ++ RW_TAC std_ss [abs, SUM_POS]
   ++ Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`)
   ++ REAL_ARITH_TAC);

val SUMMABLE_LE = store_thm
  ("SUMMABLE_LE",
   ``!f x. summable f /\ (!n. sum (0, n) f <= x) ==> suminf f <= x``,
   Strip
   ++ Suff `0 < suminf f - x ==> F` >> REAL_ARITH_TAC
   ++ Strip
   ++ Know `(\n. sum (0, n) f) --> suminf f`
   >> RW_TAC std_ss [GSYM sums, SUMMABLE_SUM]
   ++ RW_TAC std_ss [SEQ]
   ++ Q.EXISTS_TAC `suminf f - x`
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `N`
   ++ Q.PAT_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   ++ RW_TAC real_ss []
   ++ ONCE_REWRITE_TAC [ABS_SUB]
   ++ Know `0 <= suminf f - sum (0, N) f`
   >> (!! (POP_ASSUM MP_TAC)
       ++ REAL_ARITH_TAC)
   ++ RW_TAC std_ss [abs]
   ++ !! (POP_ASSUM MP_TAC)
   ++ REAL_ARITH_TAC);

val SUMS_EQ = store_thm
  ("SUMS_EQ",
   ``!f x. f sums x = summable f /\ (suminf f = x)``,
   PROVE_TAC [SUM_SUMMABLE, SUM_UNIQ, summable]);

val SUMINF_POS = store_thm
  ("SUMINF_POS",
   ``!f. (!n. 0 <= f n) /\ summable f ==> 0 <= suminf f``,
   RW_TAC std_ss []
   ++ Know `0 = sum (0, 0) f` >> RW_TAC std_ss [sum]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ MATCH_MP_TAC SER_POS_LE
   ++ RW_TAC std_ss []);

 val SUM_PICK = store_thm
  ("SUM_PICK",
   ``!n k x. sum (0, n) (\m. if m = k then x else 0) = if k < n then x else 0``,
   Induct >> RW_TAC arith_ss [sum]
   ++ RW_TAC arith_ss [sum, REAL_ADD_RID, REAL_ADD_LID]
   ++ Suff `F` >> PROVE_TAC []
   ++ NTAC 2 (POP_ASSUM MP_TAC)
   ++ DECIDE_TAC);

val SUM_LT = store_thm
  ("SUM_LT",
   ``!f g m n.
       (!r. m <= r /\ r < n + m ==> f r < g r) /\ 0 < n ==>
       sum (m,n) f < sum (m,n) g``,
   RW_TAC std_ss []
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `n` >> RW_TAC arith_ss []
   ++ RW_TAC arith_ss []
   ++ Induct_on `n'` >> RW_TAC arith_ss [sum, REAL_ADD_LID]
   ++ ONCE_REWRITE_TAC [sum]
   ++ Strip
   ++ MATCH_MP_TAC REAL_LT_ADD2
   ++ CONJ_TAC
   >> (Q.PAT_ASSUM `a ==> b` MATCH_MP_TAC
       ++ RW_TAC arith_ss [])
   ++ RW_TAC arith_ss []);

val SUM_CONST = store_thm
  ("SUM_CONST",
   ``!n r. sum (0,n) (K r) = &n * r``,
   Induct >> RW_TAC real_ss [sum]
   ++ RW_TAC bool_ss [sum, ADD1, K_THM, GSYM REAL_ADD, REAL_ADD_RDISTRIB]
   ++ RW_TAC real_ss []);

val SUMINF_ADD = store_thm
  ("SUMINF_ADD",
   ``!f g.
       summable f /\ summable g ==>
       summable (\n. f n + g n) /\
       (suminf f + suminf g = suminf (\n. f n + g n))``,
   RW_TAC std_ss []
   ++ Know `f sums suminf f /\ g sums suminf g` >> PROVE_TAC [SUMMABLE_SUM]
   ++ STRIP_TAC
   ++ Know `(\n. f n + g n) sums (suminf f + suminf g)`
   >> RW_TAC std_ss [SER_ADD]
   ++ RW_TAC std_ss [SUMS_EQ]);

val SUMINF_2D = store_thm
  ("SUMINF_2D",
   ``!f g h.
       (!m n. 0 <= f m n) /\ (!n. f n sums g n) /\ summable g /\
       BIJ h UNIV (UNIV CROSS UNIV) ==>
       (UNCURRY f o h) sums suminf g``,
   RW_TAC std_ss []
   ++ RW_TAC std_ss [sums]
   ++ Know `g sums suminf g` >> PROVE_TAC [SUMMABLE_SUM]
   ++ Q.PAT_ASSUM `!n. P n` MP_TAC
   ++ RW_TAC std_ss [SUMS_EQ, FORALL_AND_THM]
   ++ MATCH_MP_TAC INCREASING_SEQ
   ++ CONJ_TAC
   >> (RW_TAC std_ss [sum, o_THM, ADD_CLAUSES]
       ++ Cases_on `h n`
       ++ RW_TAC std_ss [UNCURRY_DEF]
       ++ Q.PAT_ASSUM `!m n. 0 <= f m n` (MP_TAC o Q.SPECL [`q`, `r`])
       ++ REAL_ARITH_TAC)
   ++ Know `!m. 0 <= g m`
   >> (STRIP_TAC
       ++ Suff `0 <= suminf (f m)` >> PROVE_TAC []
       ++ MATCH_MP_TAC SER_POS
       ++ PROVE_TAC [])
   ++ STRIP_TAC
   ++ CONJ_TAC
   >> (RW_TAC std_ss []
       ++ MP_TAC (Q.SPECL [`h`, `n`] NUM_2D_BIJ_BIG_SQUARE)
       ++ ASM_REWRITE_TAC []
       ++ STRIP_TAC
       ++ MATCH_MP_TAC REAL_LE_TRANS
       ++ Q.EXISTS_TAC `sum (0,k) g`
       ++ REVERSE CONJ_TAC
       >> (MATCH_MP_TAC SER_POS_LE
           ++ PROVE_TAC [])
       ++ MATCH_MP_TAC REAL_LE_TRANS
       ++ Q.EXISTS_TAC `sum (0,k) (\m. sum (0,k) (f m))`
       ++ REVERSE CONJ_TAC
       >> (MATCH_MP_TAC SUM_LE
           ++ RW_TAC std_ss []
           ++ Q.PAT_ASSUM `!n. suminf (f n) = g n` (REWRITE_TAC o wrap o GSYM)
           ++ MATCH_MP_TAC SER_POS_LE
           ++ PROVE_TAC [])
       ++ Suff
          `!j.
             j <= n ==>
             (sum (0, j) (UNCURRY f o h) =
              sum (0, k)
              (\m. sum (0, k)
               (\n. if (?i. i < j /\ (h i = (m, n))) then f m n else 0)))`
       >> (DISCH_THEN (MP_TAC o Q.SPEC `n`)
           ++ REWRITE_TAC [LESS_EQ_REFL]
           ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
           ++ MATCH_MP_TAC SUM_LE
           ++ RW_TAC std_ss []
           ++ MATCH_MP_TAC SUM_LE
           ++ RW_TAC std_ss [REAL_LE_REFL])
       ++ Induct >> RW_TAC arith_ss [sum, SUM_0]
       ++ RW_TAC std_ss [sum]
       ++ Q.PAT_ASSUM `p ==> q` MP_TAC
       ++ RW_TAC arith_ss []
       ++ Know
          `!m n.
             (?i. i < SUC j /\ (h i = (m,n))) =
             (?i. i < j /\ (h i = (m,n))) \/ (h j = (m, n))`
       >> (RW_TAC std_ss []
           ++ Suff `!i. i < SUC j = i < j \/ (i = j)`
           >> PROVE_TAC []
           ++ DECIDE_TAC)
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ Know
          `!m n.
             (if (?i. i < j /\ (h i = (m,n))) \/ (h j = (m,n)) then f m n
              else 0) =
             (if (?i. i < j /\ (h i = (m,n))) then f m n else 0) +
             (if (h j = (m,n)) then f m n else 0)`
       >> (Strip
           ++ Suff `(?i. i < j /\ (h i = (m,n'))) ==> ~(h j = (m,n'))`
           >> PROVE_TAC [REAL_ADD_LID, REAL_ADD_RID]
           ++ RW_TAC std_ss []
           ++ Q.PAT_ASSUM `BIJ a b c` MP_TAC
           ++ RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV, IN_CROSS]
           ++ PROVE_TAC [prim_recTheory.LESS_REFL])
       ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
       ++ RW_TAC std_ss [SUM_ADD]
       ++ POP_ASSUM K_TAC
       ++ Suff
          `(UNCURRY f o h) j =
           sum (0,k)
           (\m. sum (0,k) (\n. (if h j = (m,n) then f m n else 0)))`
       >> (KILL_TAC
           ++ Q.SPEC_TAC
              (`(sum (0,k)
                 (\m.
                  sum (0,k)
                  (\n. if ?i. i < j /\ (h i = (m,n)) then f m n else 0)))`,
               `r1`)
           ++ Q.SPEC_TAC
              (`sum (0,k)
                (\m. sum (0,k) (\n. (if h j = (m,n) then f m n else 0)))`,
               `r2`)
           ++ RW_TAC std_ss [])
       ++ Cases_on `h j`
       ++ RW_TAC std_ss [o_THM, UNCURRY_DEF]
       ++ Know
          `!m n.
             (if (q = m) /\ (r = n) then f m n else 0) =
             (if (n = r) then if (m = q) then f m n else 0 else 0)`
       >> PROVE_TAC []
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ Q.PAT_ASSUM `a SUBSET b` MP_TAC
       ++ RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, IN_CROSS]
       ++ Suff `q < k /\ r < k`
       >> RW_TAC std_ss [SUM_PICK]
       ++ POP_ASSUM (MP_TAC o Q.SPEC `h (j:num)`)
       ++ Suff `j < n`
       >> (RW_TAC std_ss []
           ++ PROVE_TAC [])
       ++ DECIDE_TAC)
   ++ RW_TAC std_ss []
   ++ Know `?M. 0 < M /\ suminf g < sum (0, M) g + e / 2`
   >> (Know `g sums suminf g` >> PROVE_TAC [SUMMABLE_SUM]
       ++ RW_TAC std_ss [sums, SEQ]
       ++ POP_ASSUM (MP_TAC o Q.SPEC `e / 2`)
       ++ RW_TAC std_ss [REAL_LT_HALF1, GREATER_EQ]
       ++ POP_ASSUM (MP_TAC o Q.SPEC `SUC N`)
       ++ ONCE_REWRITE_TAC [ABS_SUB]
       ++ Know `sum (0, SUC N) g <= suminf g`
       >> (MATCH_MP_TAC SER_POS_LE
           ++ RW_TAC std_ss [])
       ++ REVERSE (RW_TAC arith_ss [abs])
       >> (Suff `F` >> PROVE_TAC []
           ++ POP_ASSUM K_TAC
           ++ POP_ASSUM MP_TAC
           ++ POP_ASSUM MP_TAC
           ++ REAL_ARITH_TAC)
       ++ Q.EXISTS_TAC `SUC N`
       ++ CONJ_TAC >> DECIDE_TAC
       ++ POP_ASSUM MP_TAC
       ++ REAL_ARITH_TAC)
   ++ RW_TAC std_ss []
   ++ Suff `?k. sum (0, M) g < sum (0, k) (UNCURRY f o h) + e / 2`
   >> (Strip
       ++ Q.EXISTS_TAC `k`
       ++ Know
          `sum (0, M) g + e / 2 < sum (0, k) (UNCURRY f o h) + (e / 2 + e / 2)`
       >> (POP_ASSUM MP_TAC
           ++ REAL_ARITH_TAC)
       ++ POP_ASSUM K_TAC
       ++ POP_ASSUM MP_TAC
       ++ REWRITE_TAC [REAL_HALF_DOUBLE]
       ++ REAL_ARITH_TAC)
   ++ POP_ASSUM K_TAC
   ++ Know `!m. ?N. g m < sum (0, N) (f m) + (e / 2) / & M`
   >> (Know `!m. f m sums g m`
       >> RW_TAC std_ss [SUMS_EQ]
       ++ RW_TAC std_ss [sums, SEQ]
       ++ POP_ASSUM (MP_TAC o Q.SPECL [`m`, `(e / 2) / & M`])
       ++ Know `0 < (e / 2) / & M`
       >> RW_TAC arith_ss [REAL_LT_DIV, REAL_NZ_IMP_LT]
       ++ DISCH_THEN (REWRITE_TAC o wrap)
       ++ RW_TAC std_ss [GREATER_EQ]
       ++ POP_ASSUM (MP_TAC o Q.SPEC `N`)
       ++ ONCE_REWRITE_TAC [ABS_SUB]
       ++ Know `sum (0, N) (f m) <= g m`
       >> (Q.PAT_ASSUM `!n. P n = Q n` (REWRITE_TAC o wrap o GSYM)
           ++ MATCH_MP_TAC SER_POS_LE
           ++ RW_TAC std_ss [])
       ++ REVERSE (RW_TAC arith_ss [abs])
       >> (POP_ASSUM K_TAC
           ++ Suff `F` >> PROVE_TAC []
           ++ NTAC 2 (POP_ASSUM MP_TAC)
           ++ REAL_ARITH_TAC)
       ++ Q.EXISTS_TAC `N`
       ++ POP_ASSUM MP_TAC
       ++ REAL_ARITH_TAC)
   ++ DISCH_THEN (MP_TAC o CONV_RULE SKOLEM_CONV)
   ++ RW_TAC std_ss []
   ++ Know `?c. M <= c /\ !m. m < M ==> N m <= c`
   >> (KILL_TAC
       ++ Induct_on `M` >> RW_TAC arith_ss []
       ++ Strip
       ++ Q.EXISTS_TAC `MAX (SUC c) (N M)`
       ++ RW_TAC arith_ss [X_LE_MAX, LT_SUC]
       ++ PROVE_TAC [LESS_EQ_REFL, LE])
   ++ Strip
   ++ MP_TAC (Q.SPECL [`h`, `c`] NUM_2D_BIJ_SMALL_SQUARE)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (Q.X_CHOOSE_TAC `k`)
   ++ Q.EXISTS_TAC `k`
   ++ MATCH_MP_TAC REAL_LTE_TRANS
   ++ Q.EXISTS_TAC `sum (0, M) (\m. sum (0, N m) (f m) + e / 2 / &M)`
   ++ CONJ_TAC
   >> (MATCH_MP_TAC SUM_LT
       ++ RW_TAC arith_ss [])
   ++ RW_TAC std_ss [SUM_ADD, GSYM K_PARTIAL, SUM_CONST]
   ++ Know `!x:real. & M * (x / & M) = x`
   >> (RW_TAC std_ss [real_div]
       ++ Suff `(& M * inv (& M)) * x = x`
       >> PROVE_TAC [REAL_MUL_ASSOC, REAL_MUL_SYM]
       ++ Suff `~(& M = 0:real)` >> RW_TAC std_ss [REAL_MUL_RINV, REAL_MUL_LID]
       ++ RW_TAC arith_ss [REAL_INJ])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [REAL_LE_RADD]
   ++ Suff
      `sum (0,M) (\m. sum (0,N m) (f m)) =
       sum (0, k)
       (\k.
          if ?m n. m < M /\ n < N m /\ (h k = (m, n)) then (UNCURRY f o h) k
          else 0)`
   >> (RW_TAC std_ss []
       ++ MATCH_MP_TAC SUM_LE
       ++ RW_TAC std_ss [o_THM, REAL_LE_REFL]
       ++ Cases_on `h r`
       ++ RW_TAC std_ss [UNCURRY_DEF])
   ++ NTAC 3 (POP_ASSUM MP_TAC)
   ++ Q.PAT_ASSUM `BIJ h a b` MP_TAC
   ++ KILL_TAC
   ++ RW_TAC std_ss []
   ++ Induct_on `M` >> RW_TAC arith_ss [sum, SUM_ZERO]
   ++ RW_TAC arith_ss [sum, LT_SUC]
   ++ Q.PAT_ASSUM `a ==> b` K_TAC
   ++ Know
      `!k'.
         (?m n. (m < M \/ (m = M)) /\ n < N m /\ (h k' = (m, n))) =
         (?m n. m < M /\ n < N m /\ (h k' = (m, n))) \/
         (?n. n < N M /\ (h k' = (M, n)))`
   >> PROVE_TAC []
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Know
      `!k'.
         (if (?m n. m < M /\ n < N m /\ (h k' = (m,n))) \/
             (?n. n < N M /\ (h k' = (M,n)))
          then UNCURRY f (h k')
          else 0) =
         (if (?m n. m < M /\ n < N m /\ (h k' = (m,n))) then UNCURRY f (h k')
          else 0) +
         (if (?n. n < N M /\ (h k' = (M,n))) then UNCURRY f (h k')
          else 0)`
   >> (STRIP_TAC
       ++ Suff
          `(?m n. m < M /\ n < N m /\ (h k' = (m,n))) ==>
           ~(?n. n < N M /\ (h k' = (M,n)))`
       >> PROVE_TAC [REAL_ADD_RID, REAL_ADD_LID]
       ++ Cases_on `h k'`
       ++ RW_TAC arith_ss [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [SUM_ADD, REAL_EQ_LADD]
   ++ Know `N M <= c` >> PROVE_TAC []
   ++ POP_ASSUM K_TAC
   ++ Q.SPEC_TAC (`N M`, `l`)
   ++ Induct >> RW_TAC real_ss [sum, SUM_0]
   ++ RW_TAC arith_ss [sum, LT_SUC]
   ++ Q.PAT_ASSUM `a ==> b` K_TAC
   ++ Know
      `!k'.
         (?n. (n < l \/ (n = l)) /\ (h k' = (M,n))) =
         (?n. n < l /\ (h k' = (M,n))) \/ (h k' = (M, l))`
   >> PROVE_TAC []
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ Know
      `!k'.
         (if (?n. n < l /\ (h k' = (M,n))) \/ (h k' = (M, l)) then
            UNCURRY f (h k')
          else 0) =
         (if (?n. n < l /\ (h k' = (M,n))) then UNCURRY f (h k') else 0) +
         (if (h k' = (M, l)) then UNCURRY f (h k') else 0)`
   >> (STRIP_TAC
       ++ Suff `(?n. n < l /\ (h k' = (M,n))) ==> ~(h k' = (M, l))`
       >> PROVE_TAC [REAL_ADD_LID, REAL_ADD_RID]
       ++ Cases_on `h k'`
       ++ RW_TAC arith_ss [])
   ++ DISCH_THEN (REWRITE_TAC o wrap)
   ++ RW_TAC std_ss [SUM_ADD, REAL_EQ_LADD]
   ++ Q.PAT_ASSUM `a SUBSET b` MP_TAC
   ++ RW_TAC std_ss [SUBSET_DEF, IN_CROSS, IN_COUNT, IN_IMAGE]
   ++ POP_ASSUM (MP_TAC o Q.SPEC `(M, l)`)
   ++ RW_TAC arith_ss []
   ++ Suff `!k'. (h k' = (M, l)) = (k' = x')`
   >> (RW_TAC std_ss [SUM_PICK, o_THM]
       ++ Q.PAT_ASSUM `(M,l) = a` (REWRITE_TAC o wrap o GSYM)
       ++ RW_TAC std_ss [UNCURRY_DEF])
   ++ Q.PAT_ASSUM `BIJ h a b` MP_TAC
   ++ RW_TAC std_ss [BIJ_DEF, INJ_DEF, IN_UNIV, IN_CROSS]
   ++ PROVE_TAC []);

val POW_HALF_SER = store_thm
  ("POW_HALF_SER",
   ``(\n. (1 / 2) pow (n + 1)) sums 1``,
   Know `(\n. (1 / 2) pow n) sums inv (1 - (1 / 2))`
   >> (MATCH_MP_TAC GP
       ++ RW_TAC std_ss [abs, HALF_POS, REAL_LT_IMP_LE, HALF_LT_1])
   ++ RW_TAC std_ss [ONE_MINUS_HALF, REAL_INV_INV, GSYM REAL_INV_1OVER,
                     GSYM ADD1, pow]
   ++ Know `1 = inv 2 * 2:real`
   >> RW_TAC arith_ss [REAL_MUL_LINV, REAL_INJ]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ HO_MATCH_MP_TAC SER_CMUL
   ++ RW_TAC std_ss []);

val SER_POS_COMPARE = store_thm
  ("SER_POS_COMPARE",
   ``!f g.
       (!n. 0 <= f n) /\ summable g /\ (!n. f n <= g n) ==>
       summable f /\ suminf f <= suminf g``,
   REVERSE (!! (STRONG_CONJ_TAC || STRIP_TAC))
   >> PROVE_TAC [SER_LE]
   ++ MATCH_MP_TAC SER_COMPAR
   ++ Q.EXISTS_TAC `g`
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `0`
   ++ RW_TAC arith_ss [abs]);


(************************************************************************************************)
(************************************************************************************************)

val minimal_def = Define
  `minimal p = @(n:num). p n /\ (!m. m < n ==> ~(p m))`;

val MINIMAL_EXISTS0 = store_thm
  ("MINIMAL_EXISTS0",
   ``(?(n:num). P n) = (?n. P n /\ (!m. m < n ==> ~(P m)))``,
   REVERSE EQ_TAC >> PROVE_TAC []
   ++ RW_TAC std_ss []
   ++ CCONTR_TAC
   ++ Suff `!n. ~P n` >> PROVE_TAC []
   ++ STRIP_TAC
   ++ completeInduct_on `n'`
   ++ PROVE_TAC []);

val MINIMAL_EXISTS = store_thm
  ("MINIMAL_EXISTS",
   ``!P. (?n. P n) = (P (minimal P) /\ !n. n < minimal P ==> ~P n)``,
   REWRITE_TAC [MINIMAL_EXISTS0, boolTheory.EXISTS_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [GSYM minimal_def]);

val _ = export_theory ();
