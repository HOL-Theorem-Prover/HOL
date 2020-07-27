(* ------------------------------------------------------------------------- *)
(* Borel Space and Borel-measurable functions                                *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013) [2]              *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble [3] (2010)                               *)
(* Cambridge University                                                      *)
(* ------------------------------------------------------------------------- *)
(* Updated by Chun Tian (2019-2020) using some materials from:               *)
(*                                                                           *)
(*        Lebesgue Measure Theory (lebesgue_measure_hvgScript.sml)           *)
(*                                                                           *)
(*        (c) Copyright 2015,                                                *)
(*                       Muhammad Qasim,                                     *)
(*                       Osman Hasan,                                        *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*            Contact:  <m_qasi@ece.concordia.ca>                            *)
(*                                                                           *)
(* Note: This theory is inspired by Isabelle/HOL                             *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory prim_recTheory numLib combinTheory optionTheory
     res_quanTheory res_quanTools pairTheory jrhUtils mesonLib
     pred_setTheory pred_setLib listTheory quotientTheory relationTheory
     rich_listTheory sortingTheory fcpTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory RealArith;

open hurdUtils util_probTheory extrealTheory sigma_algebraTheory
     real_borelTheory measureTheory real_topologyTheory integrationTheory;

val _ = new_theory "borel";

val ASM_ARITH_TAC = REPEAT (POP_ASSUM MP_TAC) >> ARITH_TAC; (* numLib *)
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove(tm, METIS_TAC ths);

val set_ss = std_ss ++ PRED_SET_ss;

(* ------------------------------------------------------------------------- *)
(*  Indicator functions                                                      *)
(* ------------------------------------------------------------------------- *)

(* `indicator_fn s` maps x to 0 or 1 when x IN or NOTIN s *)
Definition indicator_fn_def :
    ext_indicator_fn s = \x. if x IN s then (1 :extreal) else (0 :extreal)
End

val _ = overload_on ("indicator_fn", “ext_indicator_fn”);
val _ = Unicode.unicode_version {u = UTF8.chr 0x1D7D9, tmnm = "indicator_fn"};
val _ = TeX_notation {hol = UTF8.chr 0x1D7D9, TeX = ("\\HOLTokenOne{}", 1)};
val _ = TeX_notation {hol = "indicator_fn",   TeX = ("\\HOLTokenOne{}", 1)};

val _ = TeX_notation {hol = "indicator_fn",   TeX = ("\\HOLTokenOne{}", 1)};
val _ = TeX_notation {hol = UTF8.chr 0x1D7D9, TeX = ("\\HOLTokenOne{}", 1)};

val INDICATOR_FN_POS = store_thm
  ("INDICATOR_FN_POS", ``!s x. 0 <= indicator_fn s x``,
    RW_TAC std_ss [indicator_fn_def]
 >- RW_TAC real_ss [extreal_of_num_def, extreal_le_eq]
 >> REWRITE_TAC [le_refl]);

val INDICATOR_FN_LE_1 = store_thm
  ("INDICATOR_FN_LE_1", ``!s x. indicator_fn s x <= 1``,
    RW_TAC std_ss [indicator_fn_def, le_refl, le_01]);

val INDICATOR_FN_NOT_INFTY = store_thm (* new *)
  ("INDICATOR_FN_NOT_INFTY",
  ``!s x. indicator_fn s x <> NegInf /\ indicator_fn s x <> PosInf``,
    RW_TAC std_ss []
 >- (MATCH_MP_TAC pos_not_neginf >> REWRITE_TAC [INDICATOR_FN_POS])
 >> Cases_on `x IN s`
 >> ASM_SIMP_TAC std_ss [indicator_fn_def, extreal_of_num_def, extreal_not_infty]);

(* "advanced" lemmas/theorems should have lower-case names *)
Theorem indicator_fn_normal :
    !s x. ?r. (indicator_fn s x = Normal r) /\ 0 <= r /\ r <= 1
Proof
    rpt STRIP_TAC
 >> `?r. indicator_fn s x = Normal r`
       by METIS_TAC [extreal_cases, INDICATOR_FN_NOT_INFTY]
 >> Q.EXISTS_TAC `r` >> art []
 >> METIS_TAC [INDICATOR_FN_POS, INDICATOR_FN_LE_1, extreal_le_eq,
               extreal_of_num_def]
QED

val INDICATOR_FN_SING_1 = store_thm
  ("INDICATOR_FN_SING_1", ``!x y. (x = y) ==> (indicator_fn {x} y = 1)``,
    RW_TAC std_ss [indicator_fn_def, IN_SING]);

val INDICATOR_FN_SING_0 = store_thm
  ("INDICATOR_FN_SING_0", ``!x y. x <> y ==> (indicator_fn {x} y = 0)``,
    RW_TAC std_ss [indicator_fn_def, IN_SING]);

Theorem INDICATOR_FN_EMPTY[simp] :
    !x. indicator_fn {} x = 0
Proof
    RW_TAC std_ss [indicator_fn_def, NOT_IN_EMPTY]
QED

(* Properties of the indicator function [1, p.14] *)
val INDICATOR_FN_INTER = store_thm (* new *)
  ("INDICATOR_FN_INTER",
  ``!A B. indicator_fn (A INTER B) = (\t. (indicator_fn A t) * (indicator_fn B t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> RW_TAC std_ss [indicator_fn_def, mul_lone, IN_INTER, mul_lzero]
 >> FULL_SIMP_TAC std_ss []);

val INDICATOR_FN_MUL_INTER = store_thm
  ("INDICATOR_FN_MUL_INTER",
  ``!A B. (\t. (indicator_fn A t) * (indicator_fn B t)) = (\t. indicator_fn (A INTER B) t)``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
       by METIS_TAC [indicator_fn_def]
 >> RW_TAC std_ss [indicator_fn_def, mul_lone, IN_INTER, mul_lzero]
 >> FULL_SIMP_TAC real_ss []);

val INDICATOR_FN_INTER_MIN = store_thm (* new *)
  ("INDICATOR_FN_INTER_MIN",
  ``!A B. indicator_fn (A INTER B) = (\t. min (indicator_fn A t) (indicator_fn B t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_of_num_def, extreal_min_def, extreal_le_eq]);

val INDICATOR_FN_DIFF = store_thm (* new *)
  ("INDICATOR_FN_DIFF",
  ``!A B. indicator_fn (A DIFF B) = (\t. indicator_fn A t - indicator_fn (A INTER B) t)``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A DIFF B) t = if t IN (A DIFF B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_DIFF, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [sub_rzero]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC sub_refl
 >> PROVE_TAC [extreal_of_num_def, extreal_not_infty]);

val INDICATOR_FN_DIFF_SPACE = store_thm (* new *)
  ("INDICATOR_FN_DIFF_SPACE",
  ``!A B sp. A SUBSET sp /\ B SUBSET sp ==>
            (indicator_fn (A INTER (sp DIFF B)) =
             (\t. indicator_fn A t - indicator_fn (A INTER B) t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A DIFF B) t = if t IN (A DIFF B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_DIFF, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [SUBSET_DEF, sub_rzero]
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC sub_refl
 >> PROVE_TAC [extreal_of_num_def, extreal_not_infty]);

val INDICATOR_FN_UNION_MAX = store_thm (* new *)
  ("INDICATOR_FN_UNION_MAX",
  ``!A B. indicator_fn (A UNION B) = (\t. max (indicator_fn A t) (indicator_fn B t))``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_max_def, extreal_le_eq, extreal_of_num_def]);

val INDICATOR_FN_UNION_MIN = store_thm (* new *)
  ("INDICATOR_FN_UNION_MIN",
  ``!A B. indicator_fn (A UNION B) = (\t. min (indicator_fn A t + indicator_fn B t) 1)``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION]
 >> Cases_on `t IN A` >> Cases_on `t IN B`
 >> fs [extreal_max_def, extreal_add_def, extreal_of_num_def, extreal_min_def, extreal_le_eq]);

val INDICATOR_FN_UNION = store_thm (* new *)
  ("INDICATOR_FN_UNION",
  ``!A B. indicator_fn (A UNION B) =
          (\t. indicator_fn A t + indicator_fn B t - indicator_fn (A INTER B) t)``,
    RW_TAC std_ss [FUN_EQ_THM]
 >> `indicator_fn (A INTER B) t = if t IN (A INTER B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> `indicator_fn (A UNION B) t = if t IN (A UNION B) then 1 else 0`
      by METIS_TAC [indicator_fn_def]
 >> fs [indicator_fn_def, IN_UNION, IN_INTER]
 >> Cases_on `t IN A` >> Cases_on `t IN B` >> fs [add_lzero, add_rzero, mul_rzero, sub_rzero]
 >> fs [extreal_add_def, extreal_sub_def, extreal_of_num_def]);

Theorem INDICATOR_FN_MONO :
    !s t x. s SUBSET t ==> indicator_fn s x <= indicator_fn t x
Proof
    rpt STRIP_TAC
 >> Cases_on ‘x IN s’
 >- (‘x IN t’ by PROVE_TAC [SUBSET_DEF] \\
     rw [indicator_fn_def, le_refl])
 >> ‘indicator_fn s x = 0’ by METIS_TAC [indicator_fn_def] >> POP_ORW
 >> REWRITE_TAC [INDICATOR_FN_POS]
QED

Theorem INDICATOR_FN_CROSS :
    !s t x y. indicator_fn (s CROSS t) (x,y) = indicator_fn s x *
                                               indicator_fn t y
Proof
    rw [indicator_fn_def]
 >> PROVE_TAC []
QED

Theorem INDICATOR_FN_FCP_CROSS :
    !(s :'a['b] set) (t :'a['c] set) x y.
        FINITE univ(:'b) /\ FINITE univ(:'c) ==>
       (indicator_fn (fcp_cross s t) (FCP_CONCAT x y) =
        indicator_fn s x * indicator_fn t y)
Proof
    rpt STRIP_TAC
 >> rw [IN_FCP_CROSS, indicator_fn_def] (* 4 subgoals *)
 >> METIS_TAC [FCP_CONCAT_11]
QED

Theorem indicator_fn_general_cross :
    !(cons :'a -> 'b -> 'c) car cdr (s :'a set) (t :'b set) x y.
        pair_operation cons car cdr ==>
       (indicator_fn (general_cross cons s t) (cons x y) =
        indicator_fn s x * indicator_fn t y)
Proof
    rpt STRIP_TAC
 >> rw [IN_general_cross, indicator_fn_def] (* 4 subgoals *)
 >> METIS_TAC [pair_operation_def]
QED

val indicator_fn_split = store_thm
  ("indicator_fn_split",
  ``!(r:num->bool) s (b:num->('a->bool)).
       FINITE r /\ (BIGUNION (IMAGE b r) = s) /\
       (!i j. i IN r /\ j IN r /\ i <> j ==> DISJOINT (b i) (b j)) ==>
       !a. a SUBSET s ==>
          (indicator_fn a = (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))``,
 (* proof *)
    Suff `!r. FINITE r ==>
            (\r. !s (b:num->('a->bool)).
             FINITE r /\
             (BIGUNION (IMAGE b r) = s) /\
             (!i j. i IN r /\ j IN r /\ i <> j ==> DISJOINT (b i) (b j)) ==>
             !a. a SUBSET s ==>
                 ((indicator_fn a) =
                  (\x. SIGMA (\i. indicator_fn (a INTER (b i)) x) r))) r`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY,
                   SUBSET_EMPTY, indicator_fn_def, NOT_IN_EMPTY,
                   FINITE_INSERT, IMAGE_INSERT, DELETE_NON_ELEMENT,
                   IN_INSERT, BIGUNION_INSERT]
 >> Q.PAT_X_ASSUM `!b. P ==> !a. Q ==> (x = y)`
      (MP_TAC o Q.ISPEC `(b :num -> 'a -> bool)`)
 >> RW_TAC std_ss [SUBSET_DEF]
 >> POP_ASSUM (MP_TAC o Q.ISPEC `a DIFF ((b :num -> 'a -> bool) e)`)
 >> Know `(!x. x IN a DIFF b e ==> x IN BIGUNION (IMAGE b s))`
 >- METIS_TAC [SUBSET_DEF, IN_UNION, IN_DIFF]
 >> RW_TAC std_ss [FUN_EQ_THM]
 >> `!i. i IN e INSERT s ==> (\i. if x IN a INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def, extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY]
 >> Know `SIGMA (\i. (if x IN a INTER b i then 1 else 0)) s =
          SIGMA (\i. (if x IN (a DIFF b e) INTER b i then 1 else 0)) s`
 >- (`!i. i IN s ==> (\i. if x IN a INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def,extreal_not_infty] \\
     `!i. i IN s ==> (\i. if x IN (a DIFF b e) INTER b i then 1 else 0) i <> NegInf`
      by METIS_TAC [extreal_of_num_def,extreal_not_infty] \\
     FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool)`)
                               EXTREAL_SUM_IMAGE_IN_IF] \\
     FULL_SIMP_TAC std_ss [(Q.SPEC `(\i. if x IN (a DIFF b e) INTER b i then 1 else 0)`
                            o UNDISCH o Q.ISPEC `(s :num -> bool)`)
                               EXTREAL_SUM_IMAGE_IN_IF] \\
     MATCH_MP_TAC (METIS_PROVE [] ``!f x y z. (x = y) ==> (f x z = f y z)``) \\
     RW_TAC std_ss [FUN_EQ_THM, IN_INTER, IN_DIFF] \\
     FULL_SIMP_TAC real_ss [GSYM DELETE_NON_ELEMENT, DISJOINT_DEF, IN_INTER,
                            NOT_IN_EMPTY, EXTENSION, GSPECIFICATION] \\
     RW_TAC real_ss [extreal_of_num_def] >> METIS_TAC []) >> STRIP_TAC
 >> `SIGMA (\i. if x IN a INTER b i then 1 else 0) s = (if x IN a DIFF b e then 1 else 0)`
      by METIS_TAC []
 >> POP_ORW
 >> RW_TAC real_ss [IN_INTER, IN_DIFF, EXTREAL_SUM_IMAGE_ZERO, add_rzero, add_lzero]
 >> FULL_SIMP_TAC std_ss []
 >> `x IN BIGUNION (IMAGE b s)` by METIS_TAC [SUBSET_DEF,IN_UNION]
 >> FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE]
 >> `s = {x'} UNION (s DIFF {x'})` by METIS_TAC [UNION_DIFF, SUBSET_DEF, IN_SING]
 >> POP_ORW
 >> `FINITE {x'} /\ FINITE (s DIFF {x'})` by METIS_TAC [FINITE_SING, FINITE_DIFF]
 >> `DISJOINT {x'} (s DIFF {x'})` by METIS_TAC [EXTENSION, IN_DISJOINT, IN_DIFF, IN_SING]
 >> `!i. (\i. if x IN b i then 1 else 0) i <> NegInf`
       by METIS_TAC [extreal_of_num_def,extreal_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_DISJOINT_UNION]
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_SING]
 >> Suff `SIGMA (\i. if x IN b i then 1 else 0) (s DIFF {x'}) = 0`
 >- METIS_TAC [add_rzero]
 >> FULL_SIMP_TAC std_ss [(Once o UNDISCH o Q.ISPEC `(s :num -> bool) DIFF {x'}`)
                              EXTREAL_SUM_IMAGE_IN_IF]
 >> Suff `(\i. if i IN s DIFF {x'} then if x IN b i then 1 else 0 else 0) = (\x. 0)`
 >- RW_TAC std_ss [EXTREAL_SUM_IMAGE_ZERO]
 >> RW_TAC std_ss [FUN_EQ_THM, IN_DIFF, IN_SING]
 >> METIS_TAC [IN_SING, IN_DIFF, IN_DISJOINT]);

Theorem indicator_fn_suminf :
    !a x. (!m n. m <> n ==> DISJOINT (a m) (a n)) ==>
          (suminf (\i. indicator_fn (a i) x) = indicator_fn (BIGUNION (IMAGE a univ(:num))) x)
Proof
    rpt STRIP_TAC
 >> Know `!n. 0 <= (\i. indicator_fn (a i) x) n`
 >- RW_TAC std_ss [INDICATOR_FN_POS]
 >> DISCH_THEN (MP_TAC o (MATCH_MP ext_suminf_def)) >> Rewr'
 >> RW_TAC std_ss [sup_eq', IN_UNIV, IN_IMAGE]
 >- (Cases_on `~(x IN BIGUNION (IMAGE a univ(:num)))`
     >- (FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV] \\
         RW_TAC std_ss [indicator_fn_def, EXTREAL_SUM_IMAGE_ZERO, FINITE_COUNT, le_refl, le_01]) \\
     FULL_SIMP_TAC std_ss [IN_BIGUNION_IMAGE, IN_UNIV, indicator_fn_def] \\
     reverse (RW_TAC std_ss []) >- METIS_TAC [] \\
    `!n. n <> x' ==> ~(x IN a n)` by METIS_TAC [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] \\
     Cases_on `~(x' IN count n)`
     >- (`SIGMA (\i. if x IN a i then 1 else 0) (count n) = 0`
            by (MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 \\
                RW_TAC real_ss [FINITE_COUNT] >> METIS_TAC []) \\
         RW_TAC std_ss [le_01]) \\
    `count n = ((count n) DELETE x') UNION {x'}`
        by (RW_TAC std_ss [EXTENSION, IN_DELETE, IN_UNION, IN_SING, IN_COUNT] \\
            METIS_TAC []) >> POP_ORW \\
    `DISJOINT ((count n) DELETE x') ({x'})`
        by RW_TAC std_ss [DISJOINT_DEF, EXTENSION,IN_INTER, NOT_IN_EMPTY, IN_SING, IN_DELETE] \\
    `!n. (\i. if x IN a i then 1 else 0) n <> NegInf` by RW_TAC std_ss [num_not_infty] \\
     FULL_SIMP_TAC std_ss [FINITE_COUNT, FINITE_DELETE, FINITE_SING,
                           EXTREAL_SUM_IMAGE_DISJOINT_UNION, EXTREAL_SUM_IMAGE_SING] \\
     Suff `SIGMA (\i. if x IN a i then 1 else 0) (count n DELETE x') = 0`
     >- RW_TAC std_ss [add_lzero, le_refl] \\
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 \\
     RW_TAC std_ss [FINITE_COUNT, FINITE_DELETE] \\
     METIS_TAC [IN_DELETE])
 >> Know `!n. SIGMA (\i. indicator_fn (a i) x) (count n) <= y`
 >- (RW_TAC std_ss [] >> POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `n` >> REWRITE_TAC []) >> DISCH_TAC
 >> reverse (RW_TAC std_ss [indicator_fn_def, IN_BIGUNION_IMAGE, IN_UNIV])
 >- (`0 <= SIGMA (\i. indicator_fn (a i) x) (count 0)`
        by RW_TAC std_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY, le_refl] \\
     METIS_TAC [le_trans])
 >> rename1 `x IN a x''`
 >> Suff `SIGMA (\i. indicator_fn (a i) x) (count (SUC x'')) = 1`
 >- METIS_TAC []
 >> `!i. (\i. indicator_fn (a i) x) i <> NegInf`
        by RW_TAC std_ss [indicator_fn_def, num_not_infty]
 >> FULL_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_PROPERTY, FINITE_COUNT, COUNT_SUC]
 >> Suff `SIGMA (\i. indicator_fn (a i) x) (count x'' DELETE x'') = 0`
 >- RW_TAC std_ss [indicator_fn_def, add_rzero]
 >> `!n. n <> x'' ==> ~(x IN a n)` by METIS_TAC [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
 >> MATCH_MP_TAC EXTREAL_SUM_IMAGE_0
 >> FULL_SIMP_TAC std_ss [FINITE_COUNT, FINITE_DELETE, IN_COUNT, IN_DELETE, indicator_fn_def]
QED

Theorem INDICATOR_FN_ABS[simp] :
    !s. abs o (indicator_fn s) = indicator_fn s
Proof
    GEN_TAC >> FUN_EQ_TAC
 >> RW_TAC std_ss [o_DEF]
 >> REWRITE_TAC [abs_refl, INDICATOR_FN_POS]
QED

Theorem INDICATOR_FN_ABS_MUL :
    !f s. abs o (\x. f x * indicator_fn s x) = (\x. (abs o f) x * indicator_fn s x)
Proof
    RW_TAC std_ss [o_DEF, abs_mul]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss []
 >> Suff `abs (indicator_fn s x) = indicator_fn s x` >- rw []
 >> rw [abs_refl, INDICATOR_FN_POS]
QED

(* ------------------------------------------------------------------------- *)
(*  Positive and negative parts of functions                                 *)
(* ------------------------------------------------------------------------- *)

val fn_plus_def = Define (* f^+ *)
   `fn_plus (f :'a -> extreal) = (\x. if 0 < f x then f x else 0)`;

val _ = overload_on ("TC", ``fn_plus``); (* relationTheory *)

val fn_minus_def = Define (* f^- *)
   `fn_minus (f :'a -> extreal) = (\x. if f x < 0 then ~(f x) else 0)`;

val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT,0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^-"],
                   term_name = "fn_minus"};

val _ = Unicode.unicode_version {u = Unicode.UChar.sup_minus, tmnm = "fn_minus"};
val _ = TeX_notation {hol = Unicode.UChar.sup_minus,
                      TeX = ("\\HOLTokenSupMinus{}", 1)};
val _ = TeX_notation {hol = "^-", TeX = ("\\HOLTokenSupMinus{}", 1)};

(* alternative definitions of fn_plus and fn_minus using max/min *)
val FN_PLUS_ALT = store_thm
  ("FN_PLUS_ALT", ``!f. fn_plus f = (\x. max (f x) 0)``,
    RW_TAC std_ss [fn_plus_def, extreal_max_def]
 >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC
 >> Cases_on `0 < f x`
 >- (`~(f x <= 0)` by PROVE_TAC [let_antisym] >> fs [])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> fs []);

(* !f. fn_plus f = (\x. max 0 (f x)) *)
Theorem FN_PLUS_ALT' = ONCE_REWRITE_RULE [max_comm] FN_PLUS_ALT;

Theorem fn_plus : (* original definition *)
    !f x. fn_plus f x = max 0 (f x)
Proof
    RW_TAC std_ss [FN_PLUS_ALT']
QED

val FN_MINUS_ALT = store_thm
  ("FN_MINUS_ALT", ``!f. fn_minus f = (\x. -min (f x) 0)``,
    RW_TAC std_ss [fn_minus_def, extreal_min_def]
 >> FUN_EQ_TAC >> GEN_TAC >> BETA_TAC
 >> Cases_on `f x < 0`
 >- (`f x <= 0` by PROVE_TAC [lt_imp_le] >> fs [])
 >> fs []
 >> `0 <= f x` by PROVE_TAC [extreal_lt_def]
 >> Cases_on `f x <= 0`
 >- (`f x = 0` by PROVE_TAC [le_antisym] >> fs [neg_0])
 >> fs [neg_0]);

(* |- !f. fn_minus f = (\x. -min 0 (f x)) *)
Theorem FN_MINUS_ALT' = ONCE_REWRITE_RULE [min_comm] FN_MINUS_ALT;

Theorem fn_minus : (* original definition *)
    !f x. fn_minus f x = -min 0 (f x)
Proof
    RW_TAC std_ss [FN_MINUS_ALT']
QED

val FN_DECOMP = store_thm (* new *)
  ("FN_DECOMP", ``!f x. f x = fn_plus f x - fn_minus f x``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def]
 >- METIS_TAC [lt_antisym]
 >- REWRITE_TAC [sub_rzero]
 >- (`0 - -f x = 0 + f x` by METIS_TAC [sub_rneg, extreal_of_num_def] \\
     POP_ORW >> REWRITE_TAC [add_lzero])
 >> REWRITE_TAC [sub_rzero]
 >> METIS_TAC [extreal_lt_def, le_antisym]);

val FN_DECOMP' = store_thm (* new *)
  ("FN_DECOMP'", ``!f. f = (\x. fn_plus f x - fn_minus f x)``,
    METIS_TAC [FN_DECOMP]);

(* `fn_plus f x + fn_minus f x` is always defined (same reason as above) *)
val FN_ABS = store_thm (* new *)
  ("FN_ABS", ``!f x. (abs o f) x = fn_plus f x + fn_minus f x``,
 (* proof *)
    RW_TAC std_ss [o_DEF, fn_plus_def, fn_minus_def, add_rzero, add_lzero]
 >> Q.ABBREV_TAC `e = f x` (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      METIS_TAC [lt_antisym],
      (* goal 2 (of 4) *)
      Cases_on `e` >- METIS_TAC [extreal_of_num_def, lt_infty]
      >- REWRITE_TAC [extreal_abs_def] \\
      REWRITE_TAC [extreal_abs_def, extreal_11] \\
     `0 <= r` by METIS_TAC [extreal_of_num_def, extreal_lt_eq, REAL_LT_IMP_LE] \\
      METIS_TAC [abs],
      (* goal 3 (of 4) *)
      Cases_on `e` >- REWRITE_TAC [extreal_abs_def, extreal_ainv_def]
      >- METIS_TAC [extreal_of_num_def, lt_infty] \\
      REWRITE_TAC [extreal_abs_def, extreal_ainv_def, extreal_11] \\
     `r < 0` by METIS_TAC [extreal_of_num_def, extreal_lt_eq] \\
      METIS_TAC [real_lte, abs],
      (* goal 4 (of 4) *)
     `e = 0` by METIS_TAC [extreal_lt_def, le_antisym] \\
      PROVE_TAC [abs_0] ]);

val FN_ABS' = store_thm (* new *)
  ("FN_ABS'", ``!f. (abs o f) = (\x. fn_plus f x + fn_minus f x)``,
    METIS_TAC [FN_ABS]);

val FN_PLUS_POS = store_thm
  ("FN_PLUS_POS", ``!g x. 0 <= (fn_plus g) x``,
  RW_TAC real_ss [fn_plus_def, FUN_EQ_THM, lt_imp_le, le_refl]);

val FN_MINUS_POS = store_thm
  ("FN_MINUS_POS", ``!g x. 0 <= (fn_minus g) x``,
  RW_TAC real_ss [fn_minus_def, FUN_EQ_THM, le_refl]
  >> METIS_TAC [le_neg, lt_imp_le, neg_0]);

val FN_PLUS_POS_ID = store_thm
  ("FN_PLUS_POS_ID", ``!g. (!x. 0 <= g x) ==> ((fn_plus g) = g)``,
  RW_TAC real_ss [fn_plus_def,FUN_EQ_THM]
  >> Cases_on `g x = 0` >- METIS_TAC []
  >> METIS_TAC [le_lt]);

Theorem FN_PLUS_REDUCE[simp] :
    !f x. 0 <= f x ==> (fn_plus f x = f x)
Proof
    RW_TAC std_ss [fn_plus_def]
 >> METIS_TAC [le_lt]
QED

Theorem FN_MINUS_REDUCE[simp] :
    !f x. 0 <= f x ==> (fn_minus f x = 0)
Proof
    RW_TAC std_ss [fn_minus_def]
 >> PROVE_TAC [let_antisym]
QED

(* don't put it into simp sets, ‘o’ may be eliminated *)
Theorem FN_PLUS_ABS_SELF :
    !f. fn_plus (abs o f) = abs o f
Proof
    RW_TAC bool_ss [FUN_EQ_THM]
 >> MATCH_MP_TAC FN_PLUS_REDUCE
 >> RW_TAC std_ss [o_DEF, abs_pos]
QED

(* don't put it into simp sets, ‘o’ may be eliminated *)
Theorem FN_MINUS_ABS_ZERO :
    !f. fn_minus (abs o f) = \x. 0
Proof
    RW_TAC bool_ss [FUN_EQ_THM]
 >> MATCH_MP_TAC FN_MINUS_REDUCE
 >> RW_TAC std_ss [o_DEF, abs_pos]
QED

val FN_PLUS_NEG_ZERO = store_thm
  ("FN_PLUS_NEG_ZERO",
  ``!g. (!x. g x <= 0) ==> (fn_plus g = (\x. 0))``,
    RW_TAC real_ss [fn_plus_def, FUN_EQ_THM]
 >> `~(0 < g x)` by PROVE_TAC [extreal_lt_def]
 >> fs []);

val FN_MINUS_POS_ZERO = store_thm
  ("FN_MINUS_POS_ZERO",
  ``!g. (!x. 0 <= g x) ==> (fn_minus g = (\x. 0))``,
    RW_TAC real_ss [fn_minus_def, FUN_EQ_THM]
 >> Cases_on `g x = 0` >- METIS_TAC [neg_0]
 >> `0 < g x` by METIS_TAC [lt_le]
 >> METIS_TAC [extreal_lt_def]);

Theorem FN_PLUS_ZERO[simp] :
    fn_plus (\x. 0) = (\x. 0)
Proof
    MATCH_MP_TAC FN_PLUS_NEG_ZERO
 >> RW_TAC std_ss [le_refl]
QED

Theorem FN_MINUS_ZERO[simp] :
    fn_minus (\x. 0) = (\x. 0)
Proof
    MATCH_MP_TAC FN_MINUS_POS_ZERO
 >> RW_TAC std_ss [le_refl]
QED

val FN_MINUS_TO_PLUS = store_thm
  ("FN_MINUS_TO_PLUS", ``!f. fn_minus (\x. -(f x)) = fn_plus f``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def, neg_neg]
 >> `!x. -f x < 0 <=> 0 < f x` by PROVE_TAC [neg_0, lt_neg]
 >> POP_ORW >> REWRITE_TAC []);

val FN_PLUS_TO_MINUS = store_thm
  ("FN_PLUS_TO_MINUS", ``!f. fn_plus (\x. -(f x)) = fn_minus f``,
    RW_TAC std_ss [fn_plus_def, fn_minus_def, neg_neg]
 >> `!x. 0 < -f x <=> f x < 0` by PROVE_TAC [neg_0, lt_neg]
 >> POP_ORW >> REWRITE_TAC []);

val FN_PLUS_NOT_INFTY = store_thm
  ("FN_PLUS_NOT_INFTY", ``!f. (!x. f x <> PosInf) ==> !x. fn_plus f x <> PosInf``,
    RW_TAC std_ss [fn_plus_def]
 >> Cases_on `0 < f x` >- PROVE_TAC []
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]);

Theorem FN_PLUS_NOT_INFTY' :
    !f x. f x <> PosInf ==> fn_plus f x <> PosInf
Proof
    RW_TAC std_ss [fn_plus_def]
 >> Cases_on `0 < f x` >- PROVE_TAC []
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]
QED

val FN_MINUS_NOT_INFTY = store_thm
  ("FN_MINUS_NOT_INFTY", ``!f. (!x. f x <> NegInf) ==> !x. fn_minus f x <> PosInf``,
    RW_TAC std_ss [fn_minus_def]
 >> Cases_on `f x < 0`
 >- PROVE_TAC [extreal_ainv_def, neg_neg]
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]);

Theorem FN_MINUS_NOT_INFTY' :
    !f x. f x <> NegInf ==> fn_minus f x <> PosInf
Proof
    RW_TAC std_ss [fn_minus_def]
 >> Cases_on `f x < 0`
 >- PROVE_TAC [extreal_ainv_def, neg_neg]
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]
QED

val FN_PLUS_CMUL = store_thm
  ("FN_PLUS_CMUL",
  ``!f c. (0 <= c ==> (fn_plus (\x. Normal c * f x) = (\x. Normal c * fn_plus f x))) /\
          (c <= 0 ==> (fn_plus (\x. Normal c * f x) = (\x. -Normal c * fn_minus f x)))``,
    RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
 >- (Cases_on `0 < f x`
     >- METIS_TAC [let_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, le_antisym]
     >> RW_TAC std_ss [mul_rzero]
     >> METIS_TAC [mul_le, extreal_lt_def, extreal_le_def, extreal_of_num_def, lt_imp_le,
                   le_antisym])
 >> RW_TAC std_ss [mul_rzero, neg_mul2]
 >- METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
               le_antisym, mul_comm]
 >> METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
               le_antisym]);

val FN_PLUS_CMUL_full = store_thm
  ("FN_PLUS_CMUL_full",
  ``!f c. (0 <= c ==> (fn_plus (\x. c * f x) = (\x. c * fn_plus f x))) /\
          (c <= 0 ==> (fn_plus (\x. c * f x) = (\x. -c * fn_minus f x)))``,
    rpt GEN_TAC
 >> Cases_on `c`
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_plus_def, fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [neg_mul2],
       (* goal 2 (of 4) *)
      `0 <= f x` by PROVE_TAC [extreal_lt_def] \\
      `NegInf <= 0` by PROVE_TAC [le_infty] \\
      `NegInf * f x <= 0` by PROVE_TAC [mul_le2] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `NegInf < 0` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `0 < NegInf * f x` by PROVE_TAC [lt_mul_neg],
       (* goal 4 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_plus_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
      `f x <= 0` by PROVE_TAC [extreal_lt_def] \\
       fs [le_lt] \\
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `PosInf * f x < 0` by PROVE_TAC [mul_lt] \\
       PROVE_TAC [lt_antisym],
       (* goal 2 (of 3) *)
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `0 < PosInf * f x` by PROVE_TAC [lt_mul],
       (* goal 3 (of 3) *)
       REWRITE_TAC [mul_rzero] ])
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `0 <= r` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_PLUS_CMUL],
      (* goal 2 (of 2) *)
     `r <= 0` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_PLUS_CMUL] ]);

val FN_MINUS_CMUL = store_thm
  ("FN_MINUS_CMUL",
  ``!f c. (0 <= c ==> (fn_minus (\x. Normal c * f x) = (\x. Normal c * fn_minus f x))) /\
          (c <= 0 ==> (fn_minus (\x. Normal c * f x) = (\x. -Normal c * fn_plus f x)))``,
    RW_TAC std_ss [fn_plus_def,fn_minus_def,FUN_EQ_THM]
 >- (RW_TAC std_ss [mul_rzero, mul_rneg, neg_eq0]
     >- METIS_TAC [le_mul, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
                   le_antisym]
     >> METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
                   le_antisym, neg_eq0])
 >> RW_TAC std_ss [mul_rzero, neg_eq0, mul_lneg, neg_0]
 >- METIS_TAC [le_mul_neg, extreal_of_num_def, extreal_le_def, extreal_lt_def, lt_imp_le,
               le_antisym]
 >> METIS_TAC [mul_le, extreal_of_num_def, extreal_le_def, lt_imp_le, extreal_lt_def,
               le_antisym, neg_eq0, mul_comm]);

val FN_MINUS_CMUL_full = store_thm
  ("FN_MINUS_CMUL_full",
  ``!f c. (0 <= c ==> (fn_minus (\x. c * f x) = (\x. c * fn_minus f x))) /\
          (c <= 0 ==> (fn_minus (\x. c * f x) = (\x. -c * fn_plus f x)))``,
    rpt GEN_TAC
 >> Cases_on `c`
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_plus_def, fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [GSYM mul_lneg],
       (* goal 2 (of 4) *)
      `f x <= 0` by PROVE_TAC [extreal_lt_def] \\
      `NegInf <= 0` by PROVE_TAC [le_infty] \\
      `0 <= NegInf * f x` by PROVE_TAC [le_mul_neg] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `NegInf < 0` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `NegInf * f x < 0` by PROVE_TAC [mul_lt2],
       (* goal 4 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >- (SIMP_TAC std_ss [le_infty, extreal_not_infty, extreal_of_num_def] \\
     FUN_EQ_TAC >> RW_TAC std_ss [fn_minus_def] >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       REWRITE_TAC [GSYM mul_rneg],
       (* goal 2 (of 4) *)
      `0 <= f x` by PROVE_TAC [extreal_lt_def] \\
      `0 <= PosInf` by PROVE_TAC [le_infty] \\
      `0 <= PosInf * f x` by PROVE_TAC [le_mul] \\
       PROVE_TAC [let_antisym],
       (* goal 3 (of 4) *)
      `0 < PosInf` by PROVE_TAC [lt_infty, extreal_of_num_def] \\
      `PosInf * f x < 0` by PROVE_TAC [mul_lt],
       (* goal 3 (of 4) *)
       REWRITE_TAC [mul_rzero] ])
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `0 <= r` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_MINUS_CMUL],
      (* goal 2 (of 2) *)
     `r <= 0` by PROVE_TAC [extreal_le_eq, extreal_of_num_def] \\
      METIS_TAC [FN_MINUS_CMUL] ]);

val FN_PLUS_FMUL = store_thm
  ("FN_PLUS_FMUL",
  ``!f c. (!x. 0 <= c x) ==> (fn_plus (\x. c x * f x) = (\x. c x * fn_plus f x))``,
    RW_TAC std_ss [fn_plus_def, FUN_EQ_THM]
 >> Cases_on `0 < f x`
 >- (`0 <= c x * f x` by PROVE_TAC [let_mul] \\
     fs [le_lt])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> `c x * f x <= 0` by PROVE_TAC [mul_le]
 >> `~(0 < c x * f x)` by PROVE_TAC [extreal_lt_def]
 >> fs [mul_rzero]);

val FN_MINUS_FMUL = store_thm
  ("FN_MINUS_FMUL",
  ``!f c. (!x. 0 <= c x) ==> (fn_minus (\x. c x * f x) = (\x. c x * fn_minus f x))``,
    RW_TAC std_ss [fn_minus_def, FUN_EQ_THM]
 >> Cases_on `0 < f x`
 >- (`0 <= c x * f x` by PROVE_TAC [let_mul] \\
     `~(c x * f x < 0)` by PROVE_TAC [extreal_lt_def] \\
     `~(f x < 0)` by PROVE_TAC [lt_antisym] \\
     fs [mul_rzero])
 >> `f x <= 0` by PROVE_TAC [extreal_lt_def]
 >> `c x * f x <= 0` by PROVE_TAC [mul_le]
 >> `~(0 < c x * f x)` by PROVE_TAC [extreal_lt_def]
 >> fs [le_lt, lt_refl, mul_rzero, neg_0]
 >- REWRITE_TAC [GSYM mul_rneg]
 >> fs [entire, neg_0]);

Theorem fn_plus_mul_indicator :
    !f s. fn_plus (\x. f x * indicator_fn s x) =
          (\x. fn_plus f x * indicator_fn s x)
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC (Q.SPECL [‘f’, ‘indicator_fn s’] FN_PLUS_FMUL)
 >> GEN_TAC
 >> REWRITE_TAC [INDICATOR_FN_POS]
QED

Theorem fn_minus_mul_indicator :
    !f s. fn_minus (\x. f x * indicator_fn s x) =
          (\x. fn_minus f x * indicator_fn s x)
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [mul_comm]
 >> MATCH_MP_TAC (Q.SPECL [‘f’, ‘indicator_fn s’] FN_MINUS_FMUL)
 >> GEN_TAC
 >> REWRITE_TAC [INDICATOR_FN_POS]
QED

val FN_PLUS_ADD_LE = store_thm
  ("FN_PLUS_ADD_LE",
  ``!f g x. fn_plus (\x. f x + g x) x <= (fn_plus f x) + (fn_plus g x)``,
    RW_TAC real_ss [fn_plus_def, add_rzero, add_lzero, le_refl, le_add2]
 >> METIS_TAC [le_refl, extreal_lt_def, le_add2, add_lzero, add_rzero, lt_imp_le]);

(* more antecedents added: no mixing of PosInf and NegInf *)
val FN_MINUS_ADD_LE = store_thm
  ("FN_MINUS_ADD_LE",
  ``!f g x. (f x <> NegInf) /\ (g x <> NegInf) \/
            (f x <> PosInf) /\ (g x <> PosInf) ==>
            fn_minus (\x. f x + g x) x <= (fn_minus f x) + (fn_minus g x)``,
    rpt GEN_TAC
 >> DISCH_TAC
 >> MP_TAC (BETA_RULE (Q.SPECL [`\x. -f x`, `\x. -g x`, `x`] FN_PLUS_ADD_LE))
 >> Suff `fn_plus (\x. -f x + -g x) x = fn_minus (\x. f x + g x) x`
 >- (Rewr' >> REWRITE_TAC [FN_PLUS_TO_MINUS])
 >> SIMP_TAC std_ss [fn_plus_def, fn_minus_def]
 >> Know `-f x + -g x = -(f x + g x)`
 >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC neg_add >> art []) >> Rewr
 >> `0 < -(f x + g x) <=> f x + g x < 0` by PROVE_TAC [neg_0, lt_neg] >> POP_ORW
 >> REWRITE_TAC []);

Theorem FN_PLUS_LE_ABS :
    !f x. fn_plus f x <= abs (f x)
Proof
    rpt GEN_TAC >> REWRITE_TAC [SIMP_RULE std_ss [o_DEF] FN_ABS]
 >> ACCEPT_TAC
      (((REWRITE_RULE [le_refl, add_rzero, FN_MINUS_POS]) o
        (Q.SPECL [`fn_plus f x`, `fn_plus f x`, `0`, `fn_minus f x`])) le_add2)
QED

Theorem FN_MINUS_LE_ABS :
    !f x. fn_minus f x <= abs (f x)
Proof
    rpt GEN_TAC >> REWRITE_TAC [SIMP_RULE std_ss [o_DEF] FN_ABS]
 >> ACCEPT_TAC
      (((REWRITE_RULE [le_refl, add_lzero, FN_PLUS_POS]) o
        (Q.SPECL [`0`, `fn_plus f x`, `fn_minus f x`, `fn_minus f x`])) le_add2)
QED

(* A balance between fn_plus and fn_minus *)
Theorem FN_PLUS_INFTY_IMP :
    !f x. (fn_plus f x = PosInf) ==> (fn_minus f x = 0)
Proof
    rpt STRIP_TAC
 >> Suff ‘f x = PosInf’
 >- (DISCH_TAC >> MATCH_MP_TAC FN_MINUS_REDUCE \\
     POP_ORW >> REWRITE_TAC [extreal_of_num_def, extreal_le_def])
 >> CCONTR_TAC
 >> Suff ‘fn_plus f x <> PosInf’ >- PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘fn_plus f x = PosInf’ K_TAC
 >> RW_TAC std_ss [fn_plus_def]
 >> PROVE_TAC [extreal_not_infty, extreal_of_num_def]
QED

Theorem FN_MINUS_INFTY_IMP :
    !f x. (fn_minus f x = PosInf) ==> (fn_plus f x = 0)
Proof
    rpt STRIP_TAC
 >> Suff ‘f x = NegInf’
 >- (DISCH_TAC \\
     RW_TAC std_ss [fn_plus_def, FUN_EQ_THM] \\
     fs [lt_infty, extreal_of_num_def])
 >> CCONTR_TAC
 >> Suff ‘fn_minus f x <> PosInf’ >- PROVE_TAC []
 >> Q.PAT_X_ASSUM ‘fn_minus f x = PosInf’ K_TAC
 >> reverse (RW_TAC std_ss [fn_minus_def])
 >- PROVE_TAC [extreal_not_infty, extreal_of_num_def]
 >> CCONTR_TAC >> fs []
 >> METIS_TAC [neg_neg, extreal_ainv_def]
QED

(* ******************************************* *)
(*   Non-negative functions (not very useful)  *)
(* ******************************************* *)

val nonneg_def = Define
   `nonneg (f :'a -> extreal) = !x. 0 <= f x`;

val nonneg_abs = store_thm
  ("nonneg_abs", ``!f. nonneg (abs o f)``,
    RW_TAC std_ss [o_DEF, nonneg_def, abs_pos]);

val nonneg_fn_abs = store_thm
  ("nonneg_fn_abs", ``!f. nonneg f ==> (abs o f = f)``,
    RW_TAC std_ss [nonneg_def, o_DEF, FUN_EQ_THM, abs_refl]);

val nonneg_fn_plus = store_thm
  ("nonneg_fn_plus", ``!f. nonneg f ==> (fn_plus f = f)``,
    RW_TAC std_ss [nonneg_def, fn_plus_def]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss []
 >> PROVE_TAC [le_lt]);

val nonneg_fn_minus = store_thm
  ("nonneg_fn_minus", ``!f. nonneg f ==> (fn_minus f = (\x. 0))``,
    RW_TAC std_ss [nonneg_def, fn_minus_def]
 >> FUN_EQ_TAC
 >> RW_TAC std_ss [extreal_lt_def]);

(* ******************************************* *)
(*    Borel Space and Measurable functions     *)
(* ******************************************* *)

(* This is actually the (extended) Borel set $\overline{\mathscr{B}}$ generated
   by extended open sets, c.f. Lemma 8.3 [1, p.61].

   Named after Emile Borel [7], a French mathematician and politician.

   The pure real version of Borel set is `real_borel$borel`.
 *)
val Borel_def = Define
   `Borel = sigma univ(:extreal) (IMAGE (\a. {x | x < Normal a}) univ(:real))`;

val _ = overload_on ("Borel_measurable", ``\a. measurable a Borel``);

val SPACE_BOREL = store_thm
  ("SPACE_BOREL", ``space Borel = UNIV``,
    METIS_TAC [Borel_def, sigma_def, space_def]);

val SIGMA_ALGEBRA_BOREL = store_thm
  ("SIGMA_ALGEBRA_BOREL", ``sigma_algebra Borel``,
    RW_TAC std_ss [Borel_def]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA
 >> RW_TAC std_ss [subset_class_def,SUBSET_UNIV]);

val MEASURABLE_BOREL = store_thm
  ("MEASURABLE_BOREL",
  ``!f a. f IN measurable a Borel <=>
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ((PREIMAGE f {x| x < Normal c}) INTER (space a)) IN subsets a``,
    RW_TAC std_ss []
 >> `sigma_algebra Borel` by RW_TAC std_ss [SIGMA_ALGEBRA_BOREL]
 >> `space Borel = UNIV` by RW_TAC std_ss [Borel_def, space_def, SPACE_SIGMA]
 >> EQ_TAC
 >- (RW_TAC std_ss [Borel_def, IN_MEASURABLE, IN_FUNSET, IN_UNIV, subsets_def, GSPECIFICATION]
     >> POP_ASSUM MATCH_MP_TAC
     >> MATCH_MP_TAC IN_SIGMA
     >> RW_TAC std_ss [IN_IMAGE,IN_UNIV]
     >> METIS_TAC [])
 >> RW_TAC std_ss [Borel_def]
 >> MATCH_MP_TAC MEASURABLE_SIGMA
 >> RW_TAC std_ss [subset_class_def,SUBSET_UNIV,IN_IMAGE,IN_UNIV]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL = store_thm
  ("IN_MEASURABLE_BOREL",
  ``!f a. f IN measurable a Borel <=>
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | f x < Normal c} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  >> `!c. {x | f x < Normal c} = PREIMAGE f {x| x < Normal c}`
       by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION]
  >> RW_TAC std_ss [MEASURABLE_BOREL]);

val IN_MEASURABLE_BOREL_NEGINF = store_thm
  ("IN_MEASURABLE_BOREL_NEGINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x = NegInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x = NegInf} INTER space a =
          BIGINTER (IMAGE (\n. {x | f x < -(&n)} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC >- METIS_TAC [num_not_infty,lt_infty,extreal_ainv_def,extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH_NEG, extreal_lt_def,extreal_ainv_def,neg_neg,lt_neg])
 >> Rewr'
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `- &n = Normal (- &n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_NOT_POSINF = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_NOT_POSINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x <> PosInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x <> PosInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | f x < &n} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (rpt STRIP_TAC \\
         `?n. f x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` >> art [] \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >- METIS_TAC [num_not_infty, lt_infty] \\
     ASM_REWRITE_TAC [])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x < c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- (REWRITE_TAC [GSYM lt_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [])
 >> fs [IN_MEASURABLE_BOREL]);

(* the same theorems with more meaningful names, new *)
val IN_MEASURABLE_BOREL_RO = save_thm
  ("IN_MEASURABLE_BOREL_RO", IN_MEASURABLE_BOREL_IMP);

val IN_MEASURABLE_BOREL_ALT1 = store_thm
  ("IN_MEASURABLE_BOREL_ALT1",
  ``!f a. f IN measurable a Borel <=>
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | Normal c <= f x} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> EQ_TAC
 >- (RW_TAC std_ss []
     >> `{x | Normal c <= f x} = PREIMAGE f {x | Normal c <= x}`
         by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
     >> `!c. {x | f x < Normal c} = PREIMAGE f {x | x < Normal c}`
         by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
     >> `!c. space a DIFF ((PREIMAGE f {x | x < Normal c}) INTER space a) IN subsets a`
         by METIS_TAC [sigma_algebra_def, algebra_def]
     >> `!c. space a DIFF (PREIMAGE f {x | x < Normal c}) IN subsets a` by METIS_TAC [DIFF_INTER2]
     >> `!c. (PREIMAGE f (COMPL {x | x < Normal c}) INTER space a) IN subsets a`
         by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
     >> `!c. COMPL {x | x < Normal c} = {x | Normal c <= x}`
         by RW_TAC std_ss [EXTENSION, IN_COMPL, IN_UNIV, IN_DIFF, GSPECIFICATION, extreal_lt_def]
     >> FULL_SIMP_TAC std_ss [])
 >> RW_TAC std_ss []
 >> `{x | f x < Normal c} = PREIMAGE f {x | x < Normal c}`
     by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
 >> `!c. {x | Normal c <= f x} = PREIMAGE f {x | Normal c <= x}`
     by RW_TAC std_ss [PREIMAGE_def, GSPECIFICATION]
 >> `!c. space a DIFF ((PREIMAGE f {x | Normal c <= x}) INTER space a) IN subsets a`
     by METIS_TAC [sigma_algebra_def,algebra_def]
 >> `!c. space a DIFF (PREIMAGE f {x | Normal c <= x}) IN subsets a` by METIS_TAC [DIFF_INTER2]
 >> `!c. (PREIMAGE f (COMPL {x | Normal c <= x}) INTER space a) IN subsets a`
     by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
 >> `!c. COMPL {x | Normal c <= x} = {x | x < Normal c}`
     by RW_TAC std_ss [EXTENSION, IN_COMPL, IN_UNIV, IN_DIFF, GSPECIFICATION, extreal_lt_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT2 = store_thm
  ("IN_MEASURABLE_BOREL_ALT2",
  ``!f a. f IN measurable a Borel <=>
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | f x <= Normal c} INTER space a) IN subsets a``,
    RW_TAC std_ss []
 >> EQ_TAC
 >- (RW_TAC std_ss [IN_MEASURABLE_BOREL]
     >> `!c. {x | f x <= Normal c} INTER (space a) =
             BIGINTER (IMAGE (\n:num. {x | f x < Normal (c + (1/2) pow n)} INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION,GSYM extreal_add_def]
                >> `0:real < (1 / 2) pow n` by RW_TAC real_ss [REAL_POW_LT]
                >> `0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_of_num_def,extreal_lt_eq]
                >> Cases_on `f x = NegInf` >- METIS_TAC [lt_infty,extreal_add_def]
                >> METIS_TAC [let_add2,extreal_of_num_def,extreal_not_infty,add_rzero,le_infty])
             >> RW_TAC std_ss [GSPECIFICATION]
             >> `!n. f x < Normal (c + (1 / 2) pow n)` by METIS_TAC []
             >> `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n) ` by RW_TAC real_ss [FUN_EQ_THM]
             >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
             >> `(\n. c + (1 / 2) pow n) --> c` by METIS_TAC [SEQ_CONST, Q.SPECL [`(\n:num. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD,REAL_ADD_RID]
             >> Cases_on `f x = NegInf` >- METIS_TAC [le_infty]
             >> `f x <> PosInf` by METIS_TAC [lt_infty]
             >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
             >> METIS_TAC [REAL_LT_IMP_LE,
                           Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM])
     >> `BIGINTER (IMAGE (\n:num. {x | f x < Normal (c + (1 / 2) pow n)} INTER space a) UNIV)
           IN subsets a`
         by (RW_TAC std_ss []
             >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN_BIGINTER
             >> RW_TAC std_ss []
             >> `(\n. {x | f x < Normal (c + (1/2) pow n)} INTER space a) IN (UNIV -> subsets a)`
                 by (RW_TAC std_ss [IN_FUNSET])
             >> METIS_TAC [])
     >> METIS_TAC [])
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c. {x | f x < Normal c} INTER (space a) =
         BIGUNION (IMAGE (\n:num. {x | f x <= Normal (c - (1/2) pow n)} INTER space a) UNIV)`
     by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV,IN_INTER,GSPECIFICATION]
         >> `(\n. c - (1 / 2) pow n) = (\n. (\n. c) n - (\n. (1 / 2) pow n) n)`
             by RW_TAC real_ss [FUN_EQ_THM]
         >> `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
         >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
         >> `(\n. c - (1 / 2) pow n) --> c`
             by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_SUB, REAL_SUB_RZERO]
         >> EQ_TAC
         >- (RW_TAC std_ss []
             >> Cases_on `f x = NegInf` >- METIS_TAC [le_infty]
             >> `f x <> PosInf` by METIS_TAC [lt_infty]
             >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
             >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> abs ((1 / 2) pow n) < e`
                 by FULL_SIMP_TAC real_ss [Q.SPECL [`(\n. (1/2) pow n)`,`0`] SEQ, REAL_SUB_RZERO]
             >> `!n. abs ((1 / 2) pow n):real = (1 / 2) pow n`
                 by FULL_SIMP_TAC real_ss [POW_POS, ABS_REFL]
             >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> (1 / 2) pow n < e` by METIS_TAC []
             >> `?N. !n. n >= N ==> (1 / 2) pow n < c - r` by METIS_TAC [REAL_SUB_LT]
             >> Q.EXISTS_TAC `N`
             >> `(1 / 2) pow N < c - r` by FULL_SIMP_TAC real_ss []
             >> FULL_SIMP_TAC real_ss [GSYM REAL_LT_ADD_SUB,REAL_ADD_COMM,REAL_LT_IMP_LE])
         >> RW_TAC std_ss []
         >- (`!n. - ((1 / 2) pow n) < 0:real`
              by METIS_TAC [REAL_POW_LT, REAL_NEG_0, REAL_LT_NEG, EVAL ``0:real < 1/2``]
             >> `!n. c - (1 / 2) pow n < c` by METIS_TAC [REAL_LT_IADD,REAL_ADD_RID,real_sub]
             >> Cases_on `f x = NegInf` >- METIS_TAC [lt_infty]
             >> `f x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
             >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_lt_eq,extreal_le_def]
             >> METIS_TAC [REAL_LET_TRANS])
         >> METIS_TAC [])
 >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC SIGMA_ALGEBRA_ENUM
 >> RW_TAC std_ss [IN_FUNSET]);

val IN_MEASURABLE_BOREL_ALT2_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT2_IMP",
  ``!f a. f IN measurable a Borel ==> !c. ({x | f x <= c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >- (REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >> fs [IN_MEASURABLE_BOREL_ALT2]);

val IN_MEASURABLE_BOREL_RC = save_thm
  ("IN_MEASURABLE_BOREL_RC", IN_MEASURABLE_BOREL_ALT2_IMP);

val IN_MEASURABLE_BOREL_ALT3 = store_thm
  ("IN_MEASURABLE_BOREL_ALT3",
  ``!f a. f IN measurable a Borel <=>
          sigma_algebra a /\ f IN (space a -> UNIV) /\
          !c. ({x | Normal c < f x} INTER space a) IN subsets a``,
 RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2,GSPECIFICATION]
 >> EQ_TAC
 >- (RW_TAC std_ss []
     >> `{x|Normal c < f x} = PREIMAGE f {x | Normal c < x}` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
     >> `!c. {x | f x <= Normal c} = PREIMAGE f {x | x <= Normal c}` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
     >> `!c. space a DIFF ((PREIMAGE f {x | x <= Normal c}) INTER space a) IN subsets a` by METIS_TAC [sigma_algebra_def,algebra_def]
     >> `!c. space a DIFF (PREIMAGE f {x | x <= Normal c}) IN subsets a` by METIS_TAC [DIFF_INTER2]
     >> `!c. (PREIMAGE f (COMPL {x | x <= Normal c}) INTER space a) IN subsets a` by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
     >> `COMPL {x | x <= Normal c} = {x | Normal c < x}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_COMPL,extreal_lt_def]
     >> METIS_TAC [])
 >> RW_TAC std_ss []
 >> `{x | f x <= Normal c} = PREIMAGE f {x | x <= Normal c}` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
 >> `!c. { x | Normal c < f x } = PREIMAGE f { x | Normal c < x }` by RW_TAC std_ss[PREIMAGE_def,GSPECIFICATION]
 >> `!c. space a DIFF ((PREIMAGE f {x | Normal c < x}) INTER space a) IN subsets a` by METIS_TAC [sigma_algebra_def,algebra_def]
 >> `!c. space a DIFF (PREIMAGE f {x | Normal c < x}) IN subsets a` by METIS_TAC [DIFF_INTER2]
 >> `!c. (PREIMAGE f (COMPL {x | Normal c < x}) INTER space a) IN subsets a` by METIS_TAC [GSYM PREIMAGE_COMPL_INTER]
 >> `COMPL {x | Normal c < x} = {x | x <= Normal c}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_COMPL,extreal_lt_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_POSINF = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_POSINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x = PosInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x = PosInf} INTER space a =
          BIGINTER (IMAGE (\n. {x | &n < f x} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC >- METIS_TAC [num_not_infty, lt_infty, extreal_ainv_def, extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH, extreal_lt_def])
 >> Rewr'
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_NOT_NEGINF = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_NOT_NEGINF",
  ``!f a. f IN measurable a Borel ==>
          ({x | f x <> NegInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3, GSPECIFICATION, IN_FUNSET, IN_UNIV]
 >> Know `{x | f x <> NegInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | -(&n) < f x} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (rpt STRIP_TAC \\
         `?n. -(&n) <= f x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` >> art [] \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >- METIS_TAC [num_not_infty, lt_infty] \\
     ASM_REWRITE_TAC [])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT1_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT1_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | c <= f x} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >- (REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >> fs [IN_MEASURABLE_BOREL_ALT1]);

val IN_MEASURABLE_BOREL_CR = save_thm
  ("IN_MEASURABLE_BOREL_CR", IN_MEASURABLE_BOREL_ALT1_IMP);

val IN_MEASURABLE_BOREL_ALT3_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT3_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | c < f x} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [])
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >> fs [IN_MEASURABLE_BOREL_ALT3]);

val IN_MEASURABLE_BOREL_OR = save_thm
  ("IN_MEASURABLE_BOREL_OR", IN_MEASURABLE_BOREL_ALT3_IMP);

val IN_MEASURABLE_BOREL_ALT4 = store_thm
  ("IN_MEASURABLE_BOREL_ALT4",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel <=>
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x | Normal c <= f x /\ f x < Normal d} INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- (STRIP_TAC
      >> CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL]
      >> CONJ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL]
      >> RW_TAC std_ss []
      >> `(!d. {x | f x < Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
      >> `(!c. {x | Normal c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
      >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a`
          by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) =
                 ({x | Normal c <= f x} INTER {x | f x < Normal d} INTER space a)`
          by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
      >> `{x | Normal c <= f x} INTER {x | f x < Normal d} = {x | Normal c <= f x /\ f x < Normal d}`
          by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> `{x | Normal c <= f x} INTER {x | f x < Normal d} = {x | Normal c <= f x /\ f x < Normal d}`
          by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> METIS_TAC [])
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
  >> `!c. {x | f x < Normal c} INTER (space a) =
          BIGUNION (IMAGE (\n:num. {x | Normal (- &n) <= f x /\ f x < Normal c} INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION]
                >> `f x <> PosInf` by METIS_TAC [lt_infty]
                >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                >> METIS_TAC [SIMP_REAL_ARCH_NEG,extreal_le_def])
            >> RW_TAC std_ss [GSPECIFICATION] >> METIS_TAC [lt_infty])
  >> `BIGUNION (IMAGE (\n:num. {x | Normal (- &n) <= f x /\ f x < Normal c } INTER space a) UNIV) IN subsets a`
        by (RW_TAC std_ss []
            >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
            >> RW_TAC std_ss []
            >> `(\n. {x | Normal (- &n) <= f x /\ f x < Normal c} INTER space a) IN (UNIV -> subsets a)`
                by (RW_TAC std_ss [IN_FUNSET])
            >> `{x | Normal (-&n) <= f x /\ f x < Normal c} INTER space a IN subsets a` by METIS_TAC []
            >> METIS_TAC [])
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT5 = store_thm
  ("IN_MEASURABLE_BOREL_ALT5",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel <=>
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x | Normal c < f x /\ f x <= Normal d} INTER space a) IN subsets a)``,
    RW_TAC std_ss []
 >> EQ_TAC
 >- ((RW_TAC std_ss [] >| [METIS_TAC [IN_MEASURABLE_BOREL], METIS_TAC [IN_MEASURABLE_BOREL], ALL_TAC])
     >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
     >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
     >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
     >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
          by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
     >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <=  Normal d} INTER space a)) =
                ({x | Normal c < f x} INTER {x | f x <= Normal d} INTER space a)`
          by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
     >> `{x | Normal c < f x} INTER {x | f x <= Normal d} = {x | Normal c < f x /\ f x <= Normal d}`
          by RW_TAC std_ss [EXTENSION ,GSPECIFICATION, IN_INTER]
     >> `{x | Normal c < f x} INTER {x | f x <= Normal d} = {x | Normal c < f x /\ f x <= Normal d}`
          by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
     >> METIS_TAC [])
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2]
 >> `!c. {x | f x <= Normal c} INTER (space a) =
          BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x <= Normal c } INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION]
                >> `f x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
                >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
                >> (MP_TAC o Q.SPEC `r`) SIMP_REAL_ARCH_NEG
                >> RW_TAC real_ss []
                >> Q.EXISTS_TAC `n+1`
                >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
                >> RW_TAC real_ss [REAL_NEG_ADD, REAL_LT_ADD_SUB,REAL_LT_ADD1])
            >> RW_TAC std_ss [GSPECIFICATION] >> METIS_TAC [lt_infty])
 >> `BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x <= Normal c } INTER space a) UNIV) IN subsets a`
     by (RW_TAC std_ss []
         >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
         >> RW_TAC std_ss []
         >> `(\n. {x | Normal (-&n) < f x /\ f x <= Normal c} INTER space a) IN (UNIV -> subsets a)`
            by FULL_SIMP_TAC real_ss [IN_FUNSET, GSPECIFICATION, IN_INTER]
         >> `{x | Normal (-&n) < f x /\ f x <= Normal c} INTER space a IN subsets a` by METIS_TAC []
         >> METIS_TAC [])
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT6 = store_thm
  ("IN_MEASURABLE_BOREL_ALT6",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel <=>
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x| Normal c <= f x /\ f x <= Normal d} INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- ((RW_TAC std_ss [] >| [METIS_TAC [IN_MEASURABLE_BOREL], METIS_TAC [IN_MEASURABLE_BOREL], ALL_TAC])
      >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
      >> `(!c. {x | Normal c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
      >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
         by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
      >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
                ({x | Normal c <= f x} INTER {x | f x <= Normal d} INTER space a)`
         by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
      >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
         by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
         by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> METIS_TAC [])
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT4]
  >> `!c. {x | Normal c <= f x /\ f x < Normal d} INTER (space a) =
          BIGUNION (IMAGE (\n:num. {x | Normal c <= f x /\ f x <= Normal (d - (1/2) pow n)} INTER space a) UNIV)`
      by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER, GSPECIFICATION]
          >> `(\n. c - (1 / 2) pow n) = (\n. (\n. c) n - (\n. (1 / 2) pow n) n) ` by RW_TAC real_ss [FUN_EQ_THM]
          >> `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
          >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
          >> `(\n. c - (1 / 2) pow n) --> c`
             by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_SUB,REAL_SUB_RZERO]
          >> EQ_TAC
          >- (RW_TAC std_ss []
              >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> abs ((1 / 2) pow n) < e`
                 by FULL_SIMP_TAC real_ss [Q.SPECL [`(\n. (1/2) pow n)`,`0`] SEQ,REAL_SUB_RZERO]
              >> `!n. abs ((1/2) pow n) = ((1/2) pow n):real` by FULL_SIMP_TAC real_ss [POW_POS,ABS_REFL]
              >> `!e:real. 0 < e ==> ?N. !n. n >= N ==> (1 / 2) pow n < e` by METIS_TAC []
              >> `f x <> PosInf` by METIS_TAC [lt_infty]
              >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
              >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
              >> `?N. !n. n >= N ==> (1 / 2) pow n < d - r` by METIS_TAC [REAL_SUB_LT]
              >> Q.EXISTS_TAC `N`
              >> `(1 / 2) pow N < d - r` by FULL_SIMP_TAC real_ss []
              >> FULL_SIMP_TAC real_ss [GSYM REAL_LT_ADD_SUB, REAL_ADD_COMM, REAL_LT_IMP_LE])
          >> RW_TAC std_ss [] >|
             [ METIS_TAC[],
               `!n. - ((1 / 2) pow n) < 0:real` by METIS_TAC [REAL_POW_LT, REAL_NEG_0, REAL_LT_NEG, EVAL ``0:real < 1/2``]
               >> `!n. d - (1 / 2) pow n < d` by METIS_TAC [REAL_LT_IADD, REAL_ADD_RID, real_sub]
               >> `f x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
               >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
               >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
               >> METIS_TAC [REAL_LET_TRANS],
               METIS_TAC [] ])
  >> `BIGUNION (IMAGE (\n:num. {x | Normal c <= f x /\ f x <= Normal (d - ((1 / 2) pow n))} INTER space a) UNIV)
      IN subsets a`
      by (RW_TAC std_ss []
          >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
          >> RW_TAC std_ss []
          >> `(\n. {x | Normal c <= f x /\ f x <= Normal (d - ((1 / 2) pow n))} INTER space a) IN (UNIV -> subsets a)`
             by FULL_SIMP_TAC real_ss [IN_FUNSET, GSPECIFICATION, IN_INTER]
          >> `{x | Normal c <= f x /\ f x <= Normal (d - ((1/2) pow n))} INTER space a IN subsets a` by METIS_TAC []
          >> METIS_TAC [])
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7 = store_thm
  ("IN_MEASURABLE_BOREL_ALT7",
  ``!f a. (!x. f x <> NegInf) ==>
          (f IN measurable a Borel <=>
           sigma_algebra a /\ f IN (space a -> UNIV) /\
           !c d. ({x | Normal c < f x /\ f x < Normal d } INTER space a) IN subsets a)``,
  RW_TAC std_ss []
  >> EQ_TAC
  >- (RW_TAC std_ss [IN_FUNSET,IN_UNIV]
      >- METIS_TAC [IN_MEASURABLE_BOREL]
      >> `(!d. {x | f x < Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
      >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
      >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
      >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a` by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
      >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) =
                 ({x | Normal c < f x} INTER {x | f x < Normal d} INTER space a)`
            by METIS_TAC [INTER_ASSOC,INTER_COMM,INTER_IDEMPOT]
      >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
      >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}` by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
      >> METIS_TAC [])
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
  >> `!c. {x | f x < Normal c} INTER (space a) = BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x < Normal c } INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC std_ss [GSPECIFICATION]
                >> `f x <> PosInf` by METIS_TAC [lt_infty]
                >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
                >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
                >> (MP_TAC o Q.SPEC `r`) SIMP_REAL_ARCH_NEG
                     >> RW_TAC real_ss []
                     >> Q.EXISTS_TAC `n + 1`
                     >> ONCE_REWRITE_TAC [GSYM REAL_ADD]
                     >> RW_TAC real_ss [REAL_NEG_ADD, REAL_LT_ADD_SUB,REAL_LT_ADD1])
            >> RW_TAC std_ss [GSPECIFICATION] >> METIS_TAC [lt_infty])
  >> `BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x < Normal c } INTER space a) UNIV) IN subsets a`
        by (RW_TAC std_ss []
            >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
            >> RW_TAC std_ss []
            >> `(\n. {x | Normal (-&n) < f x /\ f x < Normal c} INTER space a) IN (UNIV -> subsets a)` by FULL_SIMP_TAC real_ss [IN_FUNSET,GSPECIFICATION,IN_INTER]
            >> `{x | Normal (-&n) < f x /\ f x < Normal c} INTER space a IN subsets a` by METIS_TAC []
            >> METIS_TAC [])
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT4_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | Normal c <= f x /\ f x < Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `!d. {x | f x < Normal d} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL]
 >> `!c. {x | Normal c <= f x} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) =
            ({x | Normal c <= f x} INTER {x | f x < Normal d} INTER space a)`
    by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> `{x | Normal c <= f x} INTER {x | f x < Normal d} = {x | Normal c <= f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT4_IMP_p = prove (
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | Normal c <= f x /\ f x < PosInf} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> Know `{x | f x < PosInf} INTER space a IN subsets a`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     METIS_TAC [IN_MEASURABLE_BOREL_NOT_POSINF]) >> DISCH_TAC
 >> `!c. {x | Normal c <= f x} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < PosInf} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c. (({x | Normal c <= f x} INTER space a) INTER ({x | f x < PosInf} INTER space a)) =
          ({x | Normal c <= f x} INTER {x | f x < PosInf} INTER space a)`
    by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> `{x | Normal c <= f x} INTER {x | f x < PosInf} = {x | Normal c <= f x /\ f x < PosInf}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT4_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT4_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | c <= f x /\ f x < d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_IMP >> art [])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     SIMP_TAC std_ss [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= f x /\ f x < Normal r <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT4_IMP_p >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT4_IMP_r >> art []);

val IN_MEASURABLE_BOREL_CO = save_thm
  ("IN_MEASURABLE_BOREL_CO", IN_MEASURABLE_BOREL_ALT4_IMP);

val IN_MEASURABLE_BOREL_ALT5_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | Normal c < f x /\ f x <= Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
 >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
           ({x | Normal c < f x} INTER {x | f x <= Normal d} INTER space a)`
    by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> `{x | Normal c < f x} INTER {x | f x <= Normal d} =
     {x | Normal c < f x /\ f x <= Normal d}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT5_IMP_n = prove (
  ``!f a. f IN measurable a Borel ==>
          !d. ({x | NegInf < f x /\ f x <= Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `!d. {x | f x <= Normal d} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
 >> Know `{x | NegInf < f x} INTER space a IN subsets a`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     METIS_TAC [IN_MEASURABLE_BOREL_NOT_NEGINF]) >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!d. (({x | NegInf < f x} INTER space a) INTER
          ({x | f x <= Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!d. (({x | NegInf < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
          ({x | NegInf < f x} INTER {x | f x <= Normal d} INTER space a)`
    by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> `{x | NegInf < f x} INTER {x | f x <= Normal d} =
     {x | NegInf < f x /\ f x <= Normal d}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT5_IMP = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT5_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | c < f x /\ f x <= d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     `!x. NegInf < f x /\ f x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [])
 >- ((* goal 3 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT5_IMP_n >> art [])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r < f x /\ f x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT3_IMP >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT5_IMP_r >> art []);

val IN_MEASURABLE_BOREL_OC = save_thm
  ("IN_MEASURABLE_BOREL_OC", IN_MEASURABLE_BOREL_ALT5_IMP);

val IN_MEASURABLE_BOREL_ALT6_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x| Normal c <= f x /\ f x <= Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET,IN_UNIV]
 >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
 >> `(!c. {x | Normal c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
           ({x | Normal c <= f x} INTER {x | f x <= Normal d} INTER space a)`
    by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
  >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
    by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
  >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
    by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
  >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT6_IMP  = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT6_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x| c <= f x /\ f x <= d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT2_IMP >> art [])
 >- ((* goal 4 (of 9) *)
     `!x. PosInf <= f x /\ f x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, extreal_cases] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= f x /\ f x <= Normal r <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r <= f x /\ f x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT1_IMP >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT6_IMP_r >> art []);

val IN_MEASURABLE_BOREL_CC = save_thm
  ("IN_MEASURABLE_BOREL_CC", IN_MEASURABLE_BOREL_ALT6_IMP);

val IN_MEASURABLE_BOREL_ALT7_IMP_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | Normal c < f x /\ f x < Normal d} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `(!d. {x | f x < Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
 >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c d. ({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a) =
           ({x | Normal c < f x} INTER {x | f x < Normal d} INTER space a)`
    by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP_np = prove ((* new *)
  ``!f a. f IN measurable a Borel ==>
          ({x | NegInf < f x /\ f x < PosInf} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> fs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Know `{x | NegInf < f x /\ f x < PosInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | -&n < f x /\ f x < &n} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n1. -&n1 <= f x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         `?n2. f x <= &n2` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC (MAX n1 n2)` \\
         CONJ_TAC >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n1` >> art [] \\
                      SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
                      MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
                      REWRITE_TAC [MAX_LE] >> DISJ1_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n2` >> art [] \\
         SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
         MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
         REWRITE_TAC [MAX_LE] >> DISJ2_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP_n = prove ((* new *)
  ``!f a. f IN measurable a Borel ==>
          !d. ({x | NegInf < f x /\ f x < Normal d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> fs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Know `{x | NegInf < f x /\ f x < Normal d} INTER space a =
          BIGUNION (IMAGE (\n. {x | -&n < f x /\ f x < Normal d} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. -&n <= f x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP_p = prove ((* new *)
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | Normal c < f x /\ f x < PosInf} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> fs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Know `{x | Normal c < f x /\ f x < PosInf} INTER space a =
          BIGUNION (IMAGE (\n. {x | Normal c < f x /\ f x < &n} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION, IN_INTER] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. f x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_ALT7_IMP = store_thm
  ("IN_MEASURABLE_BOREL_ALT7_IMP",
  ``!f a. f IN measurable a Borel ==>
          !c d. ({x | c < f x /\ f x < d} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_np >> art [])
 >- ((* goal 3 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_n >> art [])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_p >> art [])
 (* goal 9 (of 9) *)
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r >> art []);

val IN_MEASURABLE_BOREL_OO = save_thm (* not "00" *)
  ("IN_MEASURABLE_BOREL_OO", IN_MEASURABLE_BOREL_ALT7_IMP);

val IN_MEASURABLE_BOREL_ALT8_r = prove (
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x = Normal c} INTER space a) IN subsets a``,
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> MP_TAC IN_MEASURABLE_BOREL_ALT4_IMP_r
 >> RW_TAC std_ss []
 >> Know `!c. {x | f x = Normal c} INTER (space a) =
              BIGINTER (IMAGE (\n. {x | Normal (c - ((1/2) pow n)) <= f x /\
                                        f x < Normal (c + ((1/2) pow n))} INTER space a) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_SING,IN_INTER] \\
     EQ_TAC >- RW_TAC real_ss [extreal_le_def, extreal_lt_eq, GSPECIFICATION, REAL_POW_LT,
                               REAL_LT_IMP_LE, REAL_LT_ADDR, REAL_LT_DIV, HALF_POS,
                               REAL_LT_ADDNEG2, real_sub, IN_INTER] \\
     RW_TAC std_ss [GSPECIFICATION] \\
    `f x <> PosInf` by METIS_TAC [lt_infty] \\
    `f x <> NegInf` by METIS_TAC [le_infty, extreal_not_infty] \\
    `?r. f x = Normal r` by METIS_TAC [extreal_cases] \\
     FULL_SIMP_TAC std_ss [extreal_le_def, extreal_lt_eq, extreal_11] \\
    `!n. c - (1 / 2) pow n <= r` by FULL_SIMP_TAC real_ss [real_sub] \\
    `!n. r <= c + (1 / 2) pow n` by FULL_SIMP_TAC real_ss [REAL_LT_IMP_LE] \\
    `(\n. c - (1 / 2) pow n) = (\n. (\n. c) n - (\n. (1 / 2) pow n) n)`
        by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n)`
        by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST] \\
    `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER] \\
    `(\n. c - (1 / 2) pow n) --> c`
        by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_SUB, REAL_SUB_RZERO] \\
    `(\n. c + (1 / 2) pow n) --> c`
        by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD, REAL_ADD_RID] \\
    `c <= r` by METIS_TAC [Q.SPECL [`r`,`c`,`(\n. c - (1 / 2) pow n)`] SEQ_LE_IMP_LIM_LE] \\
    `r <= c` by METIS_TAC [Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM] \\
     METIS_TAC [REAL_LE_ANTISYM]) >> Rewr'
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPEC `a` SIGMA_ALGEBRA_FN_BIGINTER)
 >> RW_TAC std_ss []
 >> `(\n. {x | Normal (c - ((1/2) pow n)) <= f x /\
               f x < Normal (c + ((1/2) pow n))} INTER space a) IN (UNIV -> subsets a)`
        by (RW_TAC std_ss [IN_FUNSET])
 >> METIS_TAC [IN_MEASURABLE_BOREL]);

val IN_MEASURABLE_BOREL_ALT8 = store_thm (* new *)
  ("IN_MEASURABLE_BOREL_ALT8",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x = c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> Cases_on `c` (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      RW_TAC std_ss [IN_MEASURABLE_BOREL] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [IN_MEASURABLE_BOREL],
      (* goal 2 (of 3) *)
      RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [IN_MEASURABLE_BOREL_ALT3],
      (* goal 3 (of 3) *)
      IMP_RES_TAC IN_MEASURABLE_BOREL_ALT8_r >> art [] ]);

val IN_MEASURABLE_BOREL_SING = save_thm
  ("IN_MEASURABLE_BOREL_SING", IN_MEASURABLE_BOREL_ALT8);

val IN_MEASURABLE_BOREL_ALT9 = store_thm
  ("IN_MEASURABLE_BOREL_ALT9",
  ``!f a. f IN measurable a Borel ==>
          !c. ({x | f x <> c} INTER space a) IN subsets a``,
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_SING
 >> Know `!c. {x | f x <> c} INTER (space a) =
              space a DIFF ({x | f x = c} INTER space a)`
 >- (RW_TAC std_ss [EXTENSION, IN_UNIV, IN_DIFF, IN_INTER, GSPECIFICATION] \\
     EQ_TAC >- (rpt STRIP_TAC >> art []) \\
     METIS_TAC []) >> Rewr
 >> fs [IN_MEASURABLE_BOREL]
 >> MATCH_MP_TAC ALGEBRA_COMPL
 >> CONJ_TAC
 >- IMP_RES_TAC SIGMA_ALGEBRA_ALGEBRA
 >> ASM_REWRITE_TAC []);

val IN_MEASURABLE_BOREL_NOT_SING = save_thm
  ("IN_MEASURABLE_BOREL_NOT_SING", IN_MEASURABLE_BOREL_ALT9);

(* all IMP versions of IN_MEASURABLE_BOREL_ALTs *)
val IN_MEASURABLE_BOREL_ALL = store_thm
  ("IN_MEASURABLE_BOREL_ALL",
  ``!f a.
        f IN measurable a Borel ==>
        (!c. {x | f x < c} INTER space a IN subsets a) /\
        (!c. {x | c <= f x} INTER space a IN subsets a) /\
        (!c. {x | f x <= c} INTER space a IN subsets a) /\
        (!c. {x | c < f x} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x < d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x < d} INTER space a IN subsets a) /\
        (!c. {x | f x = c} INTER space a IN subsets a) /\
        (!c. {x | f x <> c} INTER space a IN subsets a)``,
    METIS_TAC [IN_MEASURABLE_BOREL_RO,         (* f x < c *)
               IN_MEASURABLE_BOREL_CR,         (* c <= f x *)
               IN_MEASURABLE_BOREL_RC,         (* f x <= c *)
               IN_MEASURABLE_BOREL_OR,         (* c < f x *)
               IN_MEASURABLE_BOREL_CO,         (* c <= f x /\ f x < d *)
               IN_MEASURABLE_BOREL_OC,         (* c < f x /\ f x <= d *)
               IN_MEASURABLE_BOREL_CC,         (* c <= f x /\ f x <= d *)
               IN_MEASURABLE_BOREL_OO,         (* c < f x /\ f x < d *)
               IN_MEASURABLE_BOREL_SING,       (* f x = c *)
               IN_MEASURABLE_BOREL_NOT_SING]); (* f x <> c *)

(* |- !f m.
         f IN measurable (m_space m,measurable_sets m) Borel ==>
         (!c. {x | f x < c} INTER m_space m IN measurable_sets m) /\
         (!c. {x | c <= f x} INTER m_space m IN measurable_sets m) /\
         (!c. {x | f x <= c} INTER m_space m IN measurable_sets m) /\
         (!c. {x | c < f x} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c <= f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c < f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c <= f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
         (!c d. {x | c < f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
         !c. {x | f x = c} INTER m_space m IN measurable_sets m /\
         !c. {x | f x <> c} INTER m_space m IN measurable_sets m
 *)
val IN_MEASURABLE_BOREL_ALL_MEASURE = save_thm
  ("IN_MEASURABLE_BOREL_ALL_MEASURE",
  ((Q.GENL [`f`, `m`]) o
   (REWRITE_RULE [space_def, subsets_def]) o
   (Q.SPECL [`f`, `(m_space m,measurable_sets m)`])) IN_MEASURABLE_BOREL_ALL);

val IN_MEASURABLE_BOREL_LT = store_thm
  ("IN_MEASURABLE_BOREL_LT",
  ``!f g a. f IN measurable a Borel /\ g IN measurable a Borel ==>
            ({x | f x < g x} INTER space a) IN subsets a``,
  RW_TAC std_ss []
  >> `{x | f x < g x} INTER space a =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < g x} INTER space a) Q_set)`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_INTER]
            >> EQ_TAC
            >- RW_TAC std_ss [Q_DENSE_IN_R]
            >> METIS_TAC [lt_trans])
  >> POP_ORW
  >> MATCH_MP_TAC BIGUNION_IMAGE_Q
  >> CONJ_TAC
  >- FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
  >> RW_TAC std_ss [IN_FUNSET]
  >> `{x | f x < r /\ r < g x} INTER space a =
     ({x | f x < r} INTER space a) INTER ({x | r < g x} INTER space a)`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
  >> POP_ORW
  >> MATCH_MP_TAC ALGEBRA_INTER
  >> CONJ_TAC
  >- FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL, sigma_algebra_def]
  >> `?c. r = Normal c` by METIS_TAC [rat_not_infty, extreal_cases]
  >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]);

(* changed quantifier orders (was: f g a) *)
Theorem IN_MEASURABLE_BOREL_LE :
    !a f g. f IN measurable a Borel /\ g IN measurable a Borel ==>
            ({x | f x <= g x} INTER space a) IN subsets a
Proof
    RW_TAC std_ss []
 >> `{x | f x <= g x} INTER space a = space a DIFF ({x | g x < f x} INTER space a)`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF] \\
          METIS_TAC [extreal_lt_def])
 >> `{x | g x < f x} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_LT]
 >> METIS_TAC [algebra_def, IN_MEASURABLE_BOREL, sigma_algebra_def]
QED

(* changed quantifier orders (was: f g m) for applications in martingaleTheory *)
Theorem IN_MEASURABLE_BOREL_EQ :
    !m f g. (!x. x IN m_space m ==> (f x = g x)) /\
            g IN measurable (m_space m,measurable_sets m) Borel ==>
            f IN measurable (m_space m,measurable_sets m) Borel
Proof
    RW_TAC std_ss []
 >> FULL_SIMP_TAC std_ss [IN_MEASURABLE_BOREL]
 >> CONJ_TAC
 >- (EVAL_TAC THEN SRW_TAC[] [IN_DEF, space_def, IN_FUNSET])
 >> GEN_TAC
 >> POP_ASSUM (MP_TAC o Q.SPEC `c`)
 >> MATCH_MP_TAC EQ_IMPLIES >> AP_THM_TAC >> AP_TERM_TAC
 >> ASM_SET_TAC [space_def]
QED

(*****************************************************)

val BOREL_MEASURABLE_SETS_RO_r = prove (
  ``!c. {x | x < Normal c} IN subsets Borel``,
    RW_TAC std_ss [Borel_def]
 >> MATCH_MP_TAC IN_SIGMA
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV]
 >> METIS_TAC []);

val BOREL_MEASURABLE_SETS_NEGINF = prove ((* new *)
  ``{x | x = NegInf} IN subsets Borel``,
 (* proof *)
    Know `{x | x = NegInf} = BIGINTER (IMAGE (\n. {x | x < -(&n)}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC >- METIS_TAC [num_not_infty,lt_infty,extreal_ainv_def,extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH_NEG, extreal_lt_def, extreal_ainv_def, neg_neg, lt_neg])
 >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (- &n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RO_r]);

val BOREL_MEASURABLE_SETS_NEGINF' = prove ((* new *)
  ``{NegInf} IN subsets Borel``,
    Know `{NegInf} = {x | x = NegInf}`
 >- RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING]
 >> Rewr' >> REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF]);

val BOREL_MEASURABLE_SETS_NOT_POSINF = prove ((* new *)
  ``{x | x <> PosInf} IN subsets Borel``,
    Know `{x | x <> PosInf} = BIGUNION (IMAGE (\n. {x | x < &n}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (DISCH_TAC \\
         `?n. x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >> METIS_TAC [num_not_infty, lt_infty])
 >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RO_r]);

val BOREL_MEASURABLE_SETS_RO = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_RO", ``!c. {x | x < c} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- REWRITE_TAC [GSYM lt_infty, BOREL_MEASURABLE_SETS_NOT_POSINF]
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RO_r]);

val BOREL_MEASURABLE_SETS_CR_r = prove (
  ``!c. {x | Normal c <= x} IN subsets Borel``,
    RW_TAC std_ss []
 >> `{x | Normal c <= x} = UNIV DIFF {x | x < Normal c}`
      by RW_TAC std_ss [extreal_lt_def, EXTENSION, GSPECIFICATION, DIFF_DEF, IN_UNIV, real_lte]
 >> METIS_TAC [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, sigma_algebra_def, algebra_def,
               BOREL_MEASURABLE_SETS_RO]);

val BOREL_MEASURABLE_SETS_RC_r = prove (
  ``!c. {x | x <= Normal c} IN subsets Borel``,
    RW_TAC std_ss []
 >> `!c. {x | x <= Normal c} = BIGINTER (IMAGE (\n:num. {x | x < Normal (c + (1/2) pow n)}) UNIV)`
         by (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV,IN_INTER]
             >> EQ_TAC
             >- (RW_TAC std_ss [GSPECIFICATION]
                 >> `0:real < (1/2) pow n` by RW_TAC real_ss [REAL_POW_LT]
                 >> Cases_on `x = NegInf` >- METIS_TAC [lt_infty]
                 >> `x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
                 >> `0 < Normal ((1 / 2) pow n)` by METIS_TAC [extreal_lt_eq,extreal_of_num_def]
                 >> RW_TAC std_ss [GSYM extreal_add_def]
                 >> METIS_TAC [extreal_of_num_def,extreal_not_infty,let_add2,add_rzero])
                    >> RW_TAC std_ss [GSPECIFICATION]
                    >> `!n. x < Normal (c + (1 / 2) pow n)` by METIS_TAC []
                    >> `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n)`
                  by RW_TAC real_ss [FUN_EQ_THM]
                    >> `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST]
                    >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
                    >> `(\n. c + (1 / 2) pow n) --> c`
                  by METIS_TAC [Q.SPECL [`(\n. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD,REAL_ADD_RID]
             >> Cases_on `x = NegInf` >- RW_TAC std_ss [le_infty]
             >> `x <> PosInf` by METIS_TAC [lt_infty]
             >> `?r. x = Normal r` by METIS_TAC [extreal_cases]
             >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
             >> METIS_TAC [REAL_LT_IMP_LE,
                           Q.SPECL [`r`,`c`,`(\n. c + (1 / 2) pow n)`] LE_SEQ_IMP_LE_LIM])
 >> FULL_SIMP_TAC std_ss []
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> (MP_TAC o UNDISCH o Q.SPEC `Borel`)
        (INST_TYPE [alpha |-> ``:extreal``] SIGMA_ALGEBRA_FN_BIGINTER)
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!f. P f ==> Q f` (MP_TAC o Q.SPEC `(\n. {x | x < Normal (c + (1 / 2) pow n)})`)
 >> `(\n. {x | x < Normal (c + (1 / 2) pow n)}) IN (UNIV -> subsets Borel)`
        by RW_TAC std_ss [IN_FUNSET,BOREL_MEASURABLE_SETS_RO]
 >> METIS_TAC []);

val BOREL_MEASURABLE_SETS_RC = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_RC", ``!c. {x | x <= c} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [le_infty, BOREL_MEASURABLE_SETS_NEGINF])
 >- (REWRITE_TAC [le_infty, GSPEC_T] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_SPACE, SPACE_BOREL])
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_RC_r]);

val BOREL_MEASURABLE_SETS_OR_r = prove (
  ``!c. {x | Normal c < x} IN subsets Borel``,
    GEN_TAC
 >> `{x | Normal c < x} = UNIV DIFF {x | x <= Normal c}`
     by RW_TAC std_ss [extreal_lt_def, EXTENSION, GSPECIFICATION, DIFF_DEF, IN_UNIV, real_lte]
 >> METIS_TAC [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, sigma_algebra_def, algebra_def,
               BOREL_MEASURABLE_SETS_RC]);

val BOREL_MEASURABLE_SETS_NOT_NEGINF = prove ((* new *)
  ``{x | x <> NegInf} IN subsets Borel``,
    Know `{x | x <> NegInf} = BIGUNION (IMAGE (\n. {x | -(&n) < x}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (DISCH_TAC \\
         `?n. -(&n) <= x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >> METIS_TAC [num_not_infty, lt_infty]) >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OR_r]);

val BOREL_MEASURABLE_SETS_OR = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_OR", ``!c. {x | c < x} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [GSYM lt_infty, BOREL_MEASURABLE_SETS_NOT_NEGINF])
 >- (REWRITE_TAC [lt_infty, GSPEC_F] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OR_r]);

val BOREL_MEASURABLE_SETS_POSINF = prove ((* new *)
  ``{x | x = PosInf} IN subsets Borel``,
    Know `{x | x = PosInf} = BIGINTER (IMAGE (\n. {x | &n < x}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC >- METIS_TAC [num_not_infty, lt_infty, extreal_ainv_def, extreal_of_num_def] \\
     RW_TAC std_ss [] \\
     SPOSE_NOT_THEN ASSUME_TAC \\
     METIS_TAC [SIMP_EXTREAL_ARCH, extreal_lt_def])
 >> Rewr'
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> IMP_RES_TAC SIGMA_ALGEBRA_FN_BIGINTER
 >> POP_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def] >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OR]);

val BOREL_MEASURABLE_SETS_POSINF' = prove ((* new *)
  ``{PosInf} IN subsets Borel``,
    Know `{PosInf} = {x | x = PosInf}`
 >- RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING]
 >> Rewr' >> REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF]);

(* for compatibility with lebesgue_measure_hvgTheory *)
Theorem BOREL_MEASURABLE_INFINITY :
    {PosInf} IN subsets Borel /\ {NegInf} IN subsets Borel
Proof
    REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF',
                 BOREL_MEASURABLE_SETS_NEGINF']
QED

val BOREL_MEASURABLE_SETS_CR = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_CR",
  ``!c. {x | c <= x} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- (REWRITE_TAC [le_infty, GSPEC_T] \\
     PROVE_TAC [SIGMA_ALGEBRA_BOREL, sigma_algebra_def, ALGEBRA_SPACE, SPACE_BOREL])
 >- REWRITE_TAC [le_infty, BOREL_MEASURABLE_SETS_POSINF]
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_CR_r]);

val BOREL_MEASURABLE_SETS_CO_r = prove (
  ``!c d. {x | Normal c <= x /\ x < Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x < Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RO]
 >> `!c. {x | Normal c <= x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_CR]
 >> `{x | Normal c <= x /\ x < Normal d} = {x | Normal c <= x} INTER {x | x < Normal d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_CO_p = prove ((* new *)
  ``!c d. {x | Normal c <= x /\ x < PosInf} IN subsets Borel``,
    rpt GEN_TAC
 >> Know `{x | x < PosInf} IN subsets Borel`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_POSINF]) >> DISCH_TAC
 >> `!c. {x | Normal c <= x} IN subsets Borel` by REWRITE_TAC [BOREL_MEASURABLE_SETS_CR]
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> `!c. {x | Normal c <= x} INTER {x | x < PosInf} IN subsets Borel`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `{x | Normal c <= x /\ x < PosInf} = {x | Normal c <= x} INTER {x | x < PosInf}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> POP_ORW
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val BOREL_MEASURABLE_SETS_CO = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_CO",
  ``!c d. {x | c <= x /\ x < d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_POSINF])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_RO])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     SIMP_TAC std_ss [GSYM lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= x /\ x < Normal r <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_CO_p])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_CO_r]);

val BOREL_MEASURABLE_SETS_OC_r = prove (
  ``!c d. {x | Normal c < x /\ x <= Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x <= Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RC]
 >> `!c. {x | Normal c < x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_OR]
 >> `{x | Normal c < x /\ x <= Normal d} = {x | Normal c < x} INTER {x | x <= Normal d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_OC_n = prove ((* new *)
  ``!d. {x | NegInf < x /\ x <= Normal d} IN subsets Borel``,
    GEN_TAC
 >> `!d. {x | x <= Normal d} IN subsets Borel` by REWRITE_TAC [BOREL_MEASURABLE_SETS_RC]
 >> Know `{x | NegInf < x} IN subsets Borel`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_NEGINF]) >> DISCH_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> `!d. ({x | NegInf < x} INTER {x | x <= Normal d}) IN subsets Borel`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `{x | NegInf < x /\ x <= Normal d} = {x | NegInf < x} INTER {x | x <= Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> POP_ORW
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_OC = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_OC",
  ``!c d. {x | c < x /\ x <= d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     `!x. NegInf < x /\ x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NOT_NEGINF])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OC_n])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r < x /\ x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OR])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OC_r]);

val BOREL_MEASURABLE_SETS_CC_r = prove (
  ``!c d. {x | Normal c <= x /\ x <= Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x <= Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RC]
 >> `!c. {x | Normal c <= x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_CR]
 >> `{x | Normal c <= x /\ x <= Normal d} = {x | Normal c <= x} INTER {x | x <= Normal d}`
        by  RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_CC = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_CC", ``!c d. {x | c <= x /\ x <= d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [le_infty, GSPEC_T] \\
     METIS_TAC [sigma_algebra_def, ALGEBRA_SPACE, SPACE_BOREL])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_RC])
 >- ((* goal 4 (of 9) *)
     `!x. PosInf <= x /\ x <= NegInf <=> F`
        by METIS_TAC [le_infty, lt_infty, extreal_not_infty, extreal_cases] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF])
 >- ((* goal 6 (of 9) *)
     `!x. PosInf <= x /\ x <= Normal r <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     `!x. Normal r <= x /\ x <= NegInf <=> F`
       by METIS_TAC [lt_infty, le_infty, extreal_not_infty, lt_imp_ne] \\
     POP_ORW >> REWRITE_TAC [GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [le_infty] \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_CR])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_CC_r]);

val BOREL_MEASURABLE_SETS_OO_r = prove ((* not "00_r" *)
  ``!c d. {x | Normal c < x /\ x < Normal d} IN subsets Borel``,
    rpt GEN_TAC
 >> `!d. {x | x < Normal d} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_RO]
 >> `!c. {x | Normal c < x} IN subsets Borel` by METIS_TAC [BOREL_MEASURABLE_SETS_OR]
 >> `{x | Normal c < x /\ x < Normal d} = {x | Normal c < x} INTER {x | x < Normal d}`
       by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, SIGMA_ALGEBRA_BOREL]);

val BOREL_MEASURABLE_SETS_OO_np = prove ((* new, not "00_np" *)
  ``{x | NegInf < x /\ x < PosInf} IN subsets Borel``,
    ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Know `{x | NegInf < x /\ x < PosInf} =
          BIGUNION (IMAGE (\n. {x | -&n < x /\ x < &n}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n1. -&n1 <= x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         `?n2. x <= &n2` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC (MAX n1 n2)` \\
         CONJ_TAC >- (MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n1` >> art [] \\
                      SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
                      MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
                      REWRITE_TAC [MAX_LE] >> DISJ1_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n2` >> art [] \\
         SIMP_TAC std_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT] \\
         MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC \\
         REWRITE_TAC [MAX_LE] >> DISJ2_TAC >> REWRITE_TAC [LESS_EQ_REFL]) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_OO_n = prove ((* new, not "00_n" *)
  ``!d. {x | NegInf < x /\ x < Normal d} IN subsets Borel``,
    GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Know `{x | NegInf < x /\ x < Normal d} =
          BIGUNION (IMAGE (\n. {x | -&n < x /\ x < Normal d}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. -&n <= x` by PROVE_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC `-&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       ASM_REWRITE_TAC [] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `-&n = Normal (-&n)` by PROVE_TAC [extreal_ainv_def, extreal_of_num_def]
 >> ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_OO_p = prove ((* new, not "00_p" *)
  ``!c. {x | Normal c < x /\ x < PosInf} IN subsets Borel``,
    GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Know `{x | Normal c < x /\ x < PosInf} =
          BIGUNION (IMAGE (\n. {x | Normal c < x /\ x < &n}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, GSPECIFICATION] \\
     EQ_TAC
     >- (RW_TAC std_ss [GSYM lt_infty] \\
         `?n. x <= &n` by PROVE_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC `SUC n` \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `&n` >> art [] \\
         SIMP_TAC arith_ss [lt_neg, extreal_of_num_def, extreal_lt_eq, REAL_LT]) \\
     RW_TAC std_ss [] >| (* 3 subgoals *)
     [ METIS_TAC [num_not_infty, lt_infty],
       METIS_TAC [num_not_infty, lt_infty] ])
 >> Rewr'
 >> fs [SIGMA_ALGEBRA_FN]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `&n = Normal (&n)` by PROVE_TAC [extreal_of_num_def]
 >> ASM_REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_OO = store_thm (* new, not "00" *)
  ("BOREL_MEASURABLE_SETS_OO", ``!c d. {x | c < x /\ x < d} IN subsets Borel``,
    rpt GEN_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 2 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_np])
 >- ((* goal 3 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_n])
 >- ((* goal 4 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 5 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 6 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 7 (of 9) *)
     REWRITE_TAC [GSYM lt_infty, le_infty, GSPEC_F] \\
     fs [sigma_algebra_def, ALGEBRA_EMPTY])
 >- ((* goal 8 (of 9) *)
     REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_p])
 (* goal 9 (of 9) *)
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_OO_r]);

val BOREL_MEASURABLE_SETS_SING_r = prove (
  ``!c. {Normal c} IN subsets Borel``,
    RW_TAC std_ss []
 >> Know `!c. {Normal c} = BIGINTER (IMAGE (\n. {x | Normal (c - ((1/2) pow n)) <= x /\
                                                     x < Normal (c + ((1/2) pow n))}) UNIV)`
 >- (RW_TAC std_ss [EXTENSION, IN_BIGINTER_IMAGE, IN_UNIV, IN_SING, IN_INTER] \\
     EQ_TAC >- RW_TAC real_ss [extreal_lt_eq, extreal_le_def, GSPECIFICATION,
                               REAL_POW_LT, REAL_LT_IMP_LE, REAL_LT_ADDR, REAL_LT_DIV,
                               HALF_POS, REAL_LT_ADDNEG2, real_sub, IN_INTER] \\
     RW_TAC std_ss [GSPECIFICATION] \\
    `!n. Normal (c - (1/2) pow n) <= x` by FULL_SIMP_TAC real_ss [real_sub] \\
    `!n. x <= Normal (c + (1/2) pow n)` by FULL_SIMP_TAC real_ss [lt_imp_le] \\
    `(\n. c - (1/2) pow n) = (\n. (\n. c) n - (\n. (1/2) pow n) n)`
       by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c + (1/2) pow n) = (\n. (\n. c) n + (\n. (1/2) pow n) n)`
       by RW_TAC real_ss [FUN_EQ_THM] \\
    `(\n. c) --> c` by RW_TAC std_ss [SEQ_CONST] \\
    `(\n. (1/2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER] \\
    `(\n. c - (1/2) pow n) --> c`
       by METIS_TAC [Q.SPECL [`(\n. c)`, `c`, `(\n. (1/2) pow n)`, `0`] SEQ_SUB, REAL_SUB_RZERO] \\
    `(\n. c + (1/2) pow n) --> c`
       by METIS_TAC [Q.SPECL [`(\n. c)`, `c`, `(\n. (1/2) pow n)`, `0`] SEQ_ADD, REAL_ADD_RID] \\
    `x <> PosInf` by METIS_TAC [lt_infty] \\
    `x <> NegInf` by METIS_TAC [le_infty, extreal_not_infty] \\
    `?r. x = Normal r` by METIS_TAC [extreal_cases] \\
     FULL_SIMP_TAC std_ss [extreal_le_def, extreal_lt_eq, extreal_11] \\
    `c <= r` by METIS_TAC [Q.SPECL [`r`, `c`, `(\n. c - (1/2) pow n)`] SEQ_LE_IMP_LIM_LE] \\
    `r <= c` by METIS_TAC [Q.SPECL [`r`, `c`, `(\n. c + (1/2) pow n)`] LE_SEQ_IMP_LE_LIM] \\
     METIS_TAC [REAL_LE_ANTISYM]) >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> (MP_TAC o UNDISCH o Q.SPEC `Borel` o (INST_TYPE [alpha |-> ``:extreal``]))
      SIGMA_ALGEBRA_FN_BIGINTER
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM `!f. P f ==> Q f`
     (MP_TAC o
      Q.SPEC `(\n. {x | Normal (c - ((1/2) pow n)) <= x /\ x < Normal (c + ((1/2) pow n))})`)
 >> `(\n. {x | Normal (c - ((1/2) pow n)) <= x /\
               x < Normal (c + ((1/2) pow n))}) IN (UNIV -> subsets Borel)`
     by RW_TAC std_ss [IN_FUNSET, BOREL_MEASURABLE_SETS_CO]
 >> METIS_TAC []);

val BOREL_MEASURABLE_SETS_SING = store_thm (* was: BOREL_MEASURABLE_SING *)
  ("BOREL_MEASURABLE_SETS_SING", ``!c. {c} IN subsets Borel``,
    GEN_TAC >> Cases_on `c`
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF']
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF']
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_SING_r]);

val BOREL_MEASURABLE_SETS_SING' = store_thm (* new *)
  ("BOREL_MEASURABLE_SETS_SING'", ``!c. {x | x = c} IN subsets Borel``,
    GEN_TAC
 >> `{x | x = c} = {c}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING]
 >> POP_ORW >> Cases_on `c`
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF']
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF']
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_SING_r]);

val BOREL_MEASURABLE_SETS_NOT_SING = store_thm
  ("BOREL_MEASURABLE_SETS_NOT_SING", ``!c. {x | x <> c} IN subsets Borel``,
    RW_TAC std_ss []
 >> `{x | x <> c} = (space Borel) DIFF ({c})`
      by RW_TAC std_ss [SPACE_BOREL, EXTENSION, IN_DIFF, IN_SING, GSPECIFICATION, IN_UNIV]
 >> POP_ORW
 >> METIS_TAC [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS_SING,
               sigma_algebra_def, algebra_def]);

(* For backwards compatibilities *)
val BOREL_MEASURABLE_SETS1 = save_thm
  ("BOREL_MEASURABLE_SETS1", BOREL_MEASURABLE_SETS_RO);
val BOREL_MEASURABLE_SETS2 = save_thm
  ("BOREL_MEASURABLE_SETS2", BOREL_MEASURABLE_SETS_CR);
val BOREL_MEASURABLE_SETS3 = save_thm
  ("BOREL_MEASURABLE_SETS3", BOREL_MEASURABLE_SETS_RC);
val BOREL_MEASURABLE_SETS4 = save_thm
  ("BOREL_MEASURABLE_SETS4", BOREL_MEASURABLE_SETS_OR);
val BOREL_MEASURABLE_SETS5 = save_thm
  ("BOREL_MEASURABLE_SETS5", BOREL_MEASURABLE_SETS_CO);
val BOREL_MEASURABLE_SETS6 = save_thm
  ("BOREL_MEASURABLE_SETS6", BOREL_MEASURABLE_SETS_OC);
val BOREL_MEASURABLE_SETS7 = save_thm
  ("BOREL_MEASURABLE_SETS7", BOREL_MEASURABLE_SETS_CC);
val BOREL_MEASURABLE_SETS8 = save_thm
  ("BOREL_MEASURABLE_SETS8", BOREL_MEASURABLE_SETS_OO);
val BOREL_MEASURABLE_SETS9 = save_thm
  ("BOREL_MEASURABLE_SETS9", BOREL_MEASURABLE_SETS_SING);
val BOREL_MEASURABLE_SETS10 = save_thm
  ("BOREL_MEASURABLE_SETS10", BOREL_MEASURABLE_SETS_NOT_SING);

(* A summary of all Borel-measurable sets *)
val BOREL_MEASURABLE_SETS = store_thm
  ("BOREL_MEASURABLE_SETS",
  ``(!c. {x | x < c} IN subsets Borel) /\
    (!c. {x | c < x} IN subsets Borel) /\
    (!c. {x | x <= c} IN subsets Borel) /\
    (!c. {x | c <= x} IN subsets Borel) /\
    (!c d. {x | c <= x /\ x < d} IN subsets Borel) /\
    (!c d. {x | c < x /\ x <= d} IN subsets Borel) /\
    (!c d. {x | c <= x /\ x <= d} IN subsets Borel) /\
    (!c d. {x | c < x /\ x < d} IN subsets Borel) /\
    (!c. {c} IN subsets Borel) /\
    (!c. {x | x <> c} IN subsets Borel)``,
 (* proof *)
    RW_TAC std_ss [BOREL_MEASURABLE_SETS_RO, (*         x < c *)
                   BOREL_MEASURABLE_SETS_OR, (* c < x         *)
                   BOREL_MEASURABLE_SETS_RC, (*         x <= c *)
                   BOREL_MEASURABLE_SETS_CR, (* c <= x         *)
                   BOREL_MEASURABLE_SETS_CO, (* c <= x /\ x < d *)
                   BOREL_MEASURABLE_SETS_OC, (* c < x /\ x <= d *)
                   BOREL_MEASURABLE_SETS_CC, (* c <= x /\ x <= d *)
                   BOREL_MEASURABLE_SETS_OO, (* c < x /\ x < d *)
                   BOREL_MEASURABLE_SETS_SING,       (* x = c *)
                   BOREL_MEASURABLE_SETS_NOT_SING]); (* x <> c *)


(* ******************************************* *)
(*        Borel measurable functions           *)
(* ******************************************* *)

val IN_MEASURABLE_BOREL_CONST = store_thm
  ("IN_MEASURABLE_BOREL_CONST",
  ``!a k f. sigma_algebra a /\ (!x. x IN space a ==> (f x = k)) ==> f IN measurable a Borel``,
 (* proof *)
    RW_TAC std_ss [IN_MEASURABLE_BOREL,IN_FUNSET, IN_UNIV]
 >> Cases_on `Normal c <= k`
 >- (`{x | f x < Normal c} INTER space a = {}`
         by  (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER]
              >> METIS_TAC [extreal_lt_def])
      >> METIS_TAC [sigma_algebra_def,algebra_def])
 >> `{x | f x < Normal c} INTER space a = space a`
      by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
          >> METIS_TAC [extreal_lt_def])
 >> METIS_TAC [sigma_algebra_def,algebra_def,INTER_IDEMPOT,DIFF_EMPTY]);

Theorem IN_MEASURABLE_BOREL_CONST' :
    !a k. sigma_algebra a ==> (\x. k) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
 >> Q.EXISTS_TAC `k` >> RW_TAC std_ss []
QED

val IN_MEASURABLE_BOREL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_INDICATOR",
  ``!a A f. sigma_algebra a /\ A IN subsets a /\
           (!x. x IN space a ==> (f x = indicator_fn A x))
        ==> f IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL]
 >- RW_TAC std_ss [IN_FUNSET,UNIV_DEF,indicator_fn_def,IN_DEF]
 >> `!x. x IN space a ==> 0 <= f x /\ f x <= 1` by RW_TAC real_ss [indicator_fn_def,le_01,le_refl]
 >> Cases_on `Normal c <= 0`
 >- (`{x | f x < Normal c} INTER space a = {}`
      by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER,extreal_lt_def]
          >> METIS_TAC [le_trans])
      >> METIS_TAC [sigma_algebra_def,algebra_def,DIFF_EMPTY])
 >> Cases_on `1 < Normal c`
 >- (`{x | f x < Normal c} INTER space a = space a`
        by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER]
            >> METIS_TAC [let_trans])
     >> METIS_TAC [sigma_algebra_def,algebra_def,DIFF_EMPTY])
 >> `{x | f x < Normal c} INTER space a = (space a) DIFF A`
        by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER,IN_DIFF]
            >> FULL_SIMP_TAC std_ss [extreal_lt_def,indicator_fn_def]
            >> METIS_TAC [extreal_lt_def])
 >> METIS_TAC [sigma_algebra_def,algebra_def,DIFF_EMPTY]);

val IN_MEASURABLE_BOREL_CMUL = store_thm
  ("IN_MEASURABLE_BOREL_CMUL",
  ``!a f g z. sigma_algebra a /\ f IN measurable a Borel /\
             (!x. x IN space a ==> (g x = Normal z * f x))
          ==> g IN measurable a Borel``,
    RW_TAC std_ss []
 >> Cases_on `Normal z = 0`
 >- METIS_TAC [IN_MEASURABLE_BOREL_CONST, mul_lzero]
 >> Cases_on `0 < Normal z`
 >- (RW_TAC real_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV] \\
    `!c. {x | g x < Normal c} INTER space a = {x | f x < Normal (c) / Normal z} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
          METIS_TAC [lt_rdiv, mul_comm, extreal_of_num_def, extreal_lt_eq]) \\
     METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_div_eq, extreal_of_num_def, extreal_11])
 >> `z < 0` by METIS_TAC [extreal_lt_def, extreal_le_def, extreal_of_num_def,
                          REAL_LT_LE, GSYM real_lte]
 >> RW_TAC real_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> `!c. {x | g x < Normal c} INTER space a = {x | Normal c / Normal z < f x} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
          METIS_TAC [lt_rdiv_neg, mul_comm])
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_div_eq, REAL_LT_IMP_NE]);

Theorem IN_MEASURABLE_BOREL_MINUS :
    !a f g. sigma_algebra a /\ f IN measurable a Borel /\
           (!x. x IN space a ==> (g x = -f x)) ==> g IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> qexistsl_tac [`f`, `-1`]
 >> RW_TAC std_ss [Once neg_minus1]
 >> REWRITE_TAC [extreal_of_num_def, extreal_ainv_def]
QED

val IN_MEASURABLE_BOREL_ABS = store_thm
  ("IN_MEASURABLE_BOREL_ABS",
  ``!a f g. sigma_algebra a /\ f IN measurable a Borel /\
            (!x. x IN space a ==> (g x = abs (f x)))
         ==> g IN measurable a Borel``,
    RW_TAC real_ss [IN_MEASURABLE_BOREL,IN_UNIV,IN_FUNSET]
 >> Cases_on `c <= 0`
 >- (`{x | g x < Normal c} INTER space a = {}`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, NOT_IN_EMPTY, GSYM real_lte] \\
            METIS_TAC [abs_pos, le_trans, extreal_le_def, extreal_of_num_def, extreal_lt_def]) \\
     METIS_TAC [sigma_algebra_def, algebra_def])
 >> FULL_SIMP_TAC real_ss [GSYM real_lt]
 >> Suff `{x | g x < Normal c} INTER space a =
          ({x | f x < Normal c} INTER space a) INTER ({x | Normal (-c) < f x} INTER space a)`
 >- (Rewr' \\
     METIS_TAC [sigma_algebra_def, ALGEBRA_INTER, IN_MEASURABLE_BOREL_ALL,
               IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV])
 >> RW_TAC real_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> EQ_TAC
 >- (RW_TAC std_ss []
     >- (`abs (f x) < Normal c` by METIS_TAC [] \\
         Cases_on `f x` >| (* 3 subgoals *)
         [ METIS_TAC [lt_infty],
           METIS_TAC [extreal_abs_def, lt_infty, extreal_not_infty],
          `g x = Normal (abs r)` by METIS_TAC [extreal_abs_def] \\
           FULL_SIMP_TAC std_ss [extreal_lt_eq] \\
           METIS_TAC [REAL_ADD_LID, REAL_SUB_RZERO, ABS_BETWEEN] ]) \\
     Cases_on `f x` >| (* 3 subgoals *)
     [ METIS_TAC [extreal_abs_def, lt_infty],
       METIS_TAC [lt_infty],
      `g x = Normal (abs r)` by METIS_TAC [extreal_abs_def] \\
       FULL_SIMP_TAC std_ss [extreal_lt_eq] \\
       METIS_TAC [REAL_ADD_LID, REAL_SUB_LZERO, REAL_SUB_RZERO, ABS_BETWEEN] ])
 >> RW_TAC std_ss []
 >> `f x <> NegInf` by METIS_TAC [lt_infty]
 >> `f x <> PosInf` by METIS_TAC [lt_infty]
 >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
 >> FULL_SIMP_TAC std_ss [extreal_abs_def, extreal_lt_eq, extreal_le_def]
 >> `r = r - 0` by PROVE_TAC [REAL_SUB_RZERO] >> POP_ORW
 >> REWRITE_TAC [GSYM ABS_BETWEEN]
 >> ASM_REWRITE_TAC [REAL_ADD_LID, REAL_SUB_LZERO, REAL_SUB_RZERO]
 >> METIS_TAC [REAL_LET_ANTISYM, REAL_NOT_LE]);

Theorem IN_MEASURABLE_BOREL_ABS' :
    !a f. sigma_algebra a /\ f IN measurable a Borel ==> (abs o f) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS
 >> Q.EXISTS_TAC `f` >> RW_TAC std_ss [o_DEF]
QED

val IN_MEASURABLE_BOREL_SQR = store_thm
  ("IN_MEASURABLE_BOREL_SQR",
  ``!a f g. sigma_algebra a /\ f IN measurable a Borel /\
            (!x. x IN space a ==> (g x = (f x) pow 2))
        ==> g IN measurable a Borel``,
  RW_TAC real_ss []
  >> `!c. {x | f x <= Normal c} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
  >> `!c. {x | Normal c <= f x} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
  >> RW_TAC real_ss [IN_UNIV,IN_FUNSET,IN_MEASURABLE_BOREL_ALT2]
  >> Cases_on `Normal c < 0`
  >- (`{x | g x <= Normal c} INTER space a = {}`
          by ( RW_TAC real_ss [EXTENSION,GSPECIFICATION,NOT_IN_EMPTY,IN_INTER,GSYM real_lt]
             >> METIS_TAC [le_pow2,lte_trans,extreal_lt_def])
      >> METIS_TAC [sigma_algebra_def,algebra_def])
  >> FULL_SIMP_TAC real_ss [extreal_lt_def]
  >> `{x | g x <= Normal c} INTER space a =
        ({x | f x <= sqrt (Normal c)} INTER space a) INTER
        ({x | - (sqrt (Normal c)) <= f x} INTER space a)`
        by (RW_TAC real_ss [EXTENSION,GSPECIFICATION,IN_INTER]
            >> EQ_TAC
            >- (RW_TAC real_ss []
                >- (Cases_on `f x < 0` >- METIS_TAC [lte_trans,lt_imp_le,sqrt_pos_le]
                         >> METIS_TAC [pow2_sqrt,sqrt_mono_le,le_pow2,extreal_lt_def])
                     >> Cases_on `0 <= f x` >- METIS_TAC [le_trans,le_neg,sqrt_pos_le,neg_0]
                >> SPOSE_NOT_THEN ASSUME_TAC
                >> FULL_SIMP_TAC real_ss [GSYM extreal_lt_def]
                >> `sqrt (Normal c) < - (f x)` by METIS_TAC [lt_neg,neg_neg]
                >> `(sqrt (Normal c)) pow 2 < (- (f x)) pow 2` by RW_TAC real_ss [pow_lt2,sqrt_pos_le]
                >> `(sqrt (Normal c)) pow 2 = Normal c` by METIS_TAC [sqrt_pow2]
                >> `(-1) pow 2 = 1` by METIS_TAC [pow_minus1,MULT_RIGHT_1]
                >> `(- (f x)) pow 2 = (f x) pow 2` by RW_TAC std_ss [Once neg_minus1,pow_mul,mul_lone]
                >> METIS_TAC [extreal_lt_def])
            >> RW_TAC std_ss []
            >> Cases_on `0 <= f x` >- METIS_TAC [pow_le,sqrt_pow2]
            >> FULL_SIMP_TAC real_ss [GSYM extreal_lt_def]
            >> `- (f x) <= sqrt (Normal c)` by METIS_TAC [le_neg,neg_neg]
            >> `(- (f x)) pow 2 <= (sqrt (Normal c)) pow 2`
               by METIS_TAC [pow_le, sqrt_pos_le, lt_neg, neg_neg, neg_0, lt_imp_le]
            >> `(sqrt (Normal c)) pow 2 = Normal c` by METIS_TAC [sqrt_pow2]
            >> `(-1) pow 2 = 1` by METIS_TAC [pow_minus1,MULT_RIGHT_1]
            >> `(- (f x)) pow 2 = (f x) pow 2` by RW_TAC std_ss [Once neg_minus1,pow_mul,mul_lone]
            >> METIS_TAC [])
  >> METIS_TAC [sigma_algebra_def,ALGEBRA_INTER,extreal_sqrt_def,extreal_ainv_def]);

(* enhanced with more general antecedents, old:

      (!x. x IN space a ==> (f x <> NegInf /\ g x <> NegInf))

   new:

      (!x. x IN space a ==> (f x <> NegInf /\ g x <> NegInf) \/
                            (f x <> PosInf /\ g x <> PosInf))
 *)
Theorem IN_MEASURABLE_BOREL_ADD :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
              (!x. x IN space a ==> (f x <> NegInf /\ g x <> NegInf) \/
                                    (f x <> PosInf /\ g x <> PosInf)) /\
              (!x. x IN space a ==> (h x = f x + g x))
          ==> h IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL] >- RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> Know `!c. {x | h x < Normal c} INTER (space a) =
              BIGUNION (IMAGE (\r. {x | f x < r /\ r < Normal c - g x} INTER space a) Q_set)`
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER] \\
     EQ_TAC >- (RW_TAC std_ss [] \\
                MATCH_MP_TAC Q_DENSE_IN_R \\
                METIS_TAC [lt_sub_imp, lt_sub_imp']) \\
     reverse (RW_TAC std_ss []) >- art [] \\
    ‘h x = f x + g x’ by PROVE_TAC [] >> POP_ORW \\
    ‘f x < Normal c - g x’ by PROVE_TAC [lt_trans] \\
     Q.PAT_X_ASSUM ‘!x. x IN space a ==> P \/ Q’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ METIS_TAC [lt_sub , extreal_not_infty],
       METIS_TAC [lt_sub', extreal_not_infty] ])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC BIGUNION_IMAGE_Q
 >> RW_TAC std_ss [IN_FUNSET]
 >> `?y. r = Normal y` by METIS_TAC [Q_not_infty, extreal_cases]
 >> `{x | f x < Normal y /\ Normal y < Normal c - g x} =
     {x | f x < Normal y} INTER {x | Normal y < Normal c - g x}`
     by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> `({x | f x < Normal y} INTER space a) IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_ALL]
 >> Know `!x. x IN space a ==> (Normal y < Normal c - g x <=> g x < Normal c - Normal y)`
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!x. x IN space a ==> P \/ Q’ (MP_TAC o (Q.SPEC ‘x’)) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ METIS_TAC [lt_sub , extreal_not_infty, add_comm],
       METIS_TAC [lt_sub', extreal_not_infty, add_comm] ])
 >> DISCH_TAC
 >> `{x | Normal y < Normal c - g x} INTER space a = {x | g x < Normal c - Normal y} INTER space a`
     by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION] >> METIS_TAC [])
 >> `({x | Normal y < Normal c - g x} INTER space a) IN subsets a`
     by METIS_TAC [IN_MEASURABLE_BOREL_ALL, extreal_sub_def]
 >> `({x | f x < Normal y} INTER space a) INTER ({x | Normal y < Normal c - g x} INTER space a) =
     ({x | f x < Normal y} INTER {x | Normal y < Normal c - g x} INTER space a)`
     by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
         EQ_TAC >> RW_TAC std_ss [])
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
QED

(* enhanced with more general antecedents, old:

             (!x. x IN space a ==> (f x <> NegInf /\ g x <> PosInf))

   new:
             (!x. x IN space a ==> (f x <> NegInf /\ g x <> PosInf) \/
                                   (f x <> PosInf /\ g x <> NegInf))
 *)
Theorem IN_MEASURABLE_BOREL_SUB :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
             (!x. x IN space a ==> (f x <> NegInf /\ g x <> PosInf) \/
                                   (f x <> PosInf /\ g x <> NegInf)) /\
             (!x. x IN space a ==> (h x = f x - g x))
          ==> h IN measurable a Borel
Proof
    RW_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
 >> qexistsl_tac [`f`, `\x. - g x`]
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL \\
      Q.EXISTS_TAC `g` \\
      Q.EXISTS_TAC `-1` \\
      RW_TAC std_ss [GSYM extreal_ainv_def, GSYM extreal_of_num_def, GSYM neg_minus1],
      (* goal 2 (of 3) *)
      METIS_TAC [extreal_ainv_def, neg_neg],
      (* goal 3 (of 3) *)
      Cases_on `f x` >> Cases_on `g x` \\
      METIS_TAC [le_infty, extreal_ainv_def, extreal_sub_def, extreal_add_def, real_sub] ]
QED

(* cf. IN_MEASURABLE_BOREL_TIMES for a more general version *)
Theorem IN_MEASURABLE_BOREL_MUL :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
             (!x. x IN space a ==> (h x = f x * g x)) /\
             (!x. x IN space a ==> f x <> NegInf /\ f x <> PosInf /\
                                   g x <> NegInf /\ g x <> PosInf)
          ==> h IN measurable a Borel
Proof
    RW_TAC std_ss []
 >> `!x. x IN space a ==> (f x * g x = 1 / 2 * ((f x + g x) pow 2 - f x pow 2 - g x pow 2))`
 by (RW_TAC std_ss [] \\
     (MP_TAC o Q.SPECL [`f x`, `g x`]) add_pow2 \\
     RW_TAC std_ss [] \\
    `?r. f x = Normal r` by METIS_TAC [extreal_cases] \\
    `?r. g x = Normal r` by METIS_TAC [extreal_cases] \\
     FULL_SIMP_TAC real_ss [extreal_11, extreal_pow_def, extreal_add_def, extreal_sub_def,
                            extreal_of_num_def, extreal_mul_def, extreal_div_eq] \\
    `r pow 2 + r' pow 2 + 2 * r * r' - r pow 2 - r' pow 2 = 2 * r * r'` by REAL_ARITH_TAC \\
     RW_TAC real_ss [REAL_MUL_ASSOC])
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2 - g x pow 2)`
 >> Q.EXISTS_TAC `1 / 2`
 >> RW_TAC real_ss [extreal_of_num_def, extreal_div_eq]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> Q.EXISTS_TAC `(\x. (f x + g x) pow 2 - f x pow 2)`
 >> Q.EXISTS_TAC `(\x. g x pow 2)`
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB \\
      Q.EXISTS_TAC `(\x. (f x + g x) pow 2)` \\
      Q.EXISTS_TAC `(\x. f x pow 2)` \\
      RW_TAC std_ss [] >| (* 3 subgoals *)
      [ (* goal 1.1 (of 3) *)
        MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR \\
        Q.EXISTS_TAC `(\x. (f x + g x))` \\
        RW_TAC std_ss [] \\
        MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD \\
        qexistsl_tac [`f`, `g`] \\
        RW_TAC std_ss [],
        (* goal 1.2 (of 3) *)
        MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR >> METIS_TAC [],
        (* goal 1.3 (of 3) *)
        METIS_TAC [add_not_infty,pow_not_infty] ],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_SQR >> METIS_TAC [],
      (* goal 3 (of 3) *)
      DISJ1_TAC \\
      METIS_TAC [add_not_infty, pow_not_infty, sub_not_infty] ]
QED

val IN_MEASURABLE_BOREL_SUM = store_thm
  ("IN_MEASURABLE_BOREL_SUM",
  ``!a f g s. FINITE s /\ sigma_algebra a /\
              (!i. i IN s ==> (f i) IN measurable a Borel) /\
              (!i x. i IN s /\ x IN space a ==> f i x <> NegInf) /\
              (!x. x IN space a ==> (g x = SIGMA (\i. (f i) x) s)) ==>
                 g IN measurable a Borel``,
    Suff `!s:'b -> bool. FINITE s ==>
            (\s:'b -> bool. !a f g. FINITE s /\ sigma_algebra a /\
                (!i. i IN s ==> f i IN measurable a Borel) /\
                (!i x. i IN s /\ x IN space a ==> f i x <> NegInf) /\
                (!x. x IN space a ==> (g x = SIGMA (\i. f i x) s)) ==>
                   g IN measurable a Borel) s`
 >- METIS_TAC []
 >> MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [EXTREAL_SUM_IMAGE_EMPTY,NOT_IN_EMPTY]
 >- METIS_TAC [IN_MEASURABLE_BOREL_CONST]
 >> `!x. x IN space a ==> (SIGMA (\i. f i x) (e INSERT s) = f e x + SIGMA (\i. f i x) (s DELETE e))`
        by (RW_TAC std_ss [] \\
            (MP_TAC o Q.SPEC `e` o UNDISCH o Q.SPECL [`(\i. f i x)`,`s`] o
                INST_TYPE [alpha |-> beta]) EXTREAL_SUM_IMAGE_PROPERTY \\
            RW_TAC std_ss [])
 >> FULL_SIMP_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD
 >> Q.EXISTS_TAC `f e`
 >> Q.EXISTS_TAC `(\x. SIGMA (\i. f i x) s)`
 >> FULL_SIMP_TAC std_ss [IN_INSERT, DELETE_NON_ELEMENT, EXTREAL_SUM_IMAGE_NOT_INFTY]
 >> Q.PAT_X_ASSUM `!a f g. P ==> g IN measurable a Borel` MATCH_MP_TAC
 >> Q.EXISTS_TAC `f`
 >> RW_TAC std_ss []);

val IN_MEASURABLE_BOREL_CMUL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_CMUL_INDICATOR",
  ``!a z s. sigma_algebra a /\ s IN subsets a
        ==> (\x. Normal z * indicator_fn s x) IN measurable a Borel``,
    RW_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> Q.EXISTS_TAC `indicator_fn s`
 >> Q.EXISTS_TAC `z`
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_INDICATOR
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_MUL_INDICATOR = store_thm
  ("IN_MEASURABLE_BOREL_MUL_INDICATOR",
  ``!a f s. sigma_algebra a /\ f IN measurable a Borel /\ s IN subsets a ==>
            (\x. f x * indicator_fn s x) IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2, IN_FUNSET, IN_UNIV]
 >> Cases_on `0 <= Normal c`
 >- (`{x | f x * indicator_fn s x <= Normal c} INTER space a =
      (({x | f x <= Normal c} INTER space a) INTER s) UNION (space a DIFF s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER,
                            IN_UNION, IN_DIFF] \\
             Cases_on `x IN s` >- RW_TAC std_ss [mul_rone, mul_rzero] \\
             RW_TAC std_ss [mul_rone, mul_rzero]) >> POP_ORW \\
     MATCH_MP_TAC ALGEBRA_UNION \\
     CONJ_TAC >- FULL_SIMP_TAC std_ss [sigma_algebra_def] \\
     reverse CONJ_TAC >- FULL_SIMP_TAC std_ss [sigma_algebra_def, algebra_def] \\
     MATCH_MP_TAC ALGEBRA_INTER \\
     FULL_SIMP_TAC std_ss [sigma_algebra_def])
 >> `{x | f x * indicator_fn s x <= Normal c} INTER space a =
     (({x | f x <= Normal c} INTER space a) INTER s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER] \\
             Cases_on `x IN s` >- RW_TAC std_ss [mul_rone, mul_rzero] \\
             RW_TAC std_ss [mul_rone, mul_rzero]) >> POP_ORW
 >> MATCH_MP_TAC ALGEBRA_INTER
 >> FULL_SIMP_TAC std_ss [sigma_algebra_def]);

Theorem IN_MEASURABLE_BOREL_CMUL_INDICATOR' :
    !a c s. sigma_algebra a /\ s IN subsets a ==>
            (\x. c * indicator_fn s x) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘a’, ‘\x. c’, ‘s’] IN_MEASURABLE_BOREL_MUL_INDICATOR) >> rw []
 >> POP_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST' >> art []
QED

val IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ = store_thm
  ("IN_MEASURABLE_BOREL_MUL_INDICATOR_EQ",
  ``!a f. sigma_algebra a ==>
         (f IN measurable a Borel <=> (\x. f x * indicator_fn (space a) x) IN measurable a Borel)``,
    RW_TAC std_ss []
 >> EQ_TAC >- METIS_TAC [IN_MEASURABLE_BOREL_MUL_INDICATOR, ALGEBRA_SPACE, sigma_algebra_def]
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_UNIV, IN_FUNSET]
 >> `{x | f x < Normal c} INTER space a =
     {x | f x * indicator_fn (space a) x < Normal c} INTER space a`
       by (RW_TAC std_ss [IN_INTER, EXTENSION, GSPECIFICATION, indicator_fn_def,
                          mul_rzero, mul_rone]
           >> METIS_TAC [mul_rzero, mul_rone])
 >> POP_ORW >> art []);

val IN_MEASURABLE_BOREL_POW = store_thm
  ("IN_MEASURABLE_BOREL_POW",
  ``!n a f. sigma_algebra a /\ f IN measurable a Borel /\
            (!x. x IN space a ==> f x <> NegInf /\ f x <> PosInf)
        ==> (\x. (f x) pow n) IN measurable a Borel``,
    Induct >- (RW_TAC std_ss [pow_0] \\
               MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
               METIS_TAC [])
 >> RW_TAC std_ss []
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL
 >> Q.EXISTS_TAC `f`
 >> Q.EXISTS_TAC `(\x. f x pow n)`
 >> RW_TAC std_ss [pow_not_infty]
 >> METIS_TAC [pow_add, ADD1, pow_1, mul_comm]);

val IN_MEASURABLE_BOREL_MAX = store_thm
  ("IN_MEASURABLE_BOREL_MAX",
  ``!a f g. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel
        ==> (\x. max (f x) (g x)) IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, extreal_max_def, IN_FUNSET, IN_UNIV]
 >> `!c. {x | (if f x <= g x then g x else f x) < c} = {x | f x < c} INTER {x | g x < c}`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
            EQ_TAC
            >- (RW_TAC std_ss [] >- METIS_TAC [let_trans] \\
                METIS_TAC [extreal_lt_def, lt_trans]) \\
            METIS_TAC [extreal_lt_def, lt_trans])
 >> `!c. {x | (if f x <= g x then g x else f x) < c} INTER space a =
         ({x | f x < c} INTER space a) INTER ({x | g x < c} INTER space a)`
        by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]);

val IN_MEASURABLE_BOREL_MIN = store_thm
  ("IN_MEASURABLE_BOREL_MIN",
  ``!a f g. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel
        ==> (\x. min (f x) (g x)) IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, extreal_min_def, IN_FUNSET, IN_UNIV]
 >> Know `!c. {x | (if f x <= g x then f x else g x) < c} =
              {x | f x < c} UNION {x | g x < c}`
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION] \\
     EQ_TAC >- RW_TAC std_ss [] \\
     RW_TAC std_ss [] >- METIS_TAC [let_trans] \\
     METIS_TAC [extreal_lt_def, lt_trans]) >> DISCH_TAC
 >> `!c. {x | (if f x <= g x then f x else g x) < c} INTER space a =
         ({x | f x < c} INTER space a) UNION ({x | g x < c} INTER space a)`
       by ASM_SET_TAC []
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_UNION]);

val IN_MEASURABLE_BOREL_MONO_SUP = store_thm
  ("IN_MEASURABLE_BOREL_MONO_SUP",
  ``!fn f a. sigma_algebra a /\ (!n:num. fn n IN measurable a Borel) /\
            (!n x. x IN space a ==> fn n x <= fn (SUC n) x) /\
            (!x. x IN space a ==> (f x = sup (IMAGE (\n. fn n x) UNIV)))
         ==> f IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT2, IN_FUNSET, IN_UNIV]
 >> `{x | sup (IMAGE (\n. fn n x) UNIV) <= Normal c} INTER space a =
      BIGINTER (IMAGE (\n. {x | fn n x <= Normal c} INTER space a) UNIV)`
 by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER, sup_le] \\
     EQ_TAC
     >- (RW_TAC std_ss [] \\
         Q.PAT_X_ASSUM `!y. P y ==> y <= Normal c` MATCH_MP_TAC \\
         ONCE_REWRITE_TAC [GSYM SPECIFICATION] \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         METIS_TAC []) \\
     RW_TAC std_ss [] \\
     POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     METIS_TAC [])
 >> `{x | f x <= Normal c} INTER space a =
     {x | sup (IMAGE (\n. fn n x) UNIV) <= Normal c} INTER space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> `!c. BIGINTER (IMAGE (\n. {x | fn n x <= Normal c} INTER (space a)) UNIV) IN subsets a`
      by (RW_TAC std_ss [] \\
          (MP_TAC o Q.SPEC `(space a,subsets a)`) SIGMA_ALGEBRA_FN_BIGINTER \\
          RW_TAC std_ss [IN_FUNSET, IN_UNIV, space_def, subsets_def, SPACE])
 >> METIS_TAC []);

(* a generalized version of IN_MEASURABLE_BOREL_MAX, cf. sup_maximal *)
Theorem IN_MEASURABLE_BOREL_MAXIMAL :
    !N. FINITE (N :'b set) ==>
        !g f a. sigma_algebra a /\ (!n. g n IN measurable a Borel) /\
               (!x. f x = sup (IMAGE (\n. g n x) N)) ==> f IN measurable a Borel
Proof
    HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [sup_empty, IMAGE_EMPTY, IMAGE_INSERT]
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
     Q.EXISTS_TAC `NegInf` >> art [])
 >> Cases_on `N = {}`
 >- (fs [IMAGE_EMPTY, sup_sing] >> METIS_TAC [])
 >> Know `!x. sup (g e x INSERT (IMAGE (\n. g n x) N)) =
              max (g e x) (sup (IMAGE (\n. g n x) N))`
 >- (RW_TAC std_ss [sup_eq'] >| (* 2 subgoals *)
    [ (* goal 1 (of 2) *)
      fs [IN_INSERT, le_max] >> DISJ2_TAC \\
      MATCH_MP_TAC le_sup_imp' >> rw [IN_IMAGE] \\
      Q.EXISTS_TAC `n` >> art [],
      (* goal 2 (of 2) *)
      POP_ASSUM MATCH_MP_TAC \\
      fs [IN_INSERT, extreal_max_def] \\
      Cases_on `g e x <= sup (IMAGE (\n. g n x) N)` >> fs [] \\
      DISJ2_TAC \\
     `FINITE (IMAGE (\n. g n x) N)` by METIS_TAC [IMAGE_FINITE] \\
      Know `IMAGE (\n. g n x) N <> {}`
      >- (RW_TAC set_ss [NOT_IN_EMPTY, Once EXTENSION]) >> DISCH_TAC \\
     `sup (IMAGE (\n. g n x) N) IN (IMAGE (\n. g n x) N)` by METIS_TAC [sup_maximal] \\
      fs [IN_IMAGE] >> Q.EXISTS_TAC `n` >> art [] ])
 >> DISCH_THEN (fs o wrap)
 >> Q.PAT_X_ASSUM `!g f a. P => f IN Borel_measurable a`
      (MP_TAC o (Q.SPECL [`g`, `\x. sup (IMAGE (\n. g n x) N)`, `a`]))
 >> rw []
 >> `f = \x. max (g e x) ((\x. sup (IMAGE (\n. g n x) N)) x)` by METIS_TAC []
 >> POP_ORW
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX >> art []
QED

(* a generalized version of IN_MEASURABLE_BOREL_MIN, cf. inf_minimal *)
Theorem IN_MEASURABLE_BOREL_MINIMAL :
    !N. FINITE (N :'b set) ==>
        !g f a. sigma_algebra a /\ (!n. g n IN measurable a Borel) /\
               (!x. f x = inf (IMAGE (\n. g n x) N)) ==> f IN measurable a Borel
Proof
    HO_MATCH_MP_TAC FINITE_INDUCT
 >> RW_TAC std_ss [inf_empty, IMAGE_EMPTY, IMAGE_INSERT]
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST \\
     Q.EXISTS_TAC `PosInf` >> art [])
 >> Cases_on `N = {}`
 >- (fs [IMAGE_EMPTY, inf_sing] >> METIS_TAC [])
 >> Know `!x. inf (g e x INSERT (IMAGE (\n. g n x) N)) =
              min (g e x) (inf (IMAGE (\n. g n x) N))`
 >- (RW_TAC std_ss [inf_eq'] >| (* 2 subgoals *)
    [ (* goal 1 (of 2) *)
      fs [IN_INSERT, min_le] >> DISJ2_TAC \\
      MATCH_MP_TAC inf_le_imp' >> rw [IN_IMAGE] \\
      Q.EXISTS_TAC `n` >> art [],
      (* goal 2 (of 2) *)
      POP_ASSUM MATCH_MP_TAC \\
      fs [IN_INSERT, extreal_min_def] \\
      Cases_on `g e x <= inf (IMAGE (\n. g n x) N)` >> fs [] \\
      DISJ2_TAC \\
     `FINITE (IMAGE (\n. g n x) N)` by METIS_TAC [IMAGE_FINITE] \\
      Know `IMAGE (\n. g n x) N <> {}`
      >- (RW_TAC set_ss [NOT_IN_EMPTY, Once EXTENSION]) >> DISCH_TAC \\
     `inf (IMAGE (\n. g n x) N) IN (IMAGE (\n. g n x) N)` by METIS_TAC [inf_minimal] \\
      fs [IN_IMAGE] >> Q.EXISTS_TAC `n` >> art [] ])
 >> DISCH_THEN (fs o wrap)
 >> Q.PAT_X_ASSUM `!g f a. P => f IN Borel_measurable a`
      (MP_TAC o (Q.SPECL [`g`, `\x. inf (IMAGE (\n. g n x) N)`, `a`]))
 >> rw []
 >> `f = \x. min (g e x) ((\x. inf (IMAGE (\n. g n x) N)) x)` by METIS_TAC []
 >> POP_ORW
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MIN >> art []
QED

Theorem IN_MEASURABLE_BOREL_SUMINF :
    !fn f a. sigma_algebra a /\ (!n:num. fn n IN measurable a Borel) /\
            (!i x. x IN space a ==> 0 <= fn i x) /\
            (!x. x IN space a ==> (f x = suminf (\n. fn n x))) ==> f IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> Know `!x. x IN space a ==>
              f x = sup (IMAGE (\n. SIGMA (\i. fn i x) (count n)) univ(:num))`
 >- (rpt STRIP_TAC \\
     RES_TAC >> Q.PAT_X_ASSUM `f x = Y` (ONCE_REWRITE_TAC o wrap) \\
     MATCH_MP_TAC ext_suminf_def >> rw []) >> DISCH_TAC
 >> Q.PAT_X_ASSUM `!x. x IN space a ==> f x = suminf (\n. fn n x)` K_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MONO_SUP
 >> Q.EXISTS_TAC `\n x. SIGMA (\i. fn i x) (count n)`
 >> RW_TAC std_ss []
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC (ISPECL [``a :'a algebra``, ``fn :num -> 'a -> extreal``]
                           IN_MEASURABLE_BOREL_SUM) \\
      Q.EXISTS_TAC `count n` >> RW_TAC std_ss [FINITE_COUNT, IN_COUNT] \\
      MATCH_MP_TAC pos_not_neginf >> PROVE_TAC [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
      RW_TAC arith_ss [COUNT_SUC, SUBSET_DEF, FINITE_COUNT, IN_COUNT] ]
QED

val IN_MEASURABLE_BOREL_FN_PLUS = store_thm
  ("IN_MEASURABLE_BOREL_FN_PLUS",
  ``!a f. f IN measurable a Borel ==> fn_plus f IN measurable a Borel``,
    RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV, fn_plus_def]
 >> Cases_on `c <= 0`
 >- (`{x | (if 0 < f x then f x else 0) < Normal c} = {}`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] \\
          `!x. 0 <= (if 0 < f x then f x else 0)` by RW_TAC real_ss [lt_imp_le, le_refl] \\
           METIS_TAC [le_trans, extreal_lt_def, extreal_of_num_def, extreal_le_def]) \\
     METIS_TAC [sigma_algebra_def, algebra_def, INTER_EMPTY])
 >> `{x | (if 0 < f x then f x else 0) < Normal c} = {x | f x < Normal c}`
       by (RW_TAC real_ss [EXTENSION, GSPECIFICATION] \\
           EQ_TAC
           >- (RW_TAC real_ss [] >> METIS_TAC [extreal_lt_def, let_trans]) \\
           RW_TAC real_ss [] \\
           METIS_TAC [extreal_lt_eq, extreal_of_num_def, real_lte])
 >> METIS_TAC []);

val IN_MEASURABLE_BOREL_FN_MINUS = store_thm
  ("IN_MEASURABLE_BOREL_FN_MINUS",
  ``!a f. f IN measurable a Borel ==> fn_minus f IN measurable a Borel``,
    RW_TAC std_ss [fn_minus_def]
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV, fn_minus_def]
 >- METIS_TAC [IN_MEASURABLE_BOREL]
 >> Cases_on `c <= 0`
 >- (`{x | (if f x < 0 then -f x else 0) < Normal c} = {}`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] \\
           `!x. 0 <= (if f x < 0 then -f x else 0)`
                 by (RW_TAC real_ss [le_refl] \\
                     METIS_TAC [lt_neg, neg_0, lt_imp_le]) \\
            METIS_TAC [extreal_of_num_def, extreal_le_def, le_trans, extreal_lt_def]) \\
     METIS_TAC [sigma_algebra_def, algebra_def, INTER_EMPTY, IN_MEASURABLE_BOREL])
 >> `{x | (if f x < 0 then -f x else 0) < Normal c} = {x | Normal (-c) < f x}`
        by (RW_TAC real_ss [EXTENSION,GSPECIFICATION] \\
            EQ_TAC
            >- (RW_TAC std_ss [] >- METIS_TAC [lt_neg, neg_neg, extreal_ainv_def] \\
                METIS_TAC [lt_neg, neg_neg, neg_0, extreal_lt_def, lte_trans, lt_imp_le,
                           extreal_ainv_def]) \\
            RW_TAC std_ss [] >- METIS_TAC [lt_neg, neg_neg, extreal_ainv_def] \\
            METIS_TAC [real_lte, extreal_lt_eq, extreal_of_num_def, extreal_ainv_def])
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]);

(* used in martingaleTheory.FUBINI *)
Theorem IN_MEASURABLE_BOREL_PLUS_MINUS :
    !a f. f IN measurable a Borel <=>
          fn_plus f IN measurable a Borel /\ fn_minus f IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> EQ_TAC
 >- RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> qexistsl_tac [`fn_plus f`, `fn_minus f`]
 >> RW_TAC std_ss [fn_plus_def, fn_minus_def, sub_rzero, lt_antisym, sub_rzero, add_lzero]
 >| [ (* goal 1 (of 8) *)
      METIS_TAC [IN_MEASURABLE_BOREL],
      (* goal 2 (of 8) *)
      METIS_TAC [lt_antisym],
      (* goal 3 (of 8) *)
      DISJ1_TAC >> REWRITE_TAC [extreal_not_infty, extreal_of_num_def] \\
      MATCH_MP_TAC pos_not_neginf \\
      MATCH_MP_TAC lt_imp_le >> art [],
      (* goal 4 (of 8) *)
      DISJ2_TAC >> REWRITE_TAC [extreal_not_infty, extreal_of_num_def] \\
      MATCH_MP_TAC pos_not_neginf \\
      Suff ‘f x <= 0’ >- METIS_TAC [neg_neg, le_neg, neg_0] \\
      MATCH_MP_TAC lt_imp_le >> art [],
      (* goal 5 (of 8) *)
      METIS_TAC [extreal_not_infty, extreal_of_num_def],
      (* goal 6 (of 8) *)
      METIS_TAC [lt_antisym],
      (* goal 7 (of 8) *)
      METIS_TAC [sub_rneg, add_lzero, extreal_of_num_def],
      (* goal 8 (of 8) *)
      METIS_TAC [le_antisym, extreal_lt_def] ]
QED

Theorem IN_MEASURABLE_BOREL_TIMES :
  !m f g h.
     measure_space m /\
     f IN measurable (m_space m, measurable_sets m) Borel /\
     g IN measurable (m_space m, measurable_sets m) Borel /\
     (!x. x IN m_space m ==> (h x = f x * g x)) ==>
     h IN measurable (m_space m, measurable_sets m) Borel
Proof
  RW_TAC std_ss [] THEN
  Q_TAC SUFF_TAC `(\x. f x * g x) IN measurable (m_space m,measurable_sets m) Borel` THENL
  [RW_TAC std_ss [IN_MEASURABLE, space_def] THENL
   [EVAL_TAC THEN SRW_TAC[][IN_DEF,IN_FUNSET], ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `s`) THEN ASM_REWRITE_TAC [] THEN
   SIMP_TAC std_ss [INTER_DEF] THEN
   Q_TAC SUFF_TAC `{x | x IN PREIMAGE (\x. f x * g x) s /\ x IN m_space m} =
                   {x | x IN PREIMAGE h s /\ x IN m_space m}` THENL
   [METIS_TAC [], ALL_TAC] THEN
   SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_PREIMAGE] THEN
   ASM_SET_TAC [], ALL_TAC] THEN

  Q_TAC SUFF_TAC `(\x. PosInf) IN measurable (m_space m,measurable_sets m) Borel /\
                  (\x. NegInf) IN measurable (m_space m,measurable_sets m) Borel` THENL
  [STRIP_TAC,
   CONJ_TAC THEN MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
   METIS_TAC [measure_space_def]] THEN

  ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
  Q_TAC SUFF_TAC `(\x. f x * g x) =
                  (\x. if {x | ((f x = PosInf) \/ (f x = NegInf))} x
                       then (\x. if f x = PosInf then PosInf * g x
                                                 else NegInf * g x) x
                       else (\x. Normal (real (f x)) * g x) x)` THENL
  [DISC_RW_KILL,
   SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THENL
   [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [],
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN
   GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN

  MATCH_MP_TAC MEASURABLE_IF THEN
  RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
  [ALL_TAC, ALL_TAC,
   Q_TAC SUFF_TAC
   `{x | x IN m_space m /\ {x | (f x = PosInf) \/ (f x = NegInf)} x} =
    PREIMAGE f {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
    GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | (x = PosInf) \/ (x = NegInf)} =
                                {PosInf} UNION {NegInf}``] THEN
   MATCH_MP_TAC ALGEBRA_UNION THEN
   METIS_TAC [measure_space_def, sigma_algebra_def,
              BOREL_MEASURABLE_INFINITY]] THENL
  [ALL_TAC,
   ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
   Q_TAC SUFF_TAC `(\x. Normal (real (f x)) * g x) =
           (\x. if {x | ((g x = PosInf) \/ (g x = NegInf))} x
                then (\x. if g x = PosInf then Normal (real (f x)) * PosInf
                                          else Normal (real (f x)) * NegInf) x
                else (\x. Normal (real (f x)) * Normal (real (g x))) x)` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [],
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN
   MATCH_MP_TAC MEASURABLE_IF THEN
   RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
   [ALL_TAC,
    `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    MATCH_MP_TAC IN_MEASURABLE_BOREL_MUL THEN
    Q.EXISTS_TAC `(\x. Normal (real (f x)))` THEN
    Q.EXISTS_TAC `(\x. Normal (real (g x)))` THEN
    FULL_SIMP_TAC std_ss [measure_space_def, extreal_not_infty] THEN
    ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
    CONJ_TAC THENL
    [Q_TAC SUFF_TAC `(\x. Normal (real (f x))) =
      (\x. if {x | (f x = PosInf) \/ (f x = NegInf)} x then (\x. 0) x else f x)` THENL
     [DISC_RW_KILL,
      ABS_TAC THEN COND_CASES_TAC THENL
      [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
       SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [real_def, extreal_of_num_def],
       ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN
      GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN
     MATCH_MP_TAC MEASURABLE_IF THEN
     RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
     [ALL_TAC, METIS_TAC [measure_space_def]] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\
                     {x | (f x = PosInf) \/ (f x = NegInf)} x} =
          PREIMAGE f {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE
     ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `(\x. Normal (real (g x))) =
      (\x. if {x | (g x = PosInf) \/ (g x = NegInf)} x then (\x. 0) x else g x)` THENL
     [DISC_RW_KILL,
      ABS_TAC THEN COND_CASES_TAC THENL
      [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
       SIMP_TAC std_ss [GSPECIFICATION] THEN
       METIS_TAC [real_def, extreal_of_num_def],
       ALL_TAC] THEN
      POP_ASSUM MP_TAC THEN
      GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [normal_real]] THEN
     MATCH_MP_TAC MEASURABLE_IF THEN
     RW_TAC std_ss [m_space_def, measurable_sets_def, SPACE] THENL
     [ALL_TAC, METIS_TAC [measure_space_def]] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\
                     {x | (g x = PosInf) \/ (g x = NegInf)} x} =
          PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE
     ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY],

     Q_TAC SUFF_TAC `{x | x IN m_space m /\ {x | (g x = PosInf) \/ (g x = NegInf)} x} =
                  PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
     MATCH_MP_TAC ALGEBRA_UNION THEN
     METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY]] THEN

    ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
     ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
    Q_TAC SUFF_TAC `(\x. if g x = PosInf then Normal (real (f x)) * PosInf
                         else Normal (real (f x)) * NegInf) =
                    (\x. if (\x. g x = PosInf) x then (\x. Normal (real (f x)) * PosInf) x
                         else (\x. Normal (real (f x)) * NegInf) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
    MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL

    [SIMP_TAC std_ss [extreal_mul_def] THEN
     Q_TAC SUFF_TAC `(\x. if real (f x) = 0 then Normal 0
                         else if 0 < real (f x) then PosInf
                         else NegInf) =
                    (\x. if (\x. real (f x) = 0) x then (\x. Normal 0) x
                         else (\x. if 0 < real (f x) then PosInf
                         else NegInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC MEASURABLE_IF THEN
     RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
      ALL_TAC,
      SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
      Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (f x)) = 0)} =
                      PREIMAGE f {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
      [DISC_RW_KILL,
       SIMP_TAC std_ss [PREIMAGE_def] THEN
       SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
       GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
       FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
       TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
      FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                   {0} UNION ({PosInf} UNION {NegInf})``] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN
      `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN
     SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN

     Q_TAC SUFF_TAC `(\x. if 0 < real (f x) then PosInf else NegInf) =
                (\x. if (\x. 0 < real (f x)) x then (\x. PosInf) x else (\x. NegInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
     MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ALL_TAC] THEN
     SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (f x))} =
                      PREIMAGE f {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [PREIMAGE_def] THEN
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
      GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
      FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
      TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])] THEN

     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
                                  {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN
     `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
     ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
     CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE]),

     ALL_TAC,
     Q_TAC SUFF_TAC `{x | x IN m_space m /\ (g x = PosInf)} =
                    PREIMAGE g {x | x = PosInf} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
      GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
      SET_TAC []] THEN
     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
     SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

    SIMP_TAC std_ss [extreal_mul_def] THEN
     Q_TAC SUFF_TAC `(\x. if real (f x) = 0 then Normal 0
                         else if 0 < real (f x) then NegInf
                         else PosInf) =
                    (\x. if (\x. real (f x) = 0) x then (\x. Normal 0) x
                         else (\x. if 0 < real (f x) then NegInf
                         else PosInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC MEASURABLE_IF THEN
     RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
      ALL_TAC,
      SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
      Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (f x)) = 0)} =
                      PREIMAGE f {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
      [DISC_RW_KILL,
       SIMP_TAC std_ss [PREIMAGE_def] THEN
       SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
       GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
       FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
       TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
      FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                   {0} UNION ({PosInf} UNION {NegInf})``] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN
      `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
      MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN
     SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN

     Q_TAC SUFF_TAC `(\x. if 0 < real (f x) then NegInf else PosInf) =
                (\x. if (\x. 0 < real (f x)) x then (\x. NegInf) x else (\x. PosInf) x)` THENL
     [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
     MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
     [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
      ALL_TAC] THEN
     SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
     Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (f x))} =
                      PREIMAGE f {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)} INTER m_space m` THENL
     [DISC_RW_KILL,
      SIMP_TAC std_ss [PREIMAGE_def] THEN
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
      GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
      FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
      TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])] THEN

     FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ONCE_REWRITE_TAC [SET_RULE
     ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
       {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN
     `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
     ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
     MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
     CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
      ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE])] THEN

  ONCE_REWRITE_TAC [METIS [SPACE, m_space_def, measurable_sets_def]
    ``Borel = (m_space (space Borel, subsets Borel, (\x. 0)),
       measurable_sets (space Borel, subsets Borel, (\x. 0)))``] THEN
  Q_TAC SUFF_TAC `(\x. if (\x. f x = PosInf) x then (\x. PosInf * g x) x else (\x. NegInf * g x) x) IN
                    measurable (m_space m,measurable_sets m)
                               (m_space (space Borel,subsets Borel,(\x. 0)),
                                measurable_sets (space Borel,subsets Borel,(\x. 0)))` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
  [Q_TAC SUFF_TAC `(\x. PosInf * g x) =
                   (\x. if {x | ((g x = PosInf) \/ (g x = NegInf))} x
                        then (\x. if g x = PosInf then PosInf else NegInf) x
                        else (\x. PosInf * Normal (real (g x))) x)` THENL
   [DISC_RW_KILL,
    ABS_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [extreal_mul_def],
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN
    METIS_TAC [normal_real]] THEN
   MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
   [Q_TAC SUFF_TAC `(\x. if g x = PosInf then PosInf else NegInf) =
               (\x. if (\x. g x = PosInf) x then (\x. PosInf) x else (\x. NegInf) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (g x = PosInf)} =
                    PREIMAGE g {x | x = PosInf} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY],
    ALL_TAC,
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ {x | (g x = PosInf) \/ (g x = NegInf)} x} =
                   PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE
    ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY]] THEN

   `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
   SIMP_TAC std_ss [extreal_mul_def] THEN
   Q_TAC SUFF_TAC `(\x. if real (g x) = 0 then Normal 0
                        else if 0 < real (g x) then PosInf
                        else NegInf) =
                   (\x. if (\x. real (g x) = 0) x then (\x. Normal 0) x
                        else (\x. if 0 < real (g x) then PosInf
                        else NegInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC MEASURABLE_IF THEN
   RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
    ALL_TAC,
    SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (g x)) = 0)} =
                    PREIMAGE g {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def] THEN
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
     FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                 {0} UNION ({PosInf} UNION {NegInf})``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

   Q_TAC SUFF_TAC `(\x. if 0 < real (g x) then PosInf else NegInf) =
              (\x. if (\x. 0 < real (g x)) x then (\x. PosInf) x else (\x. NegInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (g x))} =
                    PREIMAGE g {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)} INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
    GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
    FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
    TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])] THEN

   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE
   ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
     {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
   ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
   CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE]),
   ALL_TAC,
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ (f x = PosInf)} =
                    PREIMAGE f {x | x = PosInf} INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
    GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SET_TAC []] THEN
   FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
   SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

  Q_TAC SUFF_TAC `(\x. NegInf * g x) =
                  (\x. if {x | ((g x = PosInf) \/ (g x = NegInf))} x
                       then (\x. if g x = PosInf then NegInf else PosInf) x
                       else (\x. NegInf * Normal (real (g x))) x)` THENL
   [DISC_RW_KILL,
    ABS_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
     SIMP_TAC std_ss [GSPECIFICATION] THEN METIS_TAC [extreal_mul_def],
     ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
    SIMP_TAC std_ss [GSPECIFICATION] THEN
    METIS_TAC [normal_real]] THEN
   MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
   [Q_TAC SUFF_TAC `(\x. if g x = PosInf then NegInf else PosInf) =
               (\x. if (\x. g x = PosInf) x then (\x. NegInf) x else (\x. PosInf) x)` THENL
    [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
    MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
    [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
     ALL_TAC] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (g x = PosInf)} =
                    PREIMAGE g {x | x = PosInf} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | x = PosInf} = {PosInf}``] THEN
    SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY],
    ALL_TAC,
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ {x | (g x = PosInf) \/ (g x = NegInf)} x} =
                   PREIMAGE g {x | (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_PREIMAGE] THEN
     GEN_TAC THEN GEN_REWR_TAC (LAND_CONV o RAND_CONV) [GSYM SPECIFICATION] THEN
     SET_TAC []] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE
    ``{x | (x = PosInf) \/ (x = NegInf)} = {PosInf} UNION {NegInf}``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    METIS_TAC [measure_space_def, sigma_algebra_def, BOREL_MEASURABLE_INFINITY]] THEN

    `(\x. 0) IN measurable (m_space m,measurable_sets m) Borel` by
     (MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST THEN
      METIS_TAC [measure_space_def]) THEN
   SIMP_TAC std_ss [extreal_mul_def] THEN
   Q_TAC SUFF_TAC `(\x. if real (g x) = 0 then Normal 0
                        else if 0 < real (g x) then NegInf
                        else PosInf) =
                   (\x. if (\x. real (g x) = 0) x then (\x. Normal 0) x
                        else (\x. if 0 < real (g x) then NegInf
                        else PosInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN MATCH_MP_TAC MEASURABLE_IF THEN
   RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE, GSYM extreal_of_num_def],
    ALL_TAC,
    SIMP_TAC std_ss [GSYM extreal_11, GSYM extreal_of_num_def] THEN
    Q_TAC SUFF_TAC `{x | x IN m_space m /\ (Normal (real (g x)) = 0)} =
                    PREIMAGE g {x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} INTER m_space m` THENL
    [DISC_RW_KILL,
     SIMP_TAC std_ss [PREIMAGE_def] THEN
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
     GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
     FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def] THEN
     TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real])] THEN
    FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [SET_RULE ``{x | (x = 0) \/ (x = PosInf) \/ (x = NegInf)} =
                                 {0} UNION ({PosInf} UNION {NegInf})``] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN
    `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_SING, extreal_of_num_def] THEN
    MATCH_MP_TAC ALGEBRA_UNION THEN ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY]] THEN

   Q_TAC SUFF_TAC `(\x. if 0 < real (g x) then NegInf else PosInf) =
              (\x. if (\x. 0 < real (g x)) x then (\x. NegInf) x else (\x. PosInf) x)` THENL
   [DISC_RW_KILL, SIMP_TAC std_ss []] THEN
   MATCH_MP_TAC MEASURABLE_IF THEN RW_TAC std_ss [] THENL
   [ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ASM_SIMP_TAC std_ss [m_space_def, measurable_sets_def, SPACE],
    ALL_TAC] THEN
   SIMP_TAC std_ss [GSYM extreal_lt_eq, GSYM extreal_of_num_def] THEN
   Q_TAC SUFF_TAC `{x | x IN m_space m /\ 0 < Normal (real (g x))} =
                    PREIMAGE g {x | 0 < x /\ (x <> PosInf) /\ (x <> NegInf)}
                    INTER m_space m` THENL
   [DISC_RW_KILL,
    SIMP_TAC std_ss [PREIMAGE_def] THEN
    SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] THEN
    GEN_TAC THEN EQ_TAC THEN
    RW_TAC std_ss [real_def, extreal_of_num_def, real_normal] THEN
    FULL_SIMP_TAC std_ss [GSYM extreal_of_num_def, lt_refl] THEN
    TRY (METIS_TAC [extreal_of_num_def, extreal_11, normal_real, extreal_lt_eq])]
   THEN FULL_SIMP_TAC std_ss [IN_MEASURABLE, space_def, subsets_def] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [SET_RULE
    ``{x | 0 < x /\ x <> PosInf /\ x <> NegInf} =
      {x | 0 < x} INTER ((UNIV DIFF {PosInf}) INTER (UNIV DIFF {NegInf}))``] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN
   `algebra Borel` by METIS_TAC [sigma_algebra_def, SIGMA_ALGEBRA_BOREL] THEN
   ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_SETS_OR, extreal_of_num_def] THEN
   MATCH_MP_TAC ALGEBRA_INTER THEN ASM_SIMP_TAC std_ss [GSYM SPACE_BOREL] THEN
   CONJ_TAC THEN (MATCH_MP_TAC ALGEBRA_DIFF THEN
    ASM_SIMP_TAC std_ss [BOREL_MEASURABLE_INFINITY, ALGEBRA_SPACE])
QED

Theorem IN_MEASURABLE_BOREL_TIMES' :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
             (!x. x IN space a ==> (h x = f x * g x)) ==> h IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘(space a,subsets a,(\s. 0))’, ‘f’, ‘g’, ‘h’]
                    IN_MEASURABLE_BOREL_TIMES)
 >> Know ‘sigma_finite_measure_space (space a,subsets a,(\s. 0))’
 >- (MATCH_MP_TAC measure_space_trivial >> art [])
 >> rw [sigma_finite_measure_space_def]
QED

Theorem IN_MEASURABLE_BOREL_IMP_BOREL : (* was: borel_IMP_Borel *)
    !f m. f IN measurable (m_space m,measurable_sets m) borel ==>
          (Normal o f) IN measurable (m_space m,measurable_sets m) Borel
Proof
  RW_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, o_DEF] THENL
  [EVAL_TAC THEN SRW_TAC[] [IN_DEF,IN_FUNSET], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [space_def, subsets_def] THEN
  KNOW_TAC ``PREIMAGE (\x. Normal ((f:'a->real) x)) s =
             PREIMAGE f (real_set s)`` THENL
  [SIMP_TAC std_ss [PREIMAGE_def, EXTENSION, GSPECIFICATION] THEN
   RW_TAC std_ss [real_set_def, GSPECIFICATION] THEN EQ_TAC THEN RW_TAC std_ss [] THENL
   [Q.EXISTS_TAC `Normal (f x)` THEN
    ASM_SIMP_TAC std_ss [extreal_not_infty, real_normal],
    ALL_TAC] THEN ASM_SIMP_TAC std_ss [normal_real],
   DISCH_TAC] THEN FULL_SIMP_TAC std_ss [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC ``s IN subsets Borel`` THEN
  FULL_SIMP_TAC std_ss [borel_eq_less, Borel_def] THEN
  RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER,
                 GSPECIFICATION, SUBSET_DEF] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `{s | real_set s IN P}`) THEN
  RW_TAC std_ss [IN_IMAGE, IN_UNIV, GSPECIFICATION] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
  [RW_TAC std_ss [real_set_def] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN Q.EXISTS_TAC `a` THEN
   GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
   [ONCE_REWRITE_TAC [GSYM extreal_lt_eq] THEN ASM_SIMP_TAC std_ss [normal_real],
    ALL_TAC] THEN Q.EXISTS_TAC `Normal x` THEN
   ASM_SIMP_TAC std_ss [extreal_lt_eq, extreal_not_infty, real_normal],
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN RW_TAC std_ss [sigma_algebra_alt_pow] THENL
  [SIMP_TAC std_ss [SUBSET_DEF, IN_POW, IN_UNIV],
   SIMP_TAC std_ss [GSPECIFICATION, real_set_def, NOT_IN_EMPTY] THEN
   ASM_SIMP_TAC std_ss [SET_RULE ``{real x | F} = {}``],
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [GSPECIFICATION] THEN DISCH_TAC THEN
   FIRST_X_ASSUM (MP_TAC o Q.SPEC `real_set s'`) THEN ASM_REWRITE_TAC [] THEN
   SIMP_TAC std_ss [real_set_def, GSPECIFICATION, IN_DIFF, IN_UNIV] THEN
   SIMP_TAC std_ss [DIFF_DEF, IN_UNIV, GSPECIFICATION] THEN
   MATCH_MP_TAC EQ_IMPLIES THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] THEN GEN_TAC THEN EQ_TAC THENL
   [RW_TAC std_ss [] THEN Q.EXISTS_TAC `Normal x` THEN
    POP_ASSUM (MP_TAC o Q.SPEC `Normal x`) THEN
    SIMP_TAC std_ss [real_normal, extreal_not_infty], ALL_TAC] THEN
   RW_TAC std_ss [] THEN ASM_CASES_TAC ``real x' <> real x''`` THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC ``x'' = PosInf`` THEN ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC ``x'' = NegInf`` THEN ASM_REWRITE_TAC [] THEN
   FULL_SIMP_TAC std_ss [] THEN UNDISCH_TAC ``real x' = real x''`` THEN
   ONCE_REWRITE_TAC [GSYM extreal_11] THEN FULL_SIMP_TAC std_ss [normal_real] THEN
   METIS_TAC [],
   ALL_TAC] THEN
  SIMP_TAC std_ss [GSPECIFICATION] THEN
  FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\i. real_set (A i))`) THEN
  KNOW_TAC ``real_set (BIGUNION {A i | i IN univ(:num)}) =
             BIGUNION {(\i. real_set (A i)) i | i IN univ(:num)}`` THENL
  [ALL_TAC,
   DISC_RW_KILL THEN DISCH_THEN (MATCH_MP_TAC) THEN POP_ASSUM MP_TAC THEN
   RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV, GSPECIFICATION] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC []] THEN
  SIMP_TAC std_ss [real_set_def, EXTENSION, GSPECIFICATION, IN_BIGUNION] THEN
  GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THENL
  [Q.EXISTS_TAC `real_set s'` THEN CONJ_TAC THENL
   [SIMP_TAC std_ss [real_set_def, GSPECIFICATION] THEN METIS_TAC [],
    ALL_TAC] THEN SIMP_TAC std_ss [IN_UNIV] THEN
   Q.EXISTS_TAC `i` THEN GEN_TAC THEN
   SIMP_TAC std_ss [real_set_def, GSPECIFICATION] THEN
   METIS_TAC [], ALL_TAC] THEN
  UNDISCH_TAC ``(x:real) IN s'`` THEN ASM_REWRITE_TAC [] THEN
  RW_TAC std_ss [] THEN Q.EXISTS_TAC `x'` THEN
  ASM_REWRITE_TAC [IN_UNIV] THEN Q.EXISTS_TAC `A i` THEN
  METIS_TAC []
QED

Theorem in_measurable_sigma_pow : (* was: measurable_measure_of *)
    !m sp N f. measure_space m /\
               N SUBSET POW sp /\ f IN (m_space m -> sp) /\
              (!y. y IN N ==> (PREIMAGE f y) INTER m_space m IN measurable_sets m) ==>
               f IN measurable (m_space m, measurable_sets m) (sigma sp N)
Proof
    RW_TAC std_ss [] >> MATCH_MP_TAC MEASURABLE_SIGMA
 >> FULL_SIMP_TAC std_ss [measure_space_def, subset_class_def]
 >> CONJ_TAC >- (ASM_SET_TAC [POW_DEF])
 >> RW_TAC std_ss []
 >- (SIMP_TAC std_ss [space_def, sigma_def] \\
     POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> EVAL_TAC >> METIS_TAC [])
 >> FULL_SIMP_TAC std_ss [space_def, subsets_def]
QED

Theorem in_measurable_borel_imp : (* was: borel_measurableI *)
    !m f. measure_space m /\
         (!s. open s ==> (PREIMAGE f s) INTER m_space m IN measurable_sets m) ==>
          f IN measurable (m_space m, measurable_sets m) borel
Proof
    RW_TAC std_ss [borel]
 >> MATCH_MP_TAC in_measurable_sigma_pow
 >> ASM_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> CONJ_TAC >- SET_TAC [POW_DEF]
 >> ASM_SET_TAC []
QED

Theorem in_measurable_borel_continuous_on : (* was: borel_measurable_continuous_on1 *)
    !f. f continuous_on UNIV ==> f IN measurable borel borel
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `M = (space borel, subsets borel, (\x:real->bool. 0))`
 >> Suff `f IN measurable (m_space M, measurable_sets M) borel`
 >- (SIMP_TAC std_ss [Abbr ‘M’, m_space_def, measurable_sets_def] \\
     SIMP_TAC std_ss [SPACE])
 >> MATCH_MP_TAC in_measurable_borel_imp
 >> reverse CONJ_TAC
 >- (RW_TAC std_ss [] \\
     Know `open {x | x IN UNIV /\ f x IN s}`
     >- (MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE (* key lemma *) \\
         ASM_SIMP_TAC std_ss [OPEN_UNIV]) >> DISCH_TAC \\
     SIMP_TAC std_ss [Abbr ‘M’, m_space_def, measurable_sets_def] \\
     SIMP_TAC std_ss [PREIMAGE_def, space_borel, INTER_UNIV] \\
     MATCH_MP_TAC borel_open >> ASM_SET_TAC [])
 >> Q.UNABBREV_TAC ‘M’
 >> MP_TAC (REWRITE_RULE [sigma_finite_measure_space_def]
                         (ISPEC “borel” measure_space_trivial))
 >> RW_TAC std_ss [sigma_algebra_borel]
QED

(* ------------------------------------------------------------------------- *)
(*  Construction of Borel measure space by CARATHEODORY_SEMIRING             *)
(* ------------------------------------------------------------------------- *)

(* cf. integrationTheory.INTERVAL_UPPERBOUND for open/closed intervals *)
Theorem right_open_interval_upperbound :
    !a b. a < b ==> interval_upperbound (right_open_interval a b) = b
Proof
    RW_TAC std_ss [interval_upperbound]
 >- (fs [EXTENSION, GSPECIFICATION, in_right_open_interval] \\
     METIS_TAC [REAL_LE_REFL])
 >> RW_TAC std_ss [right_open_interval, GSPECIFICATION,
                   GSYM REAL_LE_ANTISYM]
 >- (MATCH_MP_TAC REAL_IMP_SUP_LE >> rw []
     >- (Q.EXISTS_TAC `a` >> rw [REAL_LE_REFL]) \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> MATCH_MP_TAC REAL_LE_EPSILON
 >> rpt STRIP_TAC
 >> Q.ABBREV_TAC `y = sup {x | a <= x /\ x < b}`
 >> `b <= y + e <=> b - e <= y` by REAL_ARITH_TAC >> POP_ORW
 >> Q.UNABBREV_TAC `y`
 >> MATCH_MP_TAC REAL_IMP_LE_SUP >> rw []
 >- (Q.EXISTS_TAC `a` >> rw [REAL_LE_REFL])
 >- (Q.EXISTS_TAC `b` >> rw [] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> Cases_on `a <= b - e`
 >- (Q.EXISTS_TAC `b - e` >> rw [REAL_LE_TRANS] \\
     Q.PAT_X_ASSUM `0 < e` MP_TAC >> REAL_ARITH_TAC)
 >> Q.EXISTS_TAC `a` >> rw [REAL_LE_REFL]
 >> MATCH_MP_TAC REAL_LT_IMP_LE >> fs [real_lte]
QED

Theorem right_open_interval_lowerbound :
    !a b. a < b ==> interval_lowerbound (right_open_interval a b) = a
Proof
    RW_TAC std_ss [interval_lowerbound]
 >- (fs [EXTENSION, GSPECIFICATION, in_right_open_interval] \\
     METIS_TAC [REAL_LE_REFL])
 >> RW_TAC std_ss [right_open_interval, GSPECIFICATION]
 >> MATCH_MP_TAC REAL_INF_MIN >> rw []
QED

Theorem right_open_interval_two_bounds :
    !a b. interval_lowerbound (right_open_interval a b) <=
          interval_upperbound (right_open_interval a b)
Proof
    rpt GEN_TAC
 >> Cases_on `a < b`
 >- (rw [right_open_interval_upperbound, right_open_interval_lowerbound] \\
     IMP_RES_TAC REAL_LT_IMP_LE)
 >> fs [GSYM right_open_interval_empty]
 >> rw [interval_lowerbound, interval_upperbound, le_refl]
QED

Theorem right_open_interval_between_bounds :
    !x a b. x IN right_open_interval a b <=>
            interval_lowerbound (right_open_interval a b) <= x /\
            x < interval_upperbound (right_open_interval a b)
Proof
    rpt GEN_TAC
 >> reverse (Cases_on `a < b`)
 >- (FULL_SIMP_TAC std_ss [GSYM right_open_interval_empty] \\
     rw [NOT_IN_EMPTY, INTERVAL_BOUNDS_EMPTY] \\
     REAL_ARITH_TAC)
 >> rw [in_right_open_interval]
 >> EQ_TAC >> rpt STRIP_TAC (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      fs [right_open_interval_lowerbound],
      (* goal 2 (of 4) *)
      fs [right_open_interval_upperbound],
      (* goal 3 (of 4) *)
      rfs [right_open_interval_lowerbound, right_open_interval_upperbound],
      (* goal 4 (of 4) *)
      rfs [right_open_interval_lowerbound, right_open_interval_upperbound] ]
QED

(* The content (length) of [a, b), cf. integrationTheory.content *)
local
  val thm = prove (
    ``?l. !a b. a <= b ==> (l (right_open_interval a b) = Normal (b - a))``,
      Q.EXISTS_TAC `Normal o content` (* detail is not important *)
   >> RW_TAC std_ss [o_DEF, content]
   >- (IMP_RES_TAC REAL_LE_LT >> fs [right_open_interval_empty])
   >> fs [right_open_interval_empty]
   >> rw [right_open_interval_lowerbound, right_open_interval_upperbound]);
in
  (* |- !a b. a <= b ==> (lambda0 (right_open_interval a b) = Normal (b - a) *)
  val lambda0_def = new_specification ("lambda0_def", ["lambda0"], thm);
end;

val _ = overload_on ("lborel0",
          ``(space right_open_intervals,subsets right_open_intervals,lambda0)``);

Theorem lambda0_empty :
    lambda0 {} = 0
Proof
    MP_TAC (REWRITE_RULE [le_refl] (Q.SPECL [`0`, `0`] lambda0_def))
 >> `right_open_interval 0 0 = {}`
      by PROVE_TAC [right_open_interval_empty_eq, REAL_LE_REFL]
 >> rw [extreal_of_num_def]
QED

Theorem lambda0_not_infty :
    !a b. lambda0 (right_open_interval a b) <> PosInf /\
          lambda0 (right_open_interval a b) <> NegInf
Proof
    rpt GEN_TAC
 >> Cases_on `a < b`
 >- (IMP_RES_TAC REAL_LT_IMP_LE \\
     ASM_SIMP_TAC std_ss [lambda0_def, extreal_not_infty])
 >> fs [GSYM right_open_interval_empty, lambda0_empty,
        extreal_of_num_def, extreal_not_infty]
QED

Theorem lborel0_positive :
    positive lborel0
Proof
    RW_TAC std_ss [positive_def, measure_def, measurable_sets_def, lambda0_empty]
 >> fs [right_open_intervals, subsets_def]
 >> Cases_on `a < b`
 >- (IMP_RES_TAC REAL_LT_LE \\
     rw [lambda0_def, extreal_of_num_def, extreal_le_eq] \\
     REAL_ASM_ARITH_TAC)
 >> fs [GSYM right_open_interval_empty, lambda0_empty, le_refl]
QED

Theorem lborel0_subadditive :
    subadditive lborel0
Proof
    RW_TAC std_ss [subadditive_def, measure_def, measurable_sets_def, subsets_def,
                   right_open_intervals, GSPECIFICATION]
 >> Cases_on `x` >> Cases_on `x'` >> Cases_on `x''` >> fs []
 >> rename1 `s = right_open_interval a b`
 >> rename1 `t = right_open_interval c d`
 >> rename1 `s UNION t = right_open_interval q r`
 >> Cases_on `~(a < b)`
 >- (fs [GSYM right_open_interval_empty, right_open_interval, lambda0_empty,
         add_lzero, add_rzero] \\
     rfs [UNION_EMPTY, le_refl])
 >> Cases_on `~(c < d)`
 >- (fs [GSYM right_open_interval_empty, right_open_interval, lambda0_empty,
         add_lzero, add_rzero] \\
     rfs [UNION_EMPTY, le_refl])
 >> fs [] (* now: a < b /\ c < d *)
 >> Know `s UNION t IN subsets right_open_intervals`
 >- (SIMP_TAC std_ss [right_open_intervals, subsets_def, GSPECIFICATION] \\
     Q.EXISTS_TAC `(q,r)` >> ASM_SIMP_TAC std_ss [])
 >> DISCH_TAC
 >> `a <= d /\ c <= b` by PROVE_TAC [right_open_interval_union_imp]
 >> `s UNION t = right_open_interval (min a c) (max b d)`
     by PROVE_TAC [right_open_interval_union]
 >> `s <> {} /\ t <> {}` by PROVE_TAC [right_open_interval_empty]
 >> `s UNION t <> {}` by ASM_SET_TAC []
 >> `q < r /\ min a c < max b d` by PROVE_TAC [right_open_interval_empty]
 >> `(q = min a c) /\ (r = max b d)` by PROVE_TAC [right_open_interval_11]
 >> FULL_SIMP_TAC std_ss []
 (* max b d - min a c <= b - a + (d - c) *)
 >> IMP_RES_TAC REAL_LT_IMP_LE
 >> rw [lambda0_def, extreal_add_def, extreal_le_eq]
 >> `0 < b - a /\ 0 < d - c` by REAL_ASM_ARITH_TAC
 >> Cases_on `b <= d` >> Cases_on `a <= c`
 >> FULL_SIMP_TAC std_ss [real_lte, REAL_MAX_REDUCE, REAL_MIN_REDUCE]
 >> REAL_ASM_ARITH_TAC
QED

Theorem lborel0_additive :
    additive lborel0
Proof
    RW_TAC std_ss [additive_def, measure_def, measurable_sets_def, subsets_def,
                   right_open_intervals, GSPECIFICATION]
 (* rename the variables *)
 >> Cases_on `x` >> Cases_on `x'` >> Cases_on `x''` >> fs []
 >> rename1 `s = right_open_interval a b`
 >> rename1 `t = right_open_interval c d`
 >> rename1 `s UNION t = right_open_interval q r`
 >> Cases_on `~(a < b)`
 >- (fs [GSYM right_open_interval_empty, right_open_interval, lambda0_empty,
         add_lzero, add_rzero] \\
     rfs [UNION_EMPTY])
 >> Cases_on `~(c < d)`
 >- (fs [GSYM right_open_interval_empty, right_open_interval, lambda0_empty,
         add_lzero, add_rzero] \\
     rfs [UNION_EMPTY])
 >> fs [] (* now: a < b /\ c < d *)
 >> Know `s UNION t IN subsets right_open_intervals`
 >- (SIMP_TAC std_ss [right_open_intervals, subsets_def, GSPECIFICATION] \\
     Q.EXISTS_TAC `(q,r)` >> ASM_SIMP_TAC std_ss [])
 >> DISCH_TAC
 >> `a <= d /\ c <= b` by PROVE_TAC [right_open_interval_union_imp]
 >> `s UNION t = right_open_interval (min a c) (max b d)`
     by PROVE_TAC [right_open_interval_union]
 >> `s <> {} /\ t <> {}` by PROVE_TAC [right_open_interval_empty]
 >> `s UNION t <> {}` by ASM_SET_TAC []
 >> `q < r /\ min a c < max b d` by PROVE_TAC [right_open_interval_empty]
 >> `(q = min a c) /\ (r = max b d)` by PROVE_TAC [right_open_interval_11]
 >> FULL_SIMP_TAC std_ss []
 >> IMP_RES_TAC REAL_LT_IMP_LE
 >> ASM_SIMP_TAC std_ss [lambda0_def, extreal_add_def, extreal_11]
 (* max b d - min a c = b - a + (d - c) *)
 >> Know `b <= c \/ d <= a`
 >- (MATCH_MP_TAC right_open_interval_DISJOINT_imp >> PROVE_TAC [])
 (* clean up useless assumptions *)
 >> Q.PAT_X_ASSUM `s = right_open_interval a b` K_TAC
 >> Q.PAT_X_ASSUM `t = right_open_interval c d` K_TAC
 >> Q.PAT_X_ASSUM `_ IN subsets right_open_intervals` K_TAC
 >> Q.PAT_X_ASSUM `s UNION t = _` K_TAC
 >> Q.PAT_X_ASSUM `s UNION t <> {}` K_TAC
 >> Q.PAT_X_ASSUM `s <> {}` K_TAC
 >> Q.PAT_X_ASSUM `t <> {}` K_TAC
 >> Q.PAT_X_ASSUM `q = _` K_TAC
 >> Q.PAT_X_ASSUM `r = _` K_TAC
 >> Q.PAT_X_ASSUM `DISJOINT s t` K_TAC
 (* below are pure real arithmetic problems *)
 >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `a <= c /\ b <= d` by PROVE_TAC [REAL_LE_TRANS] \\
      fs [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
      REAL_ASM_ARITH_TAC,
      (* goal 2 (of 2) *)
     `d <= b /\ c <= a` by PROVE_TAC [REAL_LE_TRANS] \\
      fs [REAL_MAX_REDUCE, REAL_MIN_REDUCE] \\
      REAL_ASM_ARITH_TAC ]
QED

(* It seems that additivity of semiring does not imply finite additivity in
   general. To prove finite additivity of lborel0, we must first filter out
   all empty sets, then sort the rest of sets to guarantee that the first n
   sets still form a right-open interval.  -- Chun Tian, 26/1/2020
 *)
Theorem lborel0_finite_additive :
    finite_additive lborel0
Proof
    RW_TAC std_ss [finite_additive_def, measure_def, measurable_sets_def]
 >> ASSUME_TAC right_open_intervals_semiring
 >> ASSUME_TAC lborel0_positive
 >> ASSUME_TAC lborel0_additive
 (* spacial case 1: n = 0 *)
 >> `(n = 0) \/ 0 < n` by RW_TAC arith_ss []
 >- (rw [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY] \\
     fs [semiring_def, space_def, subsets_def,
         positive_def, measurable_sets_def, measure_def])
 (* special case 2: all f(i) = {} *)
 >> Cases_on `!k. k < n ==> f k = {}`
 >- (Suff `BIGUNION (IMAGE f (count n)) = {}`
     >- (Rewr' >> fs [positive_def, measurable_sets_def, measure_def] \\
         MATCH_MP_TAC EXTREAL_SUM_IMAGE_0 \\
         rw [FINITE_COUNT, IN_COUNT, o_DEF]) \\
     RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_COUNT, NOT_IN_EMPTY] \\
     STRONG_DISJ_TAC >> rw [])
 >> FULL_SIMP_TAC bool_ss [] (* f k <> {} *)
 (* Part I: filter the list removing empty sets *)
 >> Q.ABBREV_TAC `filtered = FILTER (\i. f i <> {}) (COUNT_LIST n)`
 >> Know `!i. MEM i filtered ==> i < n /\ f i <> {}`
 >- (GEN_TAC >> Q.UNABBREV_TAC `filtered` \\
     SIMP_TAC std_ss [MEM_FILTER, MEM_COUNT_LIST]) >> DISCH_TAC
 >> Q.ABBREV_TAC `n0 = LENGTH filtered`
 (* n0 <= n *)
 >> Know `n0 <= LENGTH (COUNT_LIST n)`
 >- (qunabbrevl_tac [`n0`, `filtered`] \\
     REWRITE_TAC [LENGTH_FILTER_LEQ])
 >> DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [LENGTH_COUNT_LIST]))
 >> Know `BIGUNION (IMAGE f (count n)) = BIGUNION (IMAGE f (set filtered))`
 >- (Q.UNABBREV_TAC `filtered` \\
     RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_COUNT,
                    MEM_FILTER, MEM_COUNT_LIST] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 `i < n` >> Q.EXISTS_TAC `i` \\
       rw [GSYM MEMBER_NOT_EMPTY] \\
       Q.EXISTS_TAC `x` >> art [],
       (* goal 2 (of 2) *)
       rename1 `i < n` >> Q.EXISTS_TAC `i` >> rw [] ])
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 >> Know `SIGMA (lambda0 o f) (count n) = SIGMA (lambda0 o f) (set filtered)`
 >- (Q.ABBREV_TAC `empties = FILTER (\i. f i = {}) (COUNT_LIST n)` \\
     Suff `set filtered = (count n) DIFF (set empties)`
     >- (Rewr' >> irule EXTREAL_SUM_IMAGE_ZERO_DIFF \\
         Q.UNABBREV_TAC `empties` \\
         RW_TAC std_ss [MEM_FILTER, MEM_COUNT_LIST, FINITE_COUNT,
                        IN_COUNT, o_DEF]
         >- fs [positive_def, measure_def, measurable_sets_def] \\
         DISJ1_TAC >> NTAC 2 STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         fs [positive_def, measure_def, measurable_sets_def]) \\
     qunabbrevl_tac [`empties`, `filtered`] \\
     RW_TAC std_ss [Once EXTENSION, MEM_FILTER, MEM_COUNT_LIST,
                    IN_DIFF, IN_COUNT] \\
     EQ_TAC >> RW_TAC std_ss []) >> Rewr'
 (* Part II: sort the list by lowerbounds *)
 >> Q.ABBREV_TAC `R = \s t. interval_lowerbound s <= interval_lowerbound t`
 >> Know `transitive R /\ total R`
 >- (RW_TAC std_ss [transitive_def, total_def] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.UNABBREV_TAC `R` >> fs [] \\
       MATCH_MP_TAC REAL_LE_TRANS \\
       Q.EXISTS_TAC `interval_lowerbound y` >> art [],
       (* goal 2 (of 2) *)
       Q.UNABBREV_TAC `R` >> fs [REAL_LE_TOTAL] ])
 >> STRIP_TAC
 >> Q.ABBREV_TAC `sorted = QSORT R (MAP f filtered)`
 >> `SORTED R sorted` by PROVE_TAC [QSORT_SORTED]
 (* establish a permutation *)
 >> Know `PERM sorted (MAP f filtered)`
 >- (ONCE_REWRITE_TAC [PERM_SYM] \\
     Q.UNABBREV_TAC `sorted` \\
     REWRITE_TAC [QSORT_PERM]) >> DISCH_TAC
 >> `LENGTH sorted = LENGTH filtered` by METIS_TAC [PERM_LENGTH, LENGTH_MAP]
 (* all distinctness of `sorted` from disjointness of `f` *)
 >> Know `ALL_DISTINCT sorted`
 >- (Suff `ALL_DISTINCT (MAP f filtered)`
     >- METIS_TAC [ALL_DISTINCT_PERM] \\
     MATCH_MP_TAC ALL_DISTINCT_MAP_INJ \\
     reverse CONJ_TAC
     >- (Q.UNABBREV_TAC `filtered` \\
         MATCH_MP_TAC FILTER_ALL_DISTINCT \\
         RW_TAC std_ss [COUNT_LIST_GENLIST, ALL_DISTINCT_GENLIST]) \\
     RW_TAC std_ss [] \\
     CCONTR_TAC >> METIS_TAC [DISJOINT_EMPTY_REFL]) >> DISCH_TAC
 (* from permutation to bijection (g) *)
 >> Q.PAT_X_ASSUM `PERM _ _` (MP_TAC o (MATCH_MP (GSYM PERM_BIJ)))
 >> RW_TAC std_ss []
 >> rename1 `g PERMUTES (count n0)`
 (* stage work *)
 >> Know `!i. i < n0 ==> g i < n0`
 >- (rpt STRIP_TAC >> `INJ g (count n0) (count n0)` by METIS_TAC [BIJ_DEF] \\
     fs [INJ_DEF, IN_COUNT]) >> DISCH_TAC
 >> Know `SIGMA (lambda0 o f) (set filtered) =
          SIGMA lambda0 (IMAGE f (set filtered))`
 >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_IMAGE \\
     SIMP_TAC std_ss [FINITE_LIST_TO_SET, IN_IMAGE, IN_COUNT] \\
     reverse CONJ_TAC
     >- (MATCH_MP_TAC INJ_IMAGE \\
         Q.EXISTS_TAC `set (MAP f filtered)` \\
         SIMP_TAC std_ss [INJ_DEF, MEM_MAP] \\
         CONJ_TAC >- METIS_TAC [] \\
         METIS_TAC [DISJOINT_EMPTY_REFL]) \\
     DISJ1_TAC >> NTAC 2 STRIP_TAC \\
     MATCH_MP_TAC pos_not_neginf \\
     rename1 `x = f i` \\
     Q.PAT_X_ASSUM `x = f i` (ONCE_REWRITE_TAC o wrap) \\
     fs [positive_def, measure_def, measurable_sets_def]) >> Rewr'
 >> Know `IMAGE f (set filtered) = set (MAP f filtered)`
 >- RW_TAC std_ss [Once EXTENSION, IN_IMAGE, EL_MEM, MEM_MAP]
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 (* lambda0 (BIGUNION (set (MAP f filtered))) =
                      SIGMA lambda0 (set (MAP f filtered)) *)
 >> Know `set (MAP f filtered) = set sorted`
 >- (Q.PAT_X_ASSUM `_ = MAP f filtered` (ONCE_REWRITE_TAC o wrap o SYM) \\
     ASM_SIMP_TAC std_ss [Once EXTENSION, MEM_GENLIST, MEM_EL] \\
     GEN_TAC >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `g i` >> art [] \\
       FIRST_X_ASSUM MATCH_MP_TAC >> art [],
       (* goal 2 (of 2) *)
       POP_ORW \\
       FULL_SIMP_TAC std_ss [BIJ_DEF, SURJ_DEF, IN_COUNT] \\
       rename1 `i < n0` \\
      `?y. y < n0 /\ g y = i` by METIS_TAC [] \\
       Q.EXISTS_TAC `y` >> art [] ]) >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 (* Part III: index function h of `sorted` *)
 >> Q.ABBREV_TAC `h = \i. EL i sorted`
 >> Know `set sorted = IMAGE h (count n0)`
 >- (Q.UNABBREV_TAC `h` \\
     RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_COUNT, MEM_EL] \\
     METIS_TAC [])
 >> DISCH_THEN ((REV_FULL_SIMP_TAC bool_ss) o wrap)
 (* meta h-properties *)
 >> Know `!i. i < n0 ==> h i <> {} /\ ?j. j < n /\ (h i = f j)`
 >- (NTAC 2 STRIP_TAC \\
     Q.PAT_X_ASSUM `_ = IMAGE h (count n0)` MP_TAC \\
     ASM_SIMP_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_COUNT, MEM_EL,
                          LENGTH_MAP, EL_MAP, NOT_IN_EMPTY] \\
     DISCH_THEN (ASSUME_TAC o (Q.SPEC `(h :num -> real set) i`)) \\
    `?j. j < n0 /\ h i = EL j (MAP f filtered)` by METIS_TAC [] \\
     POP_ORW \\
    `j < LENGTH filtered` by METIS_TAC [] \\
     ASM_SIMP_TAC std_ss [EL_MAP] \\
     CONJ_TAC >- METIS_TAC [EL_MEM] \\
     Q.EXISTS_TAC `EL j filtered` >> REWRITE_TAC [] \\
     METIS_TAC [EL_MEM]) >> DISCH_TAC
 (* h-properties *)
 >> Know `!i. i < n0 ==> (h i) IN subsets right_open_intervals`
 >- (rpt STRIP_TAC \\
    `?j. j < n /\ (h i = f j)` by PROVE_TAC [] >> POP_ORW \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Know `!i j. i < n0 /\ j < n0 /\ i <> j ==> DISJOINT (h i) (h j)`
 >- (rpt STRIP_TAC \\
    `?n1. n1 < n /\ (h i = f n1)` by PROVE_TAC [] \\
    `?n2. n2 < n /\ (h j = f n2)` by PROVE_TAC [] \\
     Know `n1 <> n2`
     >- (Q.UNABBREV_TAC `h` \\
         CCONTR_TAC >> rfs [EL_ALL_DISTINCT_EL_EQ] \\
         METIS_TAC []) >> DISCH_TAC >> art [] \\
     FIRST_ASSUM MATCH_MP_TAC >> art []) >> DISCH_TAC
 >> Know `SIGMA lambda0 (IMAGE h (count n0)) =
          SIGMA (lambda0 o h) (count n0)`
 >- (irule EXTREAL_SUM_IMAGE_IMAGE \\
     SIMP_TAC std_ss [FINITE_COUNT, IN_IMAGE, IN_COUNT] \\
     CONJ_TAC
     >- (DISJ1_TAC >> NTAC 2 STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         rename1 `x = h i` \\
         Q.PAT_X_ASSUM `x = h i` (ONCE_REWRITE_TAC o wrap) \\
         fs [positive_def, measure_def, measurable_sets_def]) \\
     MATCH_MP_TAC INJ_IMAGE \\
     Q.EXISTS_TAC `set sorted` \\
     qunabbrevl_tac [`h`, `n0`] >> rw [INJ_DEF, EL_MEM] \\
     METIS_TAC [EL_ALL_DISTINCT_EL_EQ]) >> Rewr'
 (* clean up useless assumptions *)
 >> Q.PAT_X_ASSUM `GENLIST _ n0 = MAP f filtered`                K_TAC
 >> Q.PAT_X_ASSUM `set (MAP f filtered) = IMAGE h (count n0)`    K_TAC
 >> Q.PAT_X_ASSUM `!i. P ==> f i IN subsets right_open_intervals` K_TAC
 >> Q.PAT_X_ASSUM `!i j. P ==> DISJOINT (f i) (f j)`             K_TAC
 >> Q.PAT_X_ASSUM `!i. MEM i filtered ==> P`                     K_TAC
 >> Q.PAT_X_ASSUM `k < n`                                        K_TAC
 >> Q.PAT_X_ASSUM `f k <> {}`                                    K_TAC
 (* Part IV: core induction assuming the key h-property *)
 >> Suff `!i. i <= n0 ==>
              BIGUNION (IMAGE h (count i)) IN subsets right_open_intervals`
 >- (DISCH_TAC \\
     Suff `!m. m <= n0 ==>
               (lambda0 (BIGUNION (IMAGE h (count m))) =
                SIGMA (lambda0 o h) (count m))`
     >- (DISCH_THEN MATCH_MP_TAC >> rw [LESS_EQ_REFL]) \\
     Induct_on `m` (* final induction *)
     >- (rw [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY] \\
         fs [positive_def, measure_def, measurable_sets_def]) \\
     DISCH_TAC \\
     SIMP_TAC std_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
     Know `lambda0 (h m UNION BIGUNION (IMAGE h (count m))) =
           lambda0 (h m) + lambda0 (BIGUNION (IMAGE h (count m)))`
     >- (MATCH_MP_TAC (REWRITE_RULE [measurable_sets_def, measure_def]
                                    (Q.ISPEC `lborel0` ADDITIVE)) \\
         rw [] >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
         REWRITE_TAC [GSYM BIGUNION_INSERT, GSYM IMAGE_INSERT, GSYM COUNT_SUC] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
     Q.PAT_X_ASSUM `m <= n0 ==> _` MP_TAC \\
    `m <= n0` by RW_TAC arith_ss [] \\
     Q.UNABBREV_TAC `n0` >> RW_TAC std_ss [] \\
     MATCH_MP_TAC EQ_SYM \\
     Suff `SIGMA (lambda0 o h) (m INSERT count m) = (lambda0 o h) m +
           SIGMA (lambda0 o h) (count m DELETE m)`
     >- rw [o_DEF, COUNT_DELETE] \\
     irule EXTREAL_SUM_IMAGE_PROPERTY_NEG \\
     RW_TAC std_ss [GSYM COUNT_SUC, IN_COUNT, o_DEF, FINITE_COUNT] \\
     MATCH_MP_TAC pos_not_neginf \\
     fs [positive_def, measure_def, measurable_sets_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.UNABBREV_TAC `h` >> rw [o_DEF])
 (* Part V: h-property of lowerbounds *)
 >> ‘!i j. i < j /\ j < n0 ==>
           interval_lowerbound (h i) <= interval_lowerbound (h j)’
      by (STRIP_TAC \\
          Q.PAT_X_ASSUM `transitive R`
                        (STRIP_ASSUME_TAC o (MATCH_MP SORTED_EL_LESS)) \\
          pop_assum (qspec_then ‘sorted’ mp_tac) \\
          simp[])
 (* h-property of upper- and lowerbounds *)
 >> Know `!i j. i < j /\ j < n0 ==>
                interval_upperbound (h i) <= interval_lowerbound (h j)`
 >- (rpt STRIP_TAC >> `i < n0` by RW_TAC arith_ss [] \\
     Q.PAT_X_ASSUM `!i j. i < j /\ j < n0 ==> P`
       (MP_TAC o Q.SPECL [`i`, `j`]) \\
     qunabbrevl_tac [`n0`, `R`] >> RW_TAC std_ss [] \\
     CCONTR_TAC \\
    `h i IN subsets right_open_intervals /\
     h j IN subsets right_open_intervals` by PROVE_TAC [] \\
    `?a1 b1. a1 < b1 /\ (h i = right_open_interval a1 b1)`
         by METIS_TAC [in_right_open_intervals_nonempty] \\
    `?a2 b2. a2 < b2 /\ (h j = right_open_interval a2 b2)`
         by METIS_TAC [in_right_open_intervals_nonempty] >> fs [] \\
     fs [right_open_interval_upperbound,
         right_open_interval_lowerbound] \\
    `i <> j` by RW_TAC arith_ss [] \\
     Know `DISJOINT (h i) (h j)` >- PROVE_TAC [] \\
     Q.PAT_X_ASSUM `h i = _` (PURE_ONCE_REWRITE_TAC o wrap) \\
     Q.PAT_X_ASSUM `h j = _` (PURE_ONCE_REWRITE_TAC o wrap) \\
     (* 2 possibile cases: [a1, [a2, b1) b2) or [a1, [a2, b2) b1),
        anyway we have `a2 IN [a1, b1)`. *)
     DISCH_THEN (ASSUME_TAC o (REWRITE_RULE [DISJOINT_ALT])) \\
     POP_ASSUM (MP_TAC o (Q.SPEC `a2`)) \\
     Know `a2 IN right_open_interval a1 b1`
     >- (rw [in_right_open_interval] >> fs [real_lte]) \\
     Know `a2 IN right_open_interval a2 b2`
     >- (rw [in_right_open_interval]) \\
     RW_TAC std_ss []) >> DISCH_TAC
 (* h-property of upperbounds *)
 >> Know `!i j. i < j /\ j < n0 ==>
                interval_upperbound (h i) <= interval_upperbound (h j)`
 >- (rpt STRIP_TAC >> `i < n0` by RW_TAC arith_ss [] \\
     Q.PAT_X_ASSUM `!i j. i < j /\ j < n0 ==> P`
       (MP_TAC o Q.SPECL [`i`, `j`]) \\
     Q.UNABBREV_TAC `n0` >> RW_TAC std_ss [] \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `interval_lowerbound (h j)` >> art [] \\
    `h j IN subsets right_open_intervals` by PROVE_TAC [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                (REWRITE_RULE [in_right_open_intervals])) \\
     POP_ORW \\
     REWRITE_TAC [right_open_interval_two_bounds]) >> DISCH_TAC
 (* h-compactness: there's no gap between each h(i) *)
 >> Know `!i. SUC i < n0 ==>
             (interval_lowerbound (h (SUC i)) = interval_upperbound (h i))`
 >- (rpt STRIP_TAC >> `i < n0` by RW_TAC arith_ss [] \\
     MATCH_MP_TAC EQ_SYM \\
    `(n0 = 0) \/ 0 < n0` by RW_TAC arith_ss [] >- fs [] \\
     Know `BIGUNION (IMAGE h (count n0)) <> {} /\
           BIGUNION (IMAGE h (count n0)) IN subsets right_open_intervals`
     >- (Q.UNABBREV_TAC `n0` >> art [] \\
         RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_COUNT, NOT_IN_EMPTY] \\
        `h i <> {}` by METIS_TAC [] \\
         FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] \\
         qexistsl_tac [`x`, `i`] >> art []) \\
     REWRITE_TAC [in_right_open_intervals_nonempty] \\
     STRIP_TAC >> POP_ASSUM MP_TAC \\
     SIMP_TAC std_ss [GSPECIFICATION, right_open_interval, IN_BIGUNION_IMAGE,
                      IN_COUNT, Once EXTENSION] >> DISCH_TAC \\
  (* |- !x. (?x'. x' < n0 /\ x IN h x') <=> a <= x /\ x < b *)
     CCONTR_TAC \\ (* suppose there's a gap between h(i) and h(i+1) *)
    `i < SUC i` by RW_TAC arith_ss [] \\
     Q.PAT_X_ASSUM `!i j. i < j /\ j < n0 ==>
                          interval_upperbound (h i) <= interval_lowerbound (h j)`
       (MP_TAC o (Q.SPECL [`i`, `SUC i`])) \\
     Q.UNABBREV_TAC `n0` >> RW_TAC std_ss [] \\
  (* now prove by contradiction *)
     CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] \\
     Q.ABBREV_TAC `b1 = interval_upperbound (h i)` \\
     Q.ABBREV_TAC `a2 = interval_lowerbound (h (SUC i))` \\
    `b1 < a2` by METIS_TAC [REAL_LT_LE] \\ (* [a1, b1) < [a2, b2) *)
     Q.PAT_X_ASSUM `b1 <> a2` K_TAC \\
     Q.PAT_X_ASSUM `b1 <= a2` K_TAC \\
     qunabbrevl_tac [`b1`, `a2`] \\
     Know `h i <> {} /\ h i IN subsets right_open_intervals` >- PROVE_TAC [] \\
     DISCH_THEN (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [in_right_open_intervals_nonempty])) \\
     Know `h (SUC i) <> {} /\
           h (SUC i) IN subsets right_open_intervals` >- PROVE_TAC [] \\
     DISCH_THEN (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [in_right_open_intervals_nonempty])) \\
    `interval_upperbound (h i) = b'`
       by METIS_TAC [right_open_interval_upperbound] \\
    `interval_lowerbound (h (SUC i)) = a''`
       by METIS_TAC [right_open_interval_lowerbound] \\
     NTAC 2 (POP_ASSUM ((FULL_SIMP_TAC bool_ss) o wrap)) \\
     rename1 `h i       = right_open_interval a1 b1` \\
     rename1 `h (SUC i) = right_open_interval a2 b2` \\
     Know `a <= a1 /\ a1 < b`
     >- (`a1 IN right_open_interval a1 b1`
            by PROVE_TAC [right_open_interval_interior] \\
         PROVE_TAC []) >> STRIP_TAC \\
     Know `a <= a2 /\ a2 < b`
     >- (`a2 IN right_open_interval a2 b2`
            by PROVE_TAC [right_open_interval_interior] \\
         PROVE_TAC []) >> STRIP_TAC \\
  (* pick any point `z` in the "gap" *)
    `?z. b1 < z /\ z < a2` by PROVE_TAC [REAL_MEAN] \\
     Know `a <= z /\ z < b`
     >- (CONJ_TAC
         >- (MATCH_MP_TAC REAL_LT_IMP_LE \\
             MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `b1` >> art [] \\
             MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `a1` >> art []) \\
         MATCH_MP_TAC REAL_LT_TRANS \\
         Q.EXISTS_TAC `a2` >> art []) >> STRIP_TAC \\
     Q.ABBREV_TAC `n0 = LENGTH filtered` \\
    `?j. j < n0 /\ z IN h j` by METIS_TAC [] \\
  (* now we show `i < j < SUC i`, i.e. j doesn't exist at all *)
     Know `h j <> {} /\ h j IN subsets right_open_intervals` >- PROVE_TAC [] \\
     DISCH_THEN (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [in_right_open_intervals_nonempty])) \\
     rename1 `h j = right_open_interval a3 b3` \\
     Know `z IN right_open_interval a3 b3` >- PROVE_TAC [] \\
     DISCH_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [in_right_open_interval])) \\
     Know `i < j`
     >- (SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_LESS])) \\
         Know `interval_upperbound (h j) <= interval_upperbound (h i)`
         >- (`(j = i) \/ j < i` by RW_TAC arith_ss []
             >- (POP_ORW >> REWRITE_TAC [REAL_LE_REFL]) \\
             FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
        `(interval_upperbound (h j) = b3) /\
         (interval_upperbound (h i) = b1)` by PROVE_TAC [right_open_interval_upperbound] \\
         NTAC 2 (POP_ASSUM (PURE_ONCE_REWRITE_TAC o wrap)) >> DISCH_TAC \\
        `z < b1` by PROVE_TAC [REAL_LTE_TRANS] \\
         METIS_TAC [REAL_LT_ANTISYM]) >> DISCH_TAC \\
     Know `j < SUC i`
     >- (SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_LESS])) \\
         Know `interval_lowerbound (h (SUC i)) <= interval_lowerbound (h j)`
         >- (`(j = SUC i) \/ SUC i < j` by RW_TAC arith_ss []
             >- (POP_ORW >> REWRITE_TAC [REAL_LE_REFL]) \\
             FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
        `(interval_lowerbound (h (SUC i)) = a2) /\
         (interval_lowerbound (h j) = a3)` by PROVE_TAC [right_open_interval_lowerbound] \\
         NTAC 2 (POP_ASSUM (PURE_ONCE_REWRITE_TAC o wrap)) >> DISCH_TAC \\
        `z < a3` by PROVE_TAC [REAL_LTE_TRANS] \\
         METIS_TAC [REAL_LTE_ANTISYM]) >> DISCH_TAC \\
    `SUC i <= j` by RW_TAC arith_ss [] \\
     METIS_TAC [LESS_EQ_ANTISYM]) >> DISCH_TAC
 (* Part VI: final strike *)
 >> NTAC 3 (Q.PAT_X_ASSUM `!i j. i < j /\ j < n0 ==> A <= B` K_TAC)
 >> rpt STRIP_TAC
 >> Cases_on `i`
 >- (rw [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY] \\
     fs [semiring_def, space_def, subsets_def,
         positive_def, measurable_sets_def, measure_def])
 >> rename1 `SUC i <= n0`
 >> Suff `!j. SUC j <= n0 ==>
              BIGUNION (IMAGE h (count (SUC j))) <> {} /\
             (BIGUNION (IMAGE h (count (SUC j))) =
              right_open_interval (interval_lowerbound (h 0))
                                 (interval_upperbound (h j)))`
 >- (DISCH_THEN (MP_TAC o (Q.SPEC `i`)) \\
     RW_TAC std_ss [right_open_interval_in_intervals])
 >> Induct_on `j`
 >- (DISCH_TAC \\
     SIMP_TAC std_ss [COUNT_SUC, COUNT_ZERO, IMAGE_INSERT, BIGUNION_INSERT,
                      IMAGE_EMPTY, BIGUNION_EMPTY, UNION_EMPTY] \\
    `0 < n0` by RW_TAC arith_ss [] \\
     CONJ_TAC >- PROVE_TAC [] (* h 0 <> {} *) \\
     Know `h 0 <> {} /\ h 0 IN subsets right_open_intervals` >- PROVE_TAC [] \\
     DISCH_THEN (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [in_right_open_intervals_nonempty])) \\
     POP_ORW \\
     METIS_TAC [right_open_interval_lowerbound, right_open_interval_upperbound])
 >> DISCH_TAC
 >> `SUC j < n0 /\ SUC j <= n0` by RW_TAC arith_ss []
 >> Q.PAT_X_ASSUM `SUC j <= n0 ==> P` MP_TAC
 >> Q.UNABBREV_TAC `n0` >> RW_TAC std_ss []
 >- (SIMP_TAC std_ss [Once COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
     ASM_SET_TAC [])
 >> SIMP_TAC std_ss [Once COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT, Once UNION_COMM]
 >> `interval_lowerbound (h 0) < interval_upperbound (h j)`
       by METIS_TAC [right_open_interval_empty]
 >> Know `h (SUC j) <> {} /\ h (SUC j) IN subsets right_open_intervals`
 >- PROVE_TAC []
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                (REWRITE_RULE [in_right_open_intervals_nonempty])) >> art []
 >> `interval_upperbound (h j) = a`
       by METIS_TAC [right_open_interval_lowerbound]
 >> `interval_upperbound (right_open_interval a b) = b`
       by METIS_TAC [right_open_interval_upperbound]
 >> `interval_lowerbound (h (SUC j)) = interval_upperbound (h j)`
       by METIS_TAC []
 >> RW_TAC real_ss [right_open_interval, Once EXTENSION, IN_UNION, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC >> art [] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      MATCH_MP_TAC REAL_LT_TRANS \\
      Q.EXISTS_TAC `interval_upperbound (h j)` >> art [],
      (* goal 2 (of 3) *)
      MATCH_MP_TAC REAL_LT_IMP_LE \\
      MATCH_MP_TAC REAL_LTE_TRANS \\
      Q.EXISTS_TAC `interval_upperbound (h j)` >> art [],
      (* goal 3 (of 3) *)
      REWRITE_TAC [REAL_LTE_TOTAL] ]
QED

(* Proposition 6.3 [1, p.46], for constructing `lborel` by CARATHEODORY_SEMIRING *)
Theorem lborel0_premeasure :
    premeasure lborel0
Proof
    ASSUME_TAC lborel0_positive >> art [premeasure_def]
 >> RW_TAC std_ss [countably_additive_def, measurable_sets_def, measure_def,
                   IN_FUNSET, IN_UNIV]
 >> Know `!n. 0 <= (lambda0 o f) n`
 >- (RW_TAC std_ss [o_DEF] \\
     fs [positive_def, measure_def, measurable_sets_def]) >> DISCH_TAC
 >> Know `0 <= suminf (lambda0 o f)`
 >- (MATCH_MP_TAC ext_suminf_pos >> rw []) >> DISCH_TAC
 (* special case: finite non-empty sets *)
 >> ASSUME_TAC lborel0_finite_additive
 >> Q.ABBREV_TAC `P = \n. f n <> {}`
 >> Cases_on `?n. !i. n <= i ==> ~P i`
 >- (Q.UNABBREV_TAC `P` >> FULL_SIMP_TAC bool_ss [] \\
     Know `suminf (lambda0 o f) = SIGMA (lambda0 o f) (count n)`
     >- (MATCH_MP_TAC ext_suminf_sum >> RW_TAC std_ss [] \\
         fs [positive_def, measure_def, measurable_sets_def]) >> Rewr' \\
     Know `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f (count n))`
     >- (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_COUNT] \\
         EQ_TAC >> rpt STRIP_TAC >> rename1 `x IN f i` >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.EXISTS_TAC `i` >> art [] \\
           SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [NOT_LESS])) \\
           METIS_TAC [MEMBER_NOT_EMPTY],
           (* goal 2 (of 2) *)
           Q.EXISTS_TAC `i` >> art [] ]) \\
     DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap) \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                (Q.ISPEC `lborel0` FINITE_ADDITIVE)) \\
     RW_TAC std_ss [])
 (* `lborel1` construction *)
 >> Know `?lborel1. ((m_space lborel1, measurable_sets lborel1) =
                     smallest_ring (space right_open_intervals)
                                   (subsets right_open_intervals)) /\
                    (!s. s IN subsets right_open_intervals ==>
                        (measure lborel1 s = lambda0 s)) /\
                    positive lborel1 /\ additive lborel1`
 >- (MP_TAC (Q.ISPEC `lborel0` SEMIRING_FINITE_ADDITIVE_EXTENSION) \\
     MP_TAC right_open_intervals_semiring \\
     MP_TAC lborel0_positive \\
     MP_TAC lborel0_finite_additive \\
     RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def, SPACE])
 >> STRIP_TAC (* now we have `lborel1` in assumptions *)
 >> `ring (m_space lborel1,measurable_sets lborel1)`
       by METIS_TAC [SMALLEST_RING, right_open_intervals_semiring, semiring_def]
 >> `m_space lborel1 = univ(:real)`
       by METIS_TAC [SPACE, SPACE_SMALLEST_RING, right_open_intervals,
                     space_def, subsets_def]
 >> Know `subsets right_open_intervals SUBSET (measurable_sets lborel1)`
 >- (ASSUME_TAC
      (Q.ISPECL [`space right_open_intervals`,
                 `subsets right_open_intervals`] SMALLEST_RING_SUBSET_SUBSETS) \\
     Suff `measurable_sets lborel1 =
           subsets (smallest_ring (space right_open_intervals)
                                  (subsets right_open_intervals))` >- rw [] \\
     METIS_TAC [SPACE, space_def, subsets_def]) >> DISCH_TAC
 >> `finite_additive lborel1 /\ increasing lborel1 /\
     subadditive lborel1 /\ finite_subadditive lborel1`
       by METIS_TAC [RING_ADDITIVE_EVERYTHING]
 >> Q.ABBREV_TAC `lambda1 = measure lborel1`
 >> reverse (rw [GSYM le_antisym])
 (* easy part: suminf (lambda0 o f) <= lambda0 (BIGUNION (IMAGE f univ(:num))) *)
 >- (rw [ext_suminf_def, sup_le', GSPECIFICATION] \\
    `lambda0 (BIGUNION (IMAGE f univ(:num))) =
     lambda1 (BIGUNION (IMAGE f univ(:num)))` by PROVE_TAC [] >> POP_ORW \\
     Know `SIGMA (lambda0 o f) (count n) = SIGMA (lambda1 o f) (count n)`
     >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_EQ \\
         STRONG_CONJ_TAC
         >- rw [FINITE_COUNT, IN_COUNT, o_DEF] \\
         rw [] >> DISJ1_TAC >> GEN_TAC >> DISCH_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         fs [positive_def, measure_def, subsets_def]) >> Rewr' \\
     Know `BIGUNION (IMAGE f (count n)) IN measurable_sets lborel1`
     >- (MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                        (Q.ISPEC `(m_space lborel1, measurable_sets lborel1)`
                                 RING_FINITE_UNION_ALT)) >> rw [] \\
         fs [SUBSET_DEF]) >> DISCH_TAC \\
     Know `SIGMA (lambda1 o f) (count n) = lambda1 (BIGUNION (IMAGE f (count n)))`
     >- (Q.UNABBREV_TAC `lambda1` \\
         MATCH_MP_TAC (Q.SPEC `lborel`
                        (INST_TYPE [alpha |-> ``:real``] FINITE_ADDITIVE)) \\
         rw [] >> fs [SUBSET_DEF]) >> Rewr' \\
     Q.UNABBREV_TAC `lambda1` \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                    (Q.SPEC `lborel1`
                      (INST_TYPE [alpha |-> ``:real``] INCREASING))) \\
     rw [] >- SET_TAC [] \\
     fs [SUBSET_DEF])
 (* N is an infinite subset of UNIV, but it doesn't hold all non-empty sets *)
 >> `?N. INFINITE N /\ !n. n IN N ==> P n` by METIS_TAC [infinitely_often_lemma]
 >> Know `INFINITE P`
 >- (`N SUBSET P` by METIS_TAC [IN_APP, SUBSET_DEF] \\
     METIS_TAC [INFINITE_SUBSET]) >> DISCH_TAC
 (* N is useless from now on *)
 >> Q.PAT_X_ASSUM `INFINITE N`               K_TAC
 >> Q.PAT_X_ASSUM `!n. n IN N ==> P n`       K_TAC
 >> Q.PAT_X_ASSUM `~?n. !i. n <= i ==> ~P i` K_TAC
 >> Know `!n. n IN P <=> f n <> {}`
 >- (GEN_TAC >> Q.UNABBREV_TAC `P` >> EQ_TAC >> RW_TAC std_ss [IN_APP])
 >> DISCH_TAC
 >> Know `BIGUNION (IMAGE f UNIV) = BIGUNION (IMAGE f P)`
 >- (SIMP_TAC bool_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV] \\
     GEN_TAC >> EQ_TAC >> rpt STRIP_TAC >> rename1 `x IN f i` >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `i` >> art [GSYM MEMBER_NOT_EMPTY] \\
       Q.EXISTS_TAC `x` >> art [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `i` >> art [] ])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 (* use P instead of univ(:num) *)
 >> `countable P` by PROVE_TAC [COUNTABLE_NUM]
 >> POP_ASSUM (STRIP_ASSUME_TAC o
               (REWRITE_RULE [COUNTABLE_ALT_BIJ, GSYM ENUMERATE]))
 (* rewrite LHS, g is the BIJ enumeration of P *)
 >> rename1 `BIJ g univ(:num) P`
 >> Know `BIGUNION (IMAGE f P) = BIGUNION (IMAGE (f o g) UNIV)`
 >- (SIMP_TAC bool_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, o_DEF] \\
     GEN_TAC >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 `x IN f i` >> FULL_SIMP_TAC bool_ss [BIJ_DEF, SURJ_DEF, IN_UNIV] \\
      `?y. g y = i` by PROVE_TAC [] >> Q.EXISTS_TAC `y` >> art [],
       (* goal 2 (of 2) *)
       rename1 `x IN f (g i)` >> Q.PAT_X_ASSUM `!n. n IN P <=> f n <> {}` K_TAC \\
       Q.EXISTS_TAC `g i` >> art [] \\
       fs [BIJ_DEF, INJ_DEF, IN_UNIV] ])
 >> DISCH_THEN ((FULL_SIMP_TAC bool_ss) o wrap)
 >> Q.ABBREV_TAC `h = f o g`
 >> Know `!n. h n <> {}`
 >- (Q.UNABBREV_TAC `h` >> GEN_TAC >> SIMP_TAC bool_ss [o_DEF] \\
     Q.PAT_X_ASSUM `!n. n IN P <=> f n <> {}` (ONCE_REWRITE_TAC o wrap o GSYM) \\
     fs [BIJ_DEF, INJ_DEF, IN_UNIV]) >> DISCH_TAC
 (* h-properties in place of f-properties *)
 >> Know `!n. h n IN subsets right_open_intervals`
 >- (Q.UNABBREV_TAC `h` >> RW_TAC std_ss [o_DEF]) >> DISCH_TAC
 >> Know `!i j. i <> j ==> DISJOINT (h i) (h j)`
 >- (Q.UNABBREV_TAC `h` >> RW_TAC std_ss [o_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     CCONTR_TAC >> fs [BIJ_ALT, IN_FUNSET, IN_UNIV] \\
     METIS_TAC [EXISTS_UNIQUE_THM]) >> DISCH_TAC
 >> Know `!n. 0 <= (lambda0 o h) n`
 >- (Q.UNABBREV_TAC `h` >> GEN_TAC >> fs [o_DEF]) >> DISCH_TAC
 (* rewrite RHS, using `h` in place of `f` *)
 >> Know `suminf (lambda0 o f) = suminf (lambda0 o h)`
 >- (Q.UNABBREV_TAC `h` >> ASM_SIMP_TAC std_ss [ext_suminf_def] \\
     FULL_SIMP_TAC pure_ss [o_ASSOC] \\
     Q.ABBREV_TAC `l = lambda0 o f` \\
     Know `!n. SIGMA (l o g) (count n) = SIGMA l (IMAGE g (count n))`
     >- (GEN_TAC >> MATCH_MP_TAC EQ_SYM \\
         irule EXTREAL_SUM_IMAGE_IMAGE >> art [FINITE_COUNT] \\
         CONJ_TAC >- (DISJ1_TAC >> RW_TAC std_ss [IN_IMAGE, IN_COUNT] \\
                      MATCH_MP_TAC pos_not_neginf >> fs [o_DEF]) \\
         MATCH_MP_TAC INJ_IMAGE \\
         Q.EXISTS_TAC `P` >> fs [BIJ_DEF, INJ_DEF]) >> Rewr' \\
     RW_TAC std_ss [GSYM le_antisym, Once CONJ_SYM] >| (* 2 subgoals *)
     [ (* goal 1 (of 2): easy *)
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
       RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
       (* SIGMA l (IMAGE g (count n)) <= y,
          |- !z. (?n. z = SIGMA l (count n)) ==> z <= y

          The goal is to find an `m` such that

            (IMAGE g (count n)) SUBSET (count m) *)
       MATCH_MP_TAC le_trans \\
       Q.ABBREV_TAC `m = SUC (MAX_SET (IMAGE g (count n)))` \\
       Q.EXISTS_TAC `SIGMA l (count m)` \\
       reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                            Q.EXISTS_TAC `m` >> art []) \\
       Q.UNABBREV_TAC `m` \\
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
       ASM_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_COUNT] \\
       RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT] \\
       rename1 `i < n` \\
       Suff `g i <= MAX_SET (IMAGE g (count n))` >- RW_TAC arith_ss [] \\
       irule in_max_set \\ (* in pred_setTheory, contributed by CakeML *)
       RW_TAC std_ss [IMAGE_FINITE, FINITE_COUNT, IN_IMAGE, IN_COUNT] \\
       Q.EXISTS_TAC `i` >> art [],
       (* goal 2 (of 2): hard *)
       RW_TAC std_ss [sup_le', IN_IMAGE, IN_UNIV] \\
       RW_TAC std_ss [le_sup', IN_IMAGE, IN_UNIV] \\
       (* SIGMA l (count n) <= y
          |- !z. (?n. z = SIGMA l (IMAGE g (count n))) ==> z <= y

          The goal is to find an `m` such that

            (count n INTER P) SUBSET (IMAGE g (count m)) *)
       MATCH_MP_TAC le_trans \\
       IMP_RES_TAC BIJ_INV >> fs [IN_UNIV, o_DEF] \\
       Q.ABBREV_TAC `m = SUC (MAX_SET (IMAGE g' (count n INTER P)))` \\
       Q.EXISTS_TAC `SIGMA l (IMAGE g (count m))` \\
       reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                            Q.EXISTS_TAC `m` >> art []) \\
       Q.UNABBREV_TAC `m` \\
       Know `SIGMA l (count n) = SIGMA l (count n INTER P)`
       >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_INTER_ELIM \\
           REWRITE_TAC [FINITE_COUNT] \\
           CONJ_TAC >- (Q.UNABBREV_TAC `l` >> BETA_TAC >> rpt STRIP_TAC \\
                       `f x = {}` by PROVE_TAC [] >> POP_ORW \\
                        fs [positive_def, measure_def, measurable_sets_def]) \\
           DISJ1_TAC >> NTAC 2 STRIP_TAC \\
           MATCH_MP_TAC pos_not_neginf >> art []) >> Rewr' \\
       MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
       ASM_SIMP_TAC std_ss [IMAGE_FINITE, FINITE_COUNT] \\
       CONJ_TAC >- (MATCH_MP_TAC SUBSET_FINITE_I \\
                    Q.EXISTS_TAC `count n` >> rw [FINITE_COUNT, INTER_SUBSET]) \\
       SIMP_TAC bool_ss [SUBSET_DEF, IN_IMAGE, IN_COUNT, IN_INTER] \\
       Q.X_GEN_TAC `i` >> STRIP_TAC \\
       Q.EXISTS_TAC `g' i` >> ASM_SIMP_TAC bool_ss [] \\
       Suff `g' i <= MAX_SET (IMAGE g' (count n INTER P))` >- RW_TAC arith_ss [] \\
       irule in_max_set \\
       CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE \\
                    MATCH_MP_TAC SUBSET_FINITE_I \\
                    Q.EXISTS_TAC `count n` >> rw [FINITE_COUNT, INTER_SUBSET]) \\
       SIMP_TAC std_ss [IN_IMAGE, IN_COUNT, IN_INTER] \\
       Q.EXISTS_TAC `i` >> art [] ]) >> Rewr'
 (* cleanup all f-properties *)
 >> Q.PAT_X_ASSUM `!x. f x IN subsets right_open_intervals` K_TAC
 >> Q.PAT_X_ASSUM `!n. 0 <= (lambda0 o f) n`                K_TAC
 >> Q.PAT_X_ASSUM `0 <= suminf (lambda0 o f)`               K_TAC
 >> Q.PAT_X_ASSUM `!i j. i <> j ==> DISJOINT (f i) (f j)`   K_TAC
 (* hard part: lambda0 (BIGUNION (IMAGE h univ(:num))) <= suminf (lambda0 o h) *)
 >> `0 <= suminf (lambda0 o h)` by PROVE_TAC [ext_suminf_pos]
 >> Know `BIGUNION (IMAGE h UNIV) <> {}`
 >- (RW_TAC std_ss [Once EXTENSION, NOT_IN_EMPTY, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `h 0 <> {}` by PROVE_TAC [] >> fs [GSYM MEMBER_NOT_EMPTY] \\
     qexistsl_tac [`x`, `0`] >> art []) >> DISCH_TAC
 >> Know `?a b. BIGUNION (IMAGE h UNIV) = right_open_interval a b`
 >- (Q.PAT_X_ASSUM `BIGUNION (IMAGE h UNIV) IN subsets right_open_intervals`
       (MP_TAC o
        (REWRITE_RULE [right_open_intervals, right_open_interval, subsets_def])) \\
     RW_TAC set_ss [right_open_interval]) >> STRIP_TAC
 >> `a < b` by PROVE_TAC [right_open_interval_empty]
 (* stage work *)
 >> MATCH_MP_TAC le_epsilon >> rpt STRIP_TAC
 >> reverse (Cases_on `e < Normal (b - a)`)
 >- (POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [extreal_lt_def])) \\
     IMP_RES_TAC REAL_LT_IMP_LE >> rw [lambda0_def] \\
     MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `e` >> rw [] \\
     MATCH_MP_TAC le_addl_imp >> art [])
 >> Know `e <> NegInf`
 >- (MATCH_MP_TAC pos_not_neginf \\
     MATCH_MP_TAC lt_imp_le >> art []) >> DISCH_TAC
 >> Know `lambda0 (BIGUNION (IMAGE h UNIV)) <= suminf (lambda0 o h) + e <=>
          lambda0 (BIGUNION (IMAGE h UNIV)) - e <= suminf (lambda0 o h)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC sub_le_eq >> art []) >> Rewr'
 >> `?d. e = Normal d` by METIS_TAC [extreal_cases]
 >> `0 < d` by METIS_TAC [extreal_lt_eq, extreal_of_num_def]
 >> Q.PAT_X_ASSUM `0 < e`            K_TAC
 >> Q.PAT_X_ASSUM `INFINITE P`       K_TAC
 >> Q.PAT_X_ASSUM `!n. n IN P <=> _` K_TAC
 >> Q.PAT_X_ASSUM `BIJ g UNIV P`     K_TAC
 >> Q.UNABBREV_TAC `P` (* last appearence of P *)
 (* (A n) and (B n) are lower- and upperbounds of each non-empty (h n) *)
 >> Know `?A B. !n. h n = right_open_interval (A n) (B n)`
 >- (Q.PAT_X_ASSUM `!x. h x IN subsets right_open_intervals`
       (MP_TAC o (REWRITE_RULE [right_open_intervals, right_open_interval, subsets_def])) \\
     RW_TAC set_ss [right_open_interval, SKOLEM_THM]) >> STRIP_TAC
 >> `!n. A n < B n` by METIS_TAC [right_open_interval_empty]
 >> Know `!i j. i <> j ==> B i <> B j`
 >- (rpt STRIP_TAC >> `A i < B i /\ A j < B j` by PROVE_TAC [] \\
    `(A i = A j) \/ A i < A j \/ A j < A i` by PROVE_TAC [REAL_LT_TOTAL] >|
     [ (* goal 1 (of 3) *)
      `h i = h j` by PROVE_TAC [] >> METIS_TAC [DISJOINT_EMPTY_REFL],
       (* goal 2 (of 3): [A i, [A j, B i/j)) *)
      `DISJOINT (h i) (h j)` by PROVE_TAC [] \\
       METIS_TAC [real_lte, right_open_interval_DISJOINT_imp],
       (* goal 3 (of 3): [A j, [A i, B i/j)) *)
      `DISJOINT (h i) (h j)` by PROVE_TAC [] \\
       METIS_TAC [real_lte, right_open_interval_DISJOINT_imp] ]) >> DISCH_TAC
 (* "open" (J) and "half open" (H) intervals of the same bounds *)
 >> Q.ABBREV_TAC `r = d / 2`
 >> Know `0 < r`
 >- (Q.UNABBREV_TAC `r` >> MATCH_MP_TAC REAL_LT_DIV \\
     RW_TAC real_ss [] (* 0 < 2 *)) >> DISCH_TAC
 >> Q.ABBREV_TAC `J = \n.      OPEN_interval (A n - r * (1 / 2) pow (n + 1),  B n)`
 >> Q.ABBREV_TAC `H = \n. right_open_interval (A n - r * (1 / 2) pow (n + 1)) (B n)`
 >> Know `!n. A n - r * (1 / 2) pow (n + 1) < B n`
 >- (GEN_TAC >> MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `A n` \\
     ASM_REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR] \\
     REWRITE_TAC [Once ADD_COMM, GSYM SUC_ONE_ADD] \\
     METIS_TAC [REAL_HALF_BETWEEN, POW_POS_LT, REAL_LT_MUL]) >> DISCH_TAC
 >> Know `!n. J n SUBSET H n`
 >- (GEN_TAC >> qunabbrevl_tac [`J`, `H`] >> BETA_TAC \\
     RW_TAC std_ss [SUBSET_DEF, IN_INTERVAL, in_right_open_interval] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> DISCH_TAC
 >> Know `!n. J n <> {}`
 >- (GEN_TAC >> Q.UNABBREV_TAC `J` \\
     BETA_TAC >> art [INTERVAL_NE_EMPTY]) >> DISCH_TAC
 >> Know `!n. H n <> {}`
 >- (GEN_TAC >> Q.UNABBREV_TAC `H` \\
     BETA_TAC >> art [right_open_interval_empty]) >> DISCH_TAC
 >> Know `!m n. m <> n ==> J m <> J n`
 >- (Q.UNABBREV_TAC `J` >> BETA_TAC >> rpt STRIP_TAC \\
     METIS_TAC [EQ_INTERVAL]) >> DISCH_TAC
 >> Know `!m n. m <> n ==> H m <> H n`
 >- (Q.UNABBREV_TAC `H` >> BETA_TAC >> rpt STRIP_TAC \\
     METIS_TAC [right_open_interval_11]) >> DISCH_TAC
 (* applying Heine-Borel theorem *)
 >> Know `compact (interval [a, b - r])`
 >- (MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT \\
     REWRITE_TAC [BOUNDED_INTERVAL, CLOSED_INTERVAL])
 >> DISCH_THEN (ASSUME_TAC o (MATCH_MP COMPACT_IMP_HEINE_BOREL))
 >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `IMAGE J univ(:num)`))
 >> Know `!t. t IN (IMAGE J univ(:num)) ==> open t`
 >- (RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     Q.UNABBREV_TAC `J` >> SIMP_TAC std_ss [OPEN_INTERVAL]) >> DISCH_TAC
 >> Know `BIGUNION (IMAGE h UNIV) SUBSET BIGUNION (IMAGE J UNIV)`
 >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV,
                    in_right_open_interval] \\
     rename1 `A i <= x` >> Q.EXISTS_TAC `i` \\
     Q.UNABBREV_TAC `J` >> RW_TAC std_ss [OPEN_interval, GSPECIFICATION] \\
     MATCH_MP_TAC REAL_LTE_TRANS \\
     Q.EXISTS_TAC `A i` >> art [] \\
     REWRITE_TAC [Once ADD_COMM, GSYM SUC_ONE_ADD] \\
     REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR] \\
     METIS_TAC [REAL_HALF_BETWEEN, POW_POS_LT, REAL_LT_MUL]) >> DISCH_TAC
 (* all "open" intervals J cover the compact interval [a, b - r] *)
 >> Know `(CLOSED_interval [a, b - r]) SUBSET (BIGUNION (IMAGE J univ(:num)))`
 >- (MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC `BIGUNION (IMAGE h UNIV)` >> art [] \\
     RW_TAC list_ss [CLOSED_interval, right_open_interval, SUBSET_DEF, GSPECIFICATION] \\
     MATCH_MP_TAC REAL_LET_TRANS \\
     Q.EXISTS_TAC `b - r` >> art [REAL_LT_SUB_RADD, REAL_LT_ADDR]) >> DISCH_TAC
 (* there exists a finite cover c from J (by Heine-Borel theorem) *)
 >> `?c. c SUBSET (IMAGE J univ(:num)) /\ FINITE c /\
         CLOSED_interval [a,b - r] SUBSET (BIGUNION c)` by PROVE_TAC []
 >> Q.PAT_X_ASSUM `X ==> ?f'. f' SUBSET (IMAGE J UNIV) /\ Y` K_TAC
 >> Know `BIJ J univ(:num) (IMAGE J univ(:num))`
 >- (RW_TAC std_ss [BIJ_ALT, IN_FUNSET, IN_UNIV, IN_IMAGE, EXISTS_UNIQUE_THM]
     >- (Q.EXISTS_TAC `x` >> art []) \\
     METIS_TAC [])
 >> DISCH_THEN (STRIP_ASSUME_TAC o
                (SIMP_RULE std_ss [IN_UNIV, IN_IMAGE]) o (MATCH_MP BIJ_INV))
 >> rename1 `!x. J' (J x) = x`
 >> Know `?cover. FINITE cover /\ (c = IMAGE J cover)`
 >- (Q.EXISTS_TAC `IMAGE J' c` \\
     CONJ_TAC >- METIS_TAC [IMAGE_FINITE] \\
     REWRITE_TAC [IMAGE_IMAGE] \\
     RW_TAC std_ss [Once EXTENSION, IN_IMAGE] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `x` >> art [] \\
       MATCH_MP_TAC EQ_SYM >> FIRST_X_ASSUM MATCH_MP_TAC \\
       fs [SUBSET_DEF, IN_IMAGE, IN_UNIV],
       (* goal 2 (of 2) *)
       Suff `J (J' x') = x'` >- PROVE_TAC [] \\
       FIRST_X_ASSUM MATCH_MP_TAC \\
       fs [SUBSET_DEF, IN_IMAGE, IN_UNIV] ]) >> STRIP_TAC
 >> POP_ASSUM ((REV_FULL_SIMP_TAC bool_ss) o wrap)
 >> Q.PAT_X_ASSUM `FINITE (IMAGE J cover)` K_TAC
 (* `N` is the minimal index such that `cover SUBSET (count N)` *)
 >> Q.ABBREV_TAC `N = SUC (MAX_SET cover)`
 >> Know `cover SUBSET (count N)` (* for IMAGE_SUBSET *)
 >- (Q.UNABBREV_TAC `N` \\
     RW_TAC std_ss [SUBSET_DEF, IN_COUNT] \\
     Suff `x <= MAX_SET cover` >- RW_TAC arith_ss [] \\
     irule in_max_set >> art []) >> DISCH_TAC
 (* RHS: from `suminf lambda0 o h` to `SIGMA (lambda0 o h) (count N)` *)
 >> ASM_SIMP_TAC bool_ss [ext_suminf_def, le_sup', IN_IMAGE, IN_UNIV, IN_COUNT]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC le_trans
 >> Q.EXISTS_TAC `SIGMA (lambda0 o h) (count N)`
 >> reverse CONJ_TAC
 >- (POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC `N` >> art [])
  (* now there's no infinity anywhere *)
 >> ASSUME_TAC lborel0_additive
 >> Know `lambda0 (right_open_interval a       b) =
          lambda0 (right_open_interval a (b - r)) +
          lambda0 (right_open_interval (b - r) b)`
 >- (MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                (Q.ISPEC `lborel0` ADDITIVE)) \\
     ASM_SIMP_TAC bool_ss [right_open_interval_in_intervals] \\
     Know `a < b - r /\ b - r < b`
     >- (ASM_REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR] \\
        `a < b - r <=> r < b - a` by REAL_ARITH_TAC >> POP_ORW \\
         MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `d` \\
         reverse CONJ_TAC >- fs [extreal_lt_eq] \\
         Q.UNABBREV_TAC `r` \\
         MATCH_MP_TAC REAL_LE_LDIV >> RW_TAC real_ss [] \\
         MATCH_MP_TAC (SIMP_RULE real_ss []
                                 (Q.SPECL [`d`, `d`, `1`, `2`] REAL_LE_MUL2)) \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> STRIP_TAC \\
     CONJ_TAC >- (METIS_TAC [right_open_interval_DISJOINT,
                             REAL_LE_REFL, REAL_LT_IMP_LE]) \\
     RW_TAC std_ss [Once EXTENSION, IN_UNION, in_right_open_interval] \\
     EQ_TAC >> STRIP_TAC >> fs [REAL_LTE_TOTAL] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `b - r` >> art [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `b - r` >> art [] \\
       MATCH_MP_TAC REAL_LT_IMP_LE >> art [] ]) >> Rewr'
 >> Know `lambda0 (right_open_interval (b - r) b) = Normal r`
 >- (Know `Normal r = Normal (b - (b - r))`
     >- (REWRITE_TAC [extreal_11] >> REAL_ARITH_TAC) >> Rewr' \\
     MATCH_MP_TAC lambda0_def \\
     REWRITE_TAC [REAL_LE_SUB_RADD, REAL_LE_ADDR] \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr'
 >> Know `right_open_interval a (b - r) SUBSET (BIGUNION (IMAGE H (count N)))`
 >- ((* step 1 (of 4) *)
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC `interval [a,b - r]` \\
     CONJ_TAC (* [a,b - r) SUBSET [a,b - r] *)
     >- (RW_TAC std_ss [SUBSET_DEF, IN_INTERVAL, in_right_open_interval] \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     (* step 2 (of 4) *)
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC `BIGUNION (IMAGE J cover)` >> art [] \\
     (* step 3 (of 4) *)
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC `BIGUNION (IMAGE J (count N))` \\
     CONJ_TAC >- (MATCH_MP_TAC SUBSET_BIGUNION \\
                  MATCH_MP_TAC IMAGE_SUBSET >> art []) \\
     (* step 4 (of 4) *)
     RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_COUNT] \\
     rename1 `i < N` >> Q.EXISTS_TAC `i` >> art [] \\
     fs [SUBSET_DEF]) >> DISCH_TAC
 >> Know `lambda0 (right_open_interval a (b - r)) <= SIGMA (lambda0 o H) (count N)`
 >- (MATCH_MP_TAC le_trans \\
     Q.EXISTS_TAC `lambda1 (BIGUNION (IMAGE H (count N)))` \\
    `lambda0 (right_open_interval a (b - r)) =
     lambda1 (right_open_interval a (b - r))`
        by METIS_TAC [right_open_interval_in_intervals] >> POP_ORW \\
     CONJ_TAC (* by "increasing" *)
     >- (Q.UNABBREV_TAC `lambda1` \\
         MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                        (Q.SPEC `lborel1`
                          (INST_TYPE [alpha |-> ``:real``] INCREASING))) \\
         ASM_SIMP_TAC bool_ss [] \\
         CONJ_TAC >- METIS_TAC [SUBSET_DEF, in_right_open_intervals] \\
         MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                    (Q.ISPEC `(m_space lborel1,measurable_sets lborel1)`
                                             RING_FINITE_UNION)) \\
         ASM_SIMP_TAC bool_ss [IMAGE_FINITE, FINITE_COUNT, IN_IMAGE, IN_COUNT,
                               SUBSET_DEF] \\
         rpt STRIP_TAC >> rename1 `s = H i` \\
         METIS_TAC [SUBSET_DEF, in_right_open_intervals]) \\
     Know `SIGMA (lambda0 o H) (count N) = SIGMA (lambda1 o H) (count N)`
     >- (MATCH_MP_TAC EQ_SYM >> irule EXTREAL_SUM_IMAGE_EQ \\
         STRONG_CONJ_TAC
         >- (RW_TAC std_ss [IN_COUNT, FINITE_COUNT, o_DEF] \\
             METIS_TAC [right_open_interval_in_intervals]) \\
         RW_TAC std_ss [FINITE_COUNT] \\
         DISJ1_TAC >> NTAC 2 STRIP_TAC \\
         MATCH_MP_TAC pos_not_neginf \\
         fs [positive_def, measure_def, measurable_sets_def] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         METIS_TAC [right_open_interval_in_intervals]) >> Rewr' \\
     (* by "finite additive" *)
     Q.UNABBREV_TAC `lambda1` \\
     MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                    (Q.SPEC `lborel1`
                      (INST_TYPE [alpha |-> ``:real``] FINITE_SUBADDITIVE))) \\
     ASM_SIMP_TAC bool_ss [] \\
     rpt STRIP_TAC >- METIS_TAC [SUBSET_DEF, in_right_open_intervals] \\
     MATCH_MP_TAC (REWRITE_RULE [subsets_def]
                                (Q.ISPEC `(m_space lborel1,measurable_sets lborel1)`
                                         RING_FINITE_UNION)) \\
     ASM_SIMP_TAC bool_ss [IMAGE_FINITE, FINITE_COUNT, IN_IMAGE, IN_COUNT, SUBSET_DEF] \\
     rpt STRIP_TAC >> rename1 `s = H i` \\
     METIS_TAC [SUBSET_DEF, in_right_open_intervals]) >> DISCH_TAC
 (* H and h *)
 >> Know `!n. lambda0 (right_open_interval (A n - r * (1 / 2) pow (n + 1)) (A n)) =
              Normal (r * (1 / 2) pow (n + 1))`
 >- (GEN_TAC \\
    `r * (1 / 2) pow (n + 1) = A n - (A n - r * (1 / 2) pow (n + 1))`
       by REAL_ARITH_TAC \\
     POP_ASSUM ((GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
     MATCH_MP_TAC lambda0_def \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     REWRITE_TAC [REAL_LT_SUB_RADD, REAL_LT_ADDR] \\
     MATCH_MP_TAC REAL_LT_MUL >> art [POW_HALF_POS]) >> DISCH_TAC
 (* rewrite `lambda0 o h` by `lambda0 o H` and the rest *)
 >> Q.ABBREV_TAC `D = (\n. right_open_interval (A n - r * (1 / 2) pow (n + 1)) (A n))`
 >> Know `lambda0 o h = \n. (lambda0 o H) n - (lambda0 o D) n`
 >- (Q.UNABBREV_TAC `D` \\
     FUN_EQ_TAC >> Q.X_GEN_TAC `n` >> SIMP_TAC std_ss [o_DEF] >> art [] \\
     REWRITE_TAC [eq_sub_ladd_normal] \\
     POP_ASSUM (ONCE_REWRITE_TAC o wrap o GSYM) \\
     MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC (REWRITE_RULE [measure_def, measurable_sets_def]
                                (Q.ISPEC `lborel0` ADDITIVE)) \\
     Q.UNABBREV_TAC `H` \\
     ASM_SIMP_TAC bool_ss [right_open_interval_in_intervals] \\
     Know `0 < r * (1 / 2) pow (n + 1)`
     >- (MATCH_MP_TAC REAL_LT_MUL >> art [POW_HALF_POS]) >> DISCH_TAC \\
     CONJ_TAC (* DISJOINT *)
     >- (ONCE_REWRITE_TAC [DISJOINT_SYM] \\
         MATCH_MP_TAC right_open_interval_DISJOINT \\
         RW_TAC std_ss [REAL_LE_REFL] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC REAL_LT_IMP_LE >> art [REAL_LT_SUB_RADD, REAL_LT_ADDR],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC REAL_LT_IMP_LE >> art [] ]) \\
     RW_TAC std_ss [Once EXTENSION, IN_UNION, in_right_open_interval] \\
     EQ_TAC >> rpt STRIP_TAC >> RW_TAC std_ss [REAL_LET_TOTAL] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC `A n` >> art [] \\
       MATCH_MP_TAC REAL_LT_IMP_LE >> art [REAL_LT_SUB_RADD, REAL_LT_ADDR],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `A n` >> art [] ]) >> Rewr'
 (* simplify extreal$SIGMA (EXTREAL_SUM_IMAGE) *)
 >> Know `SIGMA (\n. (lambda0 o H) n - (lambda0 o D) n) (count N) =
          SIGMA (lambda0 o H) (count N) - SIGMA (lambda0 o D) (count N)`
 >- (irule EXTREAL_SUM_IMAGE_SUB >> REWRITE_TAC [FINITE_COUNT, IN_COUNT] \\
     DISJ1_TAC (* this one is easier *) \\
     Q.X_GEN_TAC `n` >> Q.UNABBREV_TAC `D` >> SIMP_TAC std_ss [o_DEF] \\
     DISCH_TAC \\
     reverse CONJ_TAC >- (Q.PAT_X_ASSUM `!n. lambda0 _ = Normal _`
                            (ONCE_REWRITE_TAC o wrap) \\
                          REWRITE_TAC [extreal_not_infty]) \\
     MATCH_MP_TAC pos_not_neginf \\
     Q.UNABBREV_TAC `H` >> BETA_TAC \\
     Know `lambda0 (right_open_interval (A n - r * (1 / 2) pow (n + 1)) (B n)) =
           Normal (B n - (A n - r * (1 / 2) pow (n + 1)))`
     >- (MATCH_MP_TAC lambda0_def \\
         MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr' \\
     REWRITE_TAC [extreal_le_eq, extreal_of_num_def] \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
     ASM_REWRITE_TAC [REAL_LT_SUB_LADD, REAL_ADD_LID]) >> Rewr'
 >> Know `SIGMA (lambda0 o D) (count N) =
          SIGMA (\n. Normal (r * (1 / 2) pow (n + 1))) (count N)`
 >- (Q.UNABBREV_TAC `D` >> ASM_SIMP_TAC std_ss [o_DEF]) >> Rewr'
 >> Q.UNABBREV_TAC `D` (* D is not needed any more *)
 >> POP_ASSUM K_TAC
 >> Know `SIGMA (\n. Normal ((\n. r * (1 / 2) pow (n + 1)) n)) (count N) =
               Normal (SIGMA (\n. r * (1 / 2) pow (n + 1))     (count N))`
 >- (MATCH_MP_TAC EXTREAL_SUM_IMAGE_NORMAL \\
     REWRITE_TAC [FINITE_COUNT]) >> BETA_TAC >> Rewr'
 (* fallback to real_sigma$SIGMA (REAL_SUM_IMAGE) *)
 >> Know `REAL_SUM_IMAGE (\n. r * ((\n. (1 / 2) pow (n + 1)) n)) (count N) =
                r * REAL_SUM_IMAGE (\n. (1 / 2) pow (n + 1))     (count N)`
 >- (MATCH_MP_TAC REAL_SUM_IMAGE_CMUL \\
     REWRITE_TAC [FINITE_COUNT]) >> BETA_TAC >> Rewr'
 >> Know `REAL_SUM_IMAGE (\n. (1 / 2) pow (n + 1)) (count N) <
          suminf (\n. (1 / 2) pow (n + 1))`
 >- (REWRITE_TAC [REAL_SUM_IMAGE_COUNT] \\
     MATCH_MP_TAC SER_POS_LT \\
     CONJ_TAC >- (MATCH_MP_TAC SUM_SUMMABLE \\
                  Q.EXISTS_TAC `1` >> REWRITE_TAC [POW_HALF_SER]) \\
     RW_TAC std_ss [Once ADD_COMM, GSYM SUC_ONE_ADD] \\
     METIS_TAC [REAL_HALF_BETWEEN, POW_POS_LT])
 >> Know `suminf (\n. (1 / 2) pow (n + 1)) = (1 :real)`
 >- (MATCH_MP_TAC EQ_SYM \\
     MATCH_MP_TAC SUM_UNIQ >> REWRITE_TAC [POW_HALF_SER]) >> Rewr'
 >> DISCH_TAC
 >> Know `Normal (r * SIGMA (\n. (1 / 2) pow (n + 1)) (count N)) < Normal r`
 >- (REWRITE_TAC [extreal_lt_eq] \\
     MATCH_MP_TAC (REWRITE_RULE [REAL_MUL_RID]
                    (Q.SPECL [`r`, `SIGMA (\n. (1 / 2) pow (n + 1)) (count N)`,
                              `1`] REAL_LT_LMUL_IMP)) >> art [])
 >> POP_ASSUM K_TAC >> DISCH_TAC
 (* clean up all ring assumptions *)
 >> Q.PAT_X_ASSUM `ring _` K_TAC
 >> Q.PAT_X_ASSUM `_ = smallest_ring _ _` K_TAC
 >> Q.PAT_X_ASSUM `subsets right_open_intervals SUBSET measurable_sets lborel1` K_TAC
 >> Q.PAT_X_ASSUM `finite_additive lborel1` K_TAC
 >> Q.PAT_X_ASSUM `positive lborel1` K_TAC
 >> Q.PAT_X_ASSUM `additive lborel1` K_TAC
 >> Q.PAT_X_ASSUM `increasing lborel1` K_TAC
 >> Q.PAT_X_ASSUM `subadditive lborel1` K_TAC
 >> Q.PAT_X_ASSUM `finite_subadditive lborel1` K_TAC
 >> Q.PAT_X_ASSUM `!s. P ==> (lambda1 s = lambda0 s)` K_TAC
 >> Q.PAT_X_ASSUM `m_space lborel1 = UNIV` K_TAC
 >> Q.UNABBREV_TAC `lambda1`
 (* final extreal arithmetics *)
 >> Know `lambda0 (right_open_interval a (b - r)) = Normal (b - r - a)`
 >- (MATCH_MP_TAC lambda0_def \\
     MATCH_MP_TAC REAL_LT_IMP_LE \\
    `a < b - r <=> r < b - a` by REAL_ARITH_TAC >> POP_ORW \\
     MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `d` \\
     reverse CONJ_TAC >- fs [extreal_lt_eq] \\
     Q.UNABBREV_TAC `r` \\
     MATCH_MP_TAC REAL_LE_LDIV >> RW_TAC real_ss [] \\
     MATCH_MP_TAC (SIMP_RULE real_ss []
                             (Q.SPECL [`d`, `d`, `1`, `2`] REAL_LE_MUL2)) \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> DISCH_THEN ((FULL_SIMP_TAC std_ss) o wrap)
 >> Q.ABBREV_TAC `r1 = b - r - a`
 >> Q.ABBREV_TAC `R2 = SIGMA (lambda0 o H) (count N)`
 >> Know `R2 <> NegInf /\ R2 <> PosInf`
 >- (Q.UNABBREV_TAC `R2` \\
     CONJ_TAC (* positive *)
     >- (MATCH_MP_TAC pos_not_neginf \\
         irule EXTREAL_SUM_IMAGE_POS >> art [FINITE_COUNT] \\
         Q.UNABBREV_TAC `H` \\
         Q.X_GEN_TAC `i`>> RW_TAC std_ss [IN_COUNT, o_DEF] \\
         fs [positive_def, measure_def, measurable_sets_def] \\
         FIRST_X_ASSUM MATCH_MP_TAC \\
         REWRITE_TAC [right_open_interval_in_intervals]) \\
     (* finiteness *)
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF >> art [FINITE_COUNT] \\
     Q.UNABBREV_TAC `H` \\
     Q.X_GEN_TAC `i`>> SIMP_TAC std_ss [IN_COUNT, o_DEF] \\
     DISCH_TAC >> PROVE_TAC [lambda0_not_infty]) >> STRIP_TAC
 >> `?r2. R2 = Normal r2` by METIS_TAC [extreal_cases]
 >> Q.ABBREV_TAC `r3 = REAL_SUM_IMAGE (\n. (1 / 2) pow (n + 1)) (count N)`
 >> FULL_SIMP_TAC std_ss [extreal_le_eq, extreal_lt_eq,
                          extreal_add_def, extreal_sub_def]
 (* final real arithmetics *)
 >> Q.PAT_X_ASSUM `r1 <= r2` MP_TAC
 >> Q.PAT_X_ASSUM `r * r3 < r` MP_TAC
 >> Know `d = r * 2`
 >- (Q.UNABBREV_TAC `r` \\
     MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC REAL_DIV_RMUL \\
     RW_TAC real_ss []) >> Rewr'
 >> KILL_TAC >> REAL_ARITH_TAC
QED

(* Borel measure space with the household Lebesgue measure (lborel),
   constructed directly by Caratheodory's Extension Theorem.
 *)
local
  val thm = prove (
    ``?m. (!s. s IN subsets right_open_intervals ==> (measure m s = lambda0 s)) /\
          ((m_space m, measurable_sets m) = borel) /\ measure_space m``,
   (* proof *)
      MP_TAC (Q.ISPEC `lborel0` CARATHEODORY_SEMIRING) \\
      MP_TAC right_open_intervals_semiring \\
      MP_TAC right_open_intervals_sigma_borel \\
      MP_TAC lborel0_premeasure \\
      RW_TAC std_ss [m_space_def, measurable_sets_def, measure_def, SPACE] \\
      Q.EXISTS_TAC `m` >> art []);
in
  (* |- (!s. s IN subsets right_open_intervals ==> lambda s = lambda0 s) /\
        (m_space lborel,measurable_sets lborel) = borel /\
        measure_space lborel *)
  val lborel_def = new_specification ("lborel_def", ["lborel"], thm);
end;

Theorem space_lborel :
    m_space lborel = univ(:real)
Proof
    PROVE_TAC [lborel_def, GSYM SPACE, CLOSED_PAIR_EQ, space_borel]
QED

Theorem m_space_lborel :
    m_space lborel = space borel
Proof
    PROVE_TAC [lborel_def, GSYM SPACE, CLOSED_PAIR_EQ]
QED

Theorem sets_lborel :
    measurable_sets lborel = subsets borel
Proof
    PROVE_TAC [lborel_def, GSYM SPACE, CLOSED_PAIR_EQ]
QED

(* give `measure lebesgue` a special symbol (cf. `lambda0`) *)
val _ = overload_on ("lambda", ``measure lborel``);

Theorem lambda_empty :
    lambda {} = 0
Proof
    ASSUME_TAC right_open_intervals_semiring
 >> `{} IN subsets right_open_intervals` by PROVE_TAC [semiring_def]
 >> `lambda {} = lambda0 {}` by PROVE_TAC [lborel_def]
 >> POP_ORW >> REWRITE_TAC [lambda0_empty]
QED

Theorem lambda_prop :
    !a b. a <= b ==> (lambda (right_open_interval a b) = Normal (b - a))
Proof
    rpt STRIP_TAC
 >> Know `(right_open_interval a b) IN subsets right_open_intervals`
 >- (RW_TAC std_ss [subsets_def, right_open_intervals, GSPECIFICATION, IN_UNIV] \\
     Q.EXISTS_TAC `(a,b)` >> SIMP_TAC std_ss [])
 >> RW_TAC std_ss [lborel_def, lambda0_def, measure_def]
QED

Theorem lambda_not_infty :
    !a b. lambda (right_open_interval a b) <> PosInf /\
          lambda (right_open_interval a b) <> NegInf
Proof
    rpt GEN_TAC
 >> Know `lambda (right_open_interval a b) = lambda0 (right_open_interval a b)`
 >- (`right_open_interval a b IN subsets right_open_intervals`
       by PROVE_TAC [right_open_interval_in_intervals] \\
     PROVE_TAC [lborel_def]) >> Rewr'
 >> PROVE_TAC [lambda0_not_infty]
QED

(* |- measure_space lborel *)
val measure_space_lborel = save_thm
  ("measure_space_lborel", List.nth (CONJUNCTS lborel_def, 2));

(* first step beyond right-open_intervals *)
Theorem lambda_sing :
    !c. lambda {c} = 0
Proof
    GEN_TAC
 >> Q.ABBREV_TAC `f = \n. right_open_interval (c - (1/2) pow n) (c + (1/2) pow n)`
 >> Know `{c} = BIGINTER (IMAGE f UNIV)`
 >- (Q.UNABBREV_TAC `f` \\
     REWRITE_TAC [right_open_interval, REAL_SING_BIGINTER]) >> Rewr'
 >> Know `0 = inf (IMAGE (lambda o f) UNIV)`
 >- (Q.UNABBREV_TAC `f` \\
     SIMP_TAC std_ss [inf_eq', IN_IMAGE, IN_UNIV] \\
     Know `!x. lambda  (right_open_interval (c - (1/2) pow x) (c + (1/2) pow x)) =
               lambda0 (right_open_interval (c - (1/2) pow x) (c + (1/2) pow x))`
     >- METIS_TAC [right_open_interval_in_intervals, lborel_def] >> Rewr' \\
     Know `!x. lambda0 (right_open_interval (c - (1/2) pow x) (c + (1/2) pow x)) =
               Normal ((c + (1/2) pow x) - (c - (1/2) pow x))`
     >- (GEN_TAC >> MATCH_MP_TAC lambda0_def \\
         REWRITE_TAC [real_sub, REAL_LE_LADD] \\
         MATCH_MP_TAC REAL_LT_IMP_LE \\
        `(0 :real) < 1 / 2` by PROVE_TAC [REAL_HALF_BETWEEN] \\
         MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC `0` \\
         ASM_SIMP_TAC std_ss [REAL_POW_LT, REAL_NEG_LT0]) >> Rewr' \\
     Know `!x. c + (1/2) pow x - (c - (1/2) pow x) = 2 * (1/2) pow x`
     >- (GEN_TAC >> Q.ABBREV_TAC `(r :real) = (1 / 2) pow x` \\
        `c + r - (c - r) = 2 * r` by REAL_ARITH_TAC >> POP_ORW \\
         Q.UNABBREV_TAC `r` >> REWRITE_TAC [pow]) >> Rewr' \\
     rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2): easy *)
       POP_ORW >> REWRITE_TAC [extreal_of_num_def, extreal_le_eq] \\
       MATCH_MP_TAC REAL_LT_IMP_LE \\
       MATCH_MP_TAC REAL_LT_MUL >> RW_TAC real_ss [REAL_POW_LT],
       (* goal 2 (of 2): hard *)
       MATCH_MP_TAC le_epsilon >> RW_TAC std_ss [add_lzero] \\
       MATCH_MP_TAC le_trans \\
      `e <> NegInf` by METIS_TAC [pos_not_neginf, lt_imp_le] \\
      `?r. e = Normal r` by METIS_TAC [extreal_cases] \\
       POP_ASSUM (fn th =>
                  FULL_SIMP_TAC std_ss [extreal_not_infty, extreal_of_num_def,
                                        extreal_lt_eq, th]) \\
      `0 < r / 2` by RW_TAC real_ss [] \\
       MP_TAC (Q.SPEC `r / 2` POW_HALF_SMALL) >> RW_TAC std_ss [] \\
       Q.EXISTS_TAC `Normal (2 * (1/2) pow n)` \\
       CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                    Q.EXISTS_TAC `n` >> art []) \\
       REWRITE_TAC [extreal_le_eq, Once REAL_MUL_COMM] \\
       MATCH_MP_TAC REAL_LT_IMP_LE \\
       ASSUME_TAC (Q.SPEC `n` POW_HALF_POS) \\
      `(0 :real) < 2` by REAL_ARITH_TAC \\
       POP_ASSUM (art o wrap o (MATCH_MP (GSYM REAL_LT_RDIV_EQ))) ]) >> Rewr'
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC (Q.ISPEC `lborel` MONOTONE_CONVERGENCE_BIGINTER2)
 >> RW_TAC std_ss [measure_space_lborel, IN_FUNSET, IN_UNIV, sets_lborel]
 >| [ (* goal 1 (of 3) *)
      rename1 `f n IN _` \\
     `f n IN subsets right_open_intervals`
        by METIS_TAC [right_open_interval_in_intervals] \\
      PROVE_TAC [SUBSET_DEF, right_open_intervals_subset_borel],
      (* goal 2 (of 3) *)
     `f n IN subsets right_open_intervals`
        by METIS_TAC [right_open_interval_in_intervals] \\
     `lambda (f n) = lambda0 (f n)` by PROVE_TAC [lborel_def] >> POP_ORW \\
      Q.UNABBREV_TAC `f` >> BETA_TAC \\
      REWRITE_TAC [lambda0_not_infty],
      (* goal 3 (of 3) *)
      Q.UNABBREV_TAC `f` >> BETA_TAC \\
      RW_TAC std_ss [in_right_open_interval, SUBSET_DEF, GSPECIFICATION] >|
      [ (* goal 3.1 (of 2) *)
        MATCH_MP_TAC REAL_LE_TRANS \\
        Q.EXISTS_TAC `c - (1 / 2) pow (SUC n)` >> art [] \\
       `n <= SUC n` by RW_TAC arith_ss [] \\
        POP_ASSUM (ASSUME_TAC o (MATCH_MP POW_HALF_MONO)) \\
        REAL_ASM_ARITH_TAC,
        (* goal 3.2 (of 2) *)
        MATCH_MP_TAC REAL_LTE_TRANS \\
        Q.EXISTS_TAC `c + (1 / 2) pow (SUC n)` >> art [] \\
       `n <= SUC n` by RW_TAC arith_ss [] \\
        POP_ASSUM (ASSUME_TAC o (MATCH_MP POW_HALF_MONO)) \\
        REAL_ASM_ARITH_TAC ] ]
QED

Theorem lambda_closed_interval :
    !a b. a <= b ==> (lambda (interval [a,b]) = Normal (b - a))
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [REAL_LE_LT, Once DISJ_SYM]))
 >- fs [GSYM extreal_of_num_def, INTERVAL_SING, lambda_sing]
 >> Know `interval [a,b] = right_open_interval a b UNION {b}`
 >- (RW_TAC std_ss [Once EXTENSION, IN_UNION, IN_SING, IN_INTERVAL,
                    in_right_open_interval] \\
     EQ_TAC >> rpt STRIP_TAC >> fs [REAL_LE_REFL]
     >- fs [REAL_LE_LT] \\ (* 2 goals left, same tactics *)
     MATCH_MP_TAC REAL_LT_IMP_LE >> art []) >> Rewr'
 >> Suff `lambda (right_open_interval a b UNION {b}) =
          lambda (right_open_interval a b) + lambda {b}`
 >- (Rewr' >> REWRITE_TAC [lambda_sing, add_rzero] \\
     MATCH_MP_TAC lambda_prop \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> MATCH_MP_TAC (Q.ISPEC `lborel` ADDITIVE)
 >> ASSUME_TAC measure_space_lborel
 >> CONJ_TAC >- (MATCH_MP_TAC MEASURE_SPACE_ADDITIVE >> art [])
 >> REWRITE_TAC [sets_lborel]
 >> STRONG_CONJ_TAC
 >- REWRITE_TAC [right_open_interval, borel_measurable_sets] >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- REWRITE_TAC [borel_measurable_sets] >> DISCH_TAC
 >> reverse CONJ_TAC
 >- (MATCH_MP_TAC ALGEBRA_UNION >> art [] \\
     REWRITE_TAC [REWRITE_RULE [sigma_algebra_def] sigma_algebra_borel])
 >> ONCE_REWRITE_TAC [DISJOINT_SYM]
 >> RW_TAC std_ss [DISJOINT_ALT, IN_SING, right_open_interval,
                   GSPECIFICATION, REAL_LT_REFL, real_lte]
QED

Theorem lambda_closed_interval_content :
    !a b. lambda (interval [a,b]) = Normal (content (interval [a,b]))
Proof
    rpt STRIP_TAC
 >> `a <= b \/ b < a` by PROVE_TAC [REAL_LTE_TOTAL]
 >- ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, lambda_closed_interval]
 >> IMP_RES_TAC REAL_LT_IMP_LE
 >> fs [GSYM CONTENT_EQ_0, GSYM extreal_of_num_def]
 >> fs [INTERVAL_EQ_EMPTY]
 >> REWRITE_TAC [lambda_empty]
QED

Theorem lambda_open_interval :
    !a b. a <= b ==> (lambda (interval (a,b)) = Normal (b - a))
Proof
    rpt STRIP_TAC
 >> POP_ASSUM (STRIP_ASSUME_TAC o (REWRITE_RULE [REAL_LE_LT, Once DISJ_SYM]))
 >- fs [GSYM extreal_of_num_def, INTERVAL_SING, lambda_empty]
 >> Know `interval (a,b) = right_open_interval a b DIFF {a}`
 >- (RW_TAC std_ss [Once EXTENSION, IN_DIFF, IN_SING, IN_INTERVAL,
                    in_right_open_interval] \\
     EQ_TAC >> rpt STRIP_TAC >> fs [REAL_LE_REFL]
     >- (MATCH_MP_TAC REAL_LT_IMP_LE >> art []) \\
     fs [REAL_LE_LT]) >> Rewr'
 >> Suff `lambda (right_open_interval a b DIFF {a}) =
          lambda (right_open_interval a b) - lambda {a}`
 >- (Rewr' >> REWRITE_TAC [lambda_sing, sub_rzero] \\
     MATCH_MP_TAC lambda_prop \\
     MATCH_MP_TAC REAL_LT_IMP_LE >> art [])
 >> MATCH_MP_TAC (Q.ISPEC `lborel` MEASURE_SPACE_FINITE_DIFF_SUBSET)
 >> REWRITE_TAC [measure_space_lborel, sets_lborel]
 >> STRONG_CONJ_TAC
 >- REWRITE_TAC [right_open_interval, borel_measurable_sets] >> DISCH_TAC
 >> STRONG_CONJ_TAC
 >- REWRITE_TAC [borel_measurable_sets] >> DISCH_TAC
 >> CONJ_TAC
 >- RW_TAC std_ss [SUBSET_DEF, IN_SING, in_right_open_interval, REAL_LE_REFL]
 >> REWRITE_TAC [lambda_not_infty]
QED

(* |- sigma_finite lborel <=>
      ?A. COUNTABLE A /\ A SUBSET measurable_sets lborel /\
          BIGUNION A = m_space lborel /\ !a. a IN A ==> lambda a <> PosInf
 *)
val sigma_finite_measure = MATCH_MP SIGMA_FINITE_ALT2 measure_space_lborel;

Theorem sigma_finite_lborel :
    sigma_finite lborel
Proof
    RW_TAC std_ss [sigma_finite_measure]
 >> Q.EXISTS_TAC `{line n | n IN UNIV}`
 >> rpt CONJ_TAC (* 4 subgoals *)
 >- (SIMP_TAC std_ss [GSYM IMAGE_DEF] \\
     MATCH_MP_TAC image_countable >> SIMP_TAC std_ss [COUNTABLE_NUM])
 >- (SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, sets_lborel, IN_UNIV] \\
     rpt STRIP_TAC >> RW_TAC std_ss [borel_line])
 >- (SIMP_TAC std_ss [EXTENSION, space_lborel, IN_UNIV] \\
     SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] \\
     GEN_TAC >> ASSUME_TAC REAL_IN_LINE \\
     POP_ASSUM (MP_TAC o Q.SPEC `x`) >> SET_TAC [])
 >> RW_TAC std_ss [GSPECIFICATION, IN_UNIV, line]
 >> `-&n <= (&n) :real` by RW_TAC real_ss []
 >> POP_ASSUM (MP_TAC o (SIMP_RULE list_ss [CLOSED_interval]) o
               (MATCH_MP lambda_closed_interval)) >> Rewr'
 >> REWRITE_TAC [extreal_not_infty]
QED

(* ------------------------------------------------------------------------- *)
(*  Lebesgue sigma-algebra with the household Lebesgue measure (lebesgue)    *)
(* ------------------------------------------------------------------------- *)

val absolutely_integrable_on_indicator = store_thm
  ("absolutely_integrable_on_indicator",
  ``!A X. indicator A absolutely_integrable_on X <=>
          indicator A integrable_on X``,
  REPEAT GEN_TAC THEN REWRITE_TAC [absolutely_integrable_on] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  KNOW_TAC ``!x. abs(indicator A x) = indicator A x`` THENL
  [ALL_TAC, DISCH_TAC THEN FULL_SIMP_TAC std_ss [] THEN METIS_TAC [ETA_AX]] THEN
  RW_TAC real_ss [indicator]);

val has_integral_indicator_UNIV = store_thm
  ("has_integral_indicator_UNIV",
 ``!s A x. (indicator (s INTER A) has_integral x) UNIV =
           (indicator s has_integral x) A``,
  KNOW_TAC ``!s A. (\x. if x IN A then indicator s x else 0) = indicator (s INTER A)`` THENL
  [SET_TAC [indicator], ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN DISCH_TAC] THEN
  RW_TAC std_ss [HAS_INTEGRAL_RESTRICT_UNIV] THEN METIS_TAC [ETA_AX]);

val integral_indicator_UNIV = store_thm ("integral_indicator_UNIV",
  ``!s A. integral UNIV (indicator (s INTER A)) =
          integral A (indicator s)``,
  REWRITE_TAC [integral] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]);

val integrable_indicator_UNIV = store_thm ("integrable_indicator_UNIV",
  ``!s A. (indicator (s INTER A)) integrable_on UNIV <=>
          (indicator s) integrable_on A``,
  RW_TAC std_ss [integrable_on] THEN AP_TERM_TAC THEN
  ABS_TAC THEN METIS_TAC [has_integral_indicator_UNIV]);

Theorem integral_one : (* was: MEASURE_HOLLIGHT_EQ_ISABELLE *)
    !A. integral A (\x. 1) = integral univ(:real) (indicator A)
Proof
    ONCE_REWRITE_TAC [METIS [SET_RULE ``A = A INTER A``]
                          ``indicator A = indicator (A INTER A)``]
 >> SIMP_TAC std_ss [integral_indicator_UNIV]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC INTEGRAL_EQ >> SIMP_TAC std_ss [indicator]
QED

val indicator_fn_pos_le = INDICATOR_FN_POS;

Theorem has_integral_interval_cube :
    !a b n. (indicator (interval [a,b]) has_integral
               content (interval [a,b] INTER (line n))) (line n)
Proof
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM has_integral_indicator_UNIV] THEN
  SIMP_TAC std_ss [indicator, HAS_INTEGRAL_RESTRICT_UNIV] THEN
  SIMP_TAC std_ss [line, GSYM interval, INTER_INTERVAL] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``content (interval [(max a (-&n),min b (&n))]) =
                        content (interval [(max a (-&n),min b (&n))]) * 1``] THEN
  METIS_TAC [HAS_INTEGRAL_CONST]
QED

(* Lebesgue sigma-algebra with the household measure (lebesgue),
   constructed by Henstock-Kurzweil (gauge) Integration.

   Named after Henri Lebesgue (1875-1941), a French mathematician [5] *)
Definition lebesgue_def :
  lebesgue = (univ(:real),
              {A | !n. (indicator A) integrable_on (line n)},
              (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV}))
End

Theorem space_lebesgue :
    m_space lebesgue = univ(:real)
Proof
    SIMP_TAC std_ss [lebesgue_def, m_space_def]
QED

Theorem in_sets_lebesgue : (* was: lebesgueI *)
    !A. (!n. indicator A integrable_on line n) ==> A IN measurable_sets lebesgue
Proof
    SIMP_TAC std_ss [lebesgue_def, measurable_sets_def] THEN SET_TAC []
QED

val lebesgueI = in_sets_lebesgue;

Theorem limseq_indicator_BIGUNION : (* was: LIMSEQ_indicator_UN *)
    !A x. ((\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}) x) -->
           (indicator (BIGUNION {A i | i IN UNIV}) x)) sequentially
Proof
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``?i. x IN (A:num->real->bool) i`` THENL
  [ALL_TAC, FULL_SIMP_TAC std_ss [indicator, IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] THEN
   KNOW_TAC ``~(?s. x IN s /\ ?i. s = (A:num->real->bool) i)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN
   KNOW_TAC ``!k. ~(?s. x IN s /\ ?i. (s = (A:num->real->bool) i) /\ i < k)`` THENL
   [METIS_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC std_ss [LIM_CONST]] THEN
  FULL_SIMP_TAC std_ss [] THEN
  KNOW_TAC ``!k. indicator (BIGUNION {(A:num->real->bool) j | j < k + SUC i}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   UNDISCH_TAC ``~?s. x IN s /\ ?j. (s = (A:num->real->bool) j) /\ j < k + SUC i`` THEN
   SIMP_TAC std_ss [] THEN EXISTS_TAC ``(A:num->real->bool) i`` THEN
   ASM_SIMP_TAC std_ss [] THEN EXISTS_TAC  ``i:num`` THEN ASM_SIMP_TAC std_ss [] THEN
   ARITH_TAC, DISCH_TAC] THEN
  KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)}) x = 1`` THENL
  [RW_TAC real_ss [indicator, GSPECIFICATION, IN_BIGUNION] THEN
   POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [IN_UNIV] THEN METIS_TAC [], DISCH_TAC] THEN
  MATCH_MP_TAC SEQ_OFFSET_REV THEN EXISTS_TAC ``SUC i`` THEN
  ASM_SIMP_TAC std_ss [LIM_CONST]
QED

val LT = prove ((* HOL Light compatibility *)
  ``(!m:num. m < 0 <=> F) /\ (!m n. m < SUC n <=> (m = n) \/ m < n)``,
    METIS_TAC [LESS_THM, NOT_LESS_0]);

val LIMSEQ_indicator_UN = limseq_indicator_BIGUNION;

Theorem sigma_algebra_lebesgue :
    sigma_algebra (UNIV, {A | !n. (indicator A) integrable_on (line n)})
Proof
    RW_TAC std_ss [sigma_algebra_alt_pow]
 >- (REWRITE_TAC [POW_DEF] >> SET_TAC [])
 >- (SIMP_TAC std_ss [GSPECIFICATION] \\
     Know `indicator {} = (\x. 0)` >- SET_TAC [indicator] \\
     Rewr' >> SIMP_TAC std_ss [INTEGRABLE_0])
 >- (FULL_SIMP_TAC std_ss [GSPECIFICATION] \\
     Know `indicator (univ(:real) DIFF s) = (\x. 1 - indicator s x)`
     >- (SIMP_TAC std_ss [indicator] >> ABS_TAC \\
         SIMP_TAC std_ss [IN_DIFF, IN_UNIV] >> COND_CASES_TAC \\
         FULL_SIMP_TAC real_ss []) >> Rewr' \\
     ONCE_REWRITE_TAC [METIS [] ``(\x. 1 - indicator s x) =
                        (\x. (\x. 1) x - (\x. indicator s x) x)``] \\
     GEN_TAC >> MATCH_MP_TAC INTEGRABLE_SUB >> CONJ_TAC >|
     [SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
      METIS_TAC [ETA_AX]])
 >> FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN
  KNOW_TAC ``!k n. indicator (BIGUNION {(A:num->real->bool) i | i < k})
              integrable_on (line n)`` THENL
  [Induct_on `k` THENL
   [SIMP_TAC std_ss [LT] THEN REWRITE_TAC [SET_RULE ``BIGUNION {A i | i | F} = {}``] THEN
    KNOW_TAC ``indicator {} = (\x. 0)``
    THENL [SET_TAC [indicator], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
    SIMP_TAC std_ss [INTEGRABLE_0], ALL_TAC] THEN
   KNOW_TAC ``BIGUNION {A i | i < SUC k} =
              BIGUNION {(A:num->real->bool) i | i < k} UNION A k`` THENL
   [SIMP_TAC std_ss [ADD1, ARITH_PROVE ``i < SUC k <=> (i < k \/ (i = k))``] THEN
    SET_TAC [], DISCH_TAC THEN ASM_REWRITE_TAC []] THEN
   KNOW_TAC ``indicator (BIGUNION {(A:num->real->bool) i | i < k} UNION A k) =
              (\x. max (indicator (BIGUNION {A i | i < k}) x) (indicator (A k) x))`` THENL
   [SIMP_TAC std_ss [FUN_EQ_THM] THEN GEN_TAC THEN
    SIMP_TAC std_ss [max_def, indicator] THEN
    REPEAT COND_CASES_TAC THEN FULL_SIMP_TAC std_ss [IN_UNION] THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN FULL_SIMP_TAC real_ss [],
    DISCH_TAC] THEN
   REWRITE_TAC [GSYM absolutely_integrable_on_indicator] THEN GEN_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX THEN
   ASM_SIMP_TAC std_ss [absolutely_integrable_on_indicator] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_IMAGE, IN_UNIV] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN METIS_TAC [], DISCH_TAC] THEN GEN_TAC THEN
  MP_TAC (ISPECL [``(\k. indicator (BIGUNION {(A:num->real->bool) i | i < k}))``,
                  ``indicator (BIGUNION {(A:num->real->bool) i | i IN univ(:num)})``,
                  ``(\x:real. 1:real)``, ``line n``] DOMINATED_CONVERGENCE) THEN
  KNOW_TAC ``(!k.
    (\k. indicator (BIGUNION {(A:num->real->bool) i | i < k})) k integrable_on line n) /\
 (\x. 1) integrable_on line n /\
 (!k x.
    x IN line n ==>
    abs ((\k. indicator (BIGUNION {A i | i < k})) k x) <= (\x. 1) x) /\
 (!x.
    x IN line n ==>
    ((\k. (\k. indicator (BIGUNION {A i | i < k})) k x) -->
     indicator (BIGUNION {A i | i IN univ(:num)}) x) sequentially)`` THENL
 [ALL_TAC, METIS_TAC []] THEN REPEAT CONJ_TAC THENL
[FULL_SIMP_TAC std_ss [],
 SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
 SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1],
 METIS_TAC [LIMSEQ_indicator_UN]]
QED

Theorem sets_lebesgue :
    measurable_sets lebesgue = {A | !n. (indicator A) integrable_on (line n)}
Proof
    SIMP_TAC std_ss [lebesgue_def, measurable_sets_def]
QED

Theorem in_sets_lebesgue_imp : (* was: lebesgueD *)
    !A n. A IN measurable_sets lebesgue ==> indicator A integrable_on line n
Proof
    SIMP_TAC std_ss [sets_lebesgue, GSPECIFICATION]
QED

val lebesgueD = in_sets_lebesgue_imp;

Theorem measure_lebesgue :
    measure lebesgue =
      (\A. sup {Normal (integral (line n) (indicator A)) | n IN UNIV})
Proof
    SIMP_TAC std_ss [measure_def, lebesgue_def]
QED

Theorem positive_lebesgue :
    positive lebesgue
Proof
  SIMP_TAC std_ss [lebesgue_def, positive_def, sets_lebesgue, measure_lebesgue] THEN
  SIMP_TAC std_ss [INDICATOR_EMPTY, IN_UNIV, INTEGRAL_0, extreal_of_num_def] THEN
   REWRITE_TAC [SET_RULE ``{Normal 0 | n | T} = {Normal 0}``, sup_sing] THEN
  RW_TAC std_ss [] THEN MATCH_MP_TAC le_sup_imp THEN
  ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [GSPECIFICATION] THEN
  EXISTS_TAC ``0:num`` THEN SIMP_TAC std_ss [extreal_11, line, GSYM interval] THEN
  SIMP_TAC std_ss [REAL_NEG_0, INTEGRAL_REFL]
QED

Theorem seq_le_imp_lim_le :
    !x y f. (!n. f n <= x) /\ (f --> y) sequentially ==> y <= x
Proof
   RW_TAC boolSimps.bool_ss [LIM_SEQUENTIALLY]
   THEN MATCH_MP_TAC REAL_LE_EPSILON
   THEN RW_TAC boolSimps.bool_ss []
   THEN Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
   THEN RW_TAC boolSimps.bool_ss []
   THEN POP_ASSUM (MP_TAC o Q.SPEC `N`)
   THEN Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
   THEN REWRITE_TAC [dist]
   THEN (RW_TAC boolSimps.bool_ss
         [GREATER_EQ, LESS_EQ_REFL, abs, REAL_LE_SUB_LADD, REAL_ADD_LID]
         THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss
              [REAL_NOT_LE, REAL_NEG_SUB, REAL_LT_SUB_RADD])
   THENL [MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `x`
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LE_TRANS])
          THEN PROVE_TAC [REAL_LE_ADDR, REAL_LT_LE],
          MATCH_MP_TAC REAL_LE_TRANS
          THEN Q.EXISTS_TAC `f N + e`
          THEN (CONJ_TAC THEN1 PROVE_TAC [REAL_LT_LE, REAL_ADD_SYM])
          THEN PROVE_TAC [REAL_LE_ADD2, REAL_LE_REFL]]
QED

(* cf. seqTheory.SEQ_MONO_LE *)
Theorem seq_mono_le :
    !f x n. (!n. f n <= f (n + 1)) /\ (f --> x) sequentially ==> f n <= x
Proof
   RW_TAC boolSimps.bool_ss [LIM_SEQUENTIALLY] THEN MATCH_MP_TAC REAL_LE_EPSILON THEN
   RW_TAC boolSimps.bool_ss [] THEN Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`) THEN
   RW_TAC boolSimps.bool_ss [GREATER_EQ] THEN MP_TAC (Q.SPECL [`N`, `n`] LESS_EQ_CASES) THEN
   STRIP_TAC THENL
   [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`) THEN ASM_REWRITE_TAC [dist] THEN
    REAL_ARITH_TAC, ALL_TAC] THEN FULL_SIMP_TAC std_ss [dist] THEN
   (SUFF_TAC ``!i : num. f (N - i) <= x + (e : real)`` THEN1 PROVE_TAC [LESS_EQUAL_DIFF]) THEN
   numLib.INDUCT_TAC
   THENL [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
          THEN RW_TAC boolSimps.bool_ss [abs, LESS_EQ_REFL, SUB_0]
          THEN simpLib.FULL_SIMP_TAC boolSimps.bool_ss
               [REAL_LT_SUB_RADD, REAL_NEG_SUB, REAL_NOT_LE, REAL_ADD_LID,
                REAL_LE_SUB_LADD]
          THEN PROVE_TAC
               [REAL_LT_LE, REAL_ADD_SYM, REAL_LE_TRANS, REAL_LE_ADDR],
          MP_TAC (numLib.ARITH_PROVE
                  ``(N - i = N - SUC i) \/ (N - i = (N - SUC i) + 1)``)
          THEN PROVE_TAC [REAL_LE_REFL, REAL_LE_TRANS]]
QED

(* cf. extrealTheory.sup_seq *)
Theorem sup_sequence :
    !f l. mono_increasing f ==> ((f --> l) sequentially =
          (sup (IMAGE (\n. Normal (f n)) UNIV) = Normal l))
Proof
  RW_TAC std_ss [] THEN EQ_TAC THENL
  [RW_TAC std_ss [sup_eq] THENL
   [POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN RW_TAC std_ss [extreal_le_def] THEN
    METIS_TAC [mono_increasing_suc,seq_mono_le,ADD1], ALL_TAC] THEN
   KNOW_TAC ``!n:num. Normal (f n) <= y`` THENL
   [RW_TAC std_ss [] THEN POP_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
    METIS_TAC [], ALL_TAC] THEN
   Cases_on `y` THENL
   [METIS_TAC [le_infty,extreal_not_infty],
    METIS_TAC [le_infty],
    METIS_TAC [seq_le_imp_lim_le,extreal_le_def]], ALL_TAC] THEN
  RW_TAC std_ss [extreal_sup_def] THEN
  KNOW_TAC ``(\r. IMAGE (\n. Normal ((f:num->real) n)) UNIV (Normal r)) =
                  IMAGE f UNIV`` THENL
  [RW_TAC std_ss [EXTENSION,IN_ABS,IN_IMAGE,IN_UNIV] THEN EQ_TAC THENL
   [RW_TAC std_ss [] THEN POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM SPECIFICATION]) THEN
    RW_TAC std_ss [IN_IMAGE,IN_UNIV], ALL_TAC] THEN
   RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN
   RW_TAC std_ss [IN_UNIV,IN_IMAGE] THEN METIS_TAC [], ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [] THEN KNOW_TAC ``!n:num. Normal (f n) <= x`` THENL
  [RW_TAC std_ss [] THEN Q.PAT_X_ASSUM `!y. P` MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN RW_TAC std_ss [IN_UNIV,IN_IMAGE] THEN
   METIS_TAC [], ALL_TAC] THEN
  `x <> NegInf` by METIS_TAC [lt_infty,extreal_not_infty,lte_trans] THEN
  `?z. x = Normal z` by METIS_TAC [extreal_cases] THEN
  KNOW_TAC ``!n:num. f n <= z:real`` THENL
  [RW_TAC std_ss [GSYM extreal_le_def] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM SPECIFICATION] THEN SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
   METIS_TAC [], ALL_TAC] THEN
  RW_TAC std_ss [LIM_SEQUENTIALLY, dist] THEN
  (MP_TAC o Q.ISPECL [`IMAGE (f:num->real) UNIV`,`e:real/2`]) SUP_EPSILON THEN
  SIMP_TAC std_ss [REAL_LT_HALF1] THEN
  KNOW_TAC ``!y x z. IMAGE f UNIV x <=> x IN IMAGE (f:num->real) UNIV`` THENL
  [RW_TAC std_ss [SPECIFICATION], DISCH_TAC] THEN
  STRIP_TAC THEN KNOW_TAC ``(?z. !x. x IN IMAGE (f:num->real) UNIV ==> x <= z)`` THENL
  [Q.EXISTS_TAC `z:real` THEN RW_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
   METIS_TAC [], DISCH_TAC] THEN
  KNOW_TAC ``?x. x IN IMAGE (f:num->real) UNIV`` THENL
  [RW_TAC std_ss [IN_UNIV,IN_IMAGE], ALL_TAC] THEN
  RW_TAC std_ss [] THEN KNOW_TAC ``?x. x IN IMAGE (f:num->real) UNIV /\
                                   real$sup (IMAGE f UNIV) <= x + e / 2`` THENL
  [METIS_TAC [], DISCH_TAC] THEN
  RW_TAC std_ss [GSYM ABS_BETWEEN, GREATER_EQ] THEN
  FULL_SIMP_TAC std_ss [IN_IMAGE,IN_UNIV] THEN
  Q.EXISTS_TAC `x''''` THEN RW_TAC std_ss [REAL_LT_SUB_RADD] THENL
  [MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `f x'''' + e / 2` THEN
   RW_TAC std_ss [] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   Q.EXISTS_TAC `(f:num->real) n + e / 2` THEN reverse CONJ_TAC THENL
   [METIS_TAC [REAL_LET_ADD2,REAL_LT_HALF2,REAL_LE_REFL], ALL_TAC] THEN
   RW_TAC std_ss [REAL_LE_RADD] THEN
   METIS_TAC [mono_increasing_def], ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN Q.EXISTS_TAC `real$sup (IMAGE f UNIV)` THEN
  RW_TAC std_ss [REAL_LT_ADDR] THEN
  Q_TAC SUFF_TAC `!y. (\y. y IN IMAGE f UNIV) y ==> y <= real$sup (IMAGE f UNIV)` THENL
  [METIS_TAC [IN_IMAGE, IN_UNIV], ALL_TAC] THEN
  SIMP_TAC std_ss [IN_DEF] THEN
  MATCH_MP_TAC REAL_SUP_UBOUND_LE THEN
  KNOW_TAC ``!y x z. IMAGE (f:num->bool) UNIV x <=> x IN IMAGE f UNIV`` THENL
  [RW_TAC std_ss [IN_DEF], DISCH_TAC] THEN
  RW_TAC std_ss [IN_IMAGE, IN_UNIV] THEN
  Q.EXISTS_TAC `z'` THEN RW_TAC std_ss []
QED

Theorem countably_additive_lebesgue :
    countably_additive lebesgue
Proof
    RW_TAC std_ss [countably_additive_def]
 >> Know `!A. IMAGE A univ(:num) SUBSET measurable_sets lebesgue ==>
              !i n. indicator (A i) integrable_on line n`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC lebesgueD \\
     FULL_SIMP_TAC std_ss [SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> METIS_TAC [IN_IMAGE, IN_UNIV])
 >> DISCH_TAC
 >> Know `!i n. 0 <= integral (line n) (indicator ((f:num->real->bool) i))`
 >- (rpt STRIP_TAC >> MATCH_MP_TAC INTEGRAL_COMPONENT_POS \\
     SIMP_TAC std_ss [DROP_INDICATOR_POS_LE] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     FULL_SIMP_TAC std_ss [IN_FUNSET, SUBSET_DEF, IN_IMAGE] \\
     METIS_TAC []) >> DISCH_TAC
 >> Know `BIGUNION {f i | i IN UNIV} IN measurable_sets lebesgue ==>
          !i n. (indicator ((f:num->real->bool) i)) integrable_on line n`
 >- (RW_TAC std_ss [] \\
     MATCH_MP_TAC lebesgueD \\
     FULL_SIMP_TAC std_ss [IN_FUNSET, IN_UNIV])
 >> FULL_SIMP_TAC std_ss [GSYM IMAGE_DEF] >> DISCH_TAC
 >> SIMP_TAC std_ss [o_DEF, measure_lebesgue]
 >> Know `suminf (\i. sup {(\n i. Normal (integral (line n) (indicator (f i)))) n i | n IN UNIV}) =
          sup {suminf (\i. (\n i. Normal (integral (line n) (indicator (f i)))) n i) | n IN UNIV}`
 >- (MATCH_MP_TAC ext_suminf_sup_eq \\
     SIMP_TAC std_ss [extreal_of_num_def] \\
     CONJ_TAC
     >- (SIMP_TAC std_ss [extreal_le_def] >> rpt STRIP_TAC \\
         MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE \\
         FULL_SIMP_TAC std_ss [LINE_MONO, DROP_INDICATOR_POS_LE]) \\
     SIMP_TAC std_ss [extreal_le_def] \\
     rpt GEN_TAC >> MATCH_MP_TAC INTEGRAL_COMPONENT_POS \\
     FULL_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE])
 >> RW_TAC std_ss [] >> POP_ASSUM K_TAC
 >> Suff `!n. Normal (integral (line n) (indicator (BIGUNION (IMAGE f univ(:num))))) =
              suminf (\x. Normal (integral (line n) (indicator ((f:num->real->bool) x))))`
 >- (DISCH_TAC >> ASM_SIMP_TAC std_ss [])
 >> GEN_TAC
 >> Know `suminf (\x. Normal (integral (line n) (indicator (f x)))) =
          sup (IMAGE (\n'. EXTREAL_SUM_IMAGE (\x. Normal (integral (line n) (indicator (f x))))
                                             (count n')) UNIV)`
 >- (MATCH_MP_TAC ext_suminf_def \\
     rw [extreal_of_num_def, extreal_le_eq]) >> Rewr'
 >> SIMP_TAC std_ss [FINITE_COUNT, EXTREAL_SUM_IMAGE_NORMAL]
 >> Know `mono_increasing
          (\n'. SIGMA (\x. integral (line n) (indicator ((f:num->real->bool) x))) (count n'))`
 >- (SIMP_TAC std_ss [mono_increasing_def] THEN
     REPEAT STRIP_TAC THEN SIMP_TAC std_ss [GSYM extreal_le_def] THEN
     SIMP_TAC std_ss [FINITE_COUNT, GSYM EXTREAL_SUM_IMAGE_NORMAL] THEN
     MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET THEN
     ASM_SIMP_TAC real_ss [count_def, GSPECIFICATION, FINITE_COUNT, SUBSET_DEF] THEN
     REPEAT STRIP_TAC THEN REWRITE_TAC [extreal_of_num_def, extreal_le_def] THEN
     MATCH_MP_TAC INTEGRAL_COMPONENT_POS THEN
     ASM_SIMP_TAC std_ss [DROP_INDICATOR_POS_LE]) >> DISCH_TAC
 >> ASM_SIMP_TAC std_ss [GSYM sup_sequence, REAL_SUM_IMAGE_COUNT]
 >> Know `!n m. sum (0,m) (\x. integral (line n) (indicator ((f:num->real->bool) x))) =
                integral (line n) (indicator (BIGUNION {f i | i < m}))`
 THENL (* the rest works fine *)
[GEN_TAC THEN Induct_on `m` THENL
  [REWRITE_TAC [realTheory.sum, LT] THEN
  REWRITE_TAC [SET_RULE ``{f i | i | F} = {}``, BIGUNION_EMPTY] THEN
  SIMP_TAC real_ss [INDICATOR_EMPTY, INTEGRAL_0], ALL_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
 [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
  ASSUME_TAC sigma_algebra_lebesgue THEN
  FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
  [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN METIS_TAC [],
  DISCH_TAC] THEN
 KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} INTER f m = {}`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [INTER_DEF, IN_BIGUNION, GSPECIFICATION] THEN
  SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY] THEN
  GEN_TAC THEN ASM_CASES_TAC ``x NOTIN (f:num->real->bool) m'`` THEN
  ASM_REWRITE_TAC [] THEN GEN_TAC THEN
  ASM_CASES_TAC ``x IN (s:real->bool)`` THEN FULL_SIMP_TAC std_ss [] THEN
  GEN_TAC THEN ASM_CASES_TAC ``~(i < m':num)`` THEN FULL_SIMP_TAC std_ss [] THEN
  EXISTS_TAC ``x:real`` THEN FULL_SIMP_TAC std_ss [DISJOINT_DEF] THEN
  POP_ASSUM MP_TAC THEN DISCH_THEN (ASSUME_TAC o MATCH_MP LESS_NOT_EQ) THEN
  ASM_SET_TAC [], DISCH_TAC] THEN
 KNOW_TAC ``!x. indicator (BIGUNION {(f:num->real->bool) i | i < SUC m}) x =
                indicator (BIGUNION {f i | i < m}) x +
                indicator (f m) x`` THENL
 [GEN_TAC THEN SIMP_TAC std_ss [indicator] THEN
  ASM_CASES_TAC ``x IN ((f:num->real->bool) m)`` THEN ASM_SIMP_TAC std_ss [] THENL
  [KNOW_TAC ``x NOTIN BIGUNION {(f:num->real->bool) i | i < m}`` THENL
   [ASM_SET_TAC [], DISCH_TAC] THEN ASM_SIMP_TAC real_ss [IN_BIGUNION] THEN
   SIMP_TAC std_ss [GSPECIFICATION] THEN
   KNOW_TAC ``?s. x IN s /\ ?i. (s = (f:num->real->bool) i) /\ i < SUC m`` THENL
   [ALL_TAC, METIS_TAC []] THEN EXISTS_TAC ``(f:num->real->bool) m`` THEN
   ASM_REWRITE_TAC [] THEN EXISTS_TAC ``m:num`` THEN SIMP_TAC arith_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC real_ss [IN_BIGUNION, GSPECIFICATION] THEN COND_CASES_TAC THENL
   [ALL_TAC, COND_CASES_TAC THENL [ALL_TAC, SIMP_TAC real_ss []] THEN
    FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``s:real->bool``) THEN
    ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
    ASM_SIMP_TAC arith_ss []] THEN FULL_SIMP_TAC std_ss [] THEN
   COND_CASES_TAC THENL [SIMP_TAC std_ss [], ALL_TAC] THEN
   FULL_SIMP_TAC std_ss [] THEN FIRST_X_ASSUM (MP_TAC o SPEC ``(f:num->real->bool) i``) THEN
   ASM_SIMP_TAC std_ss [] THEN DISCH_THEN (MP_TAC o SPEC ``i:num``) THEN
   RW_TAC std_ss [] THEN KNOW_TAC ``i = m:num`` THENL
   [ASM_SIMP_TAC arith_ss [], DISCH_TAC] THEN FULL_SIMP_TAC std_ss [],
   DISCH_TAC] THEN
  ONCE_REWRITE_TAC [realTheory.sum] THEN ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN REWRITE_TAC [ADD] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV) [METIS [] ``!f. indicator f = (\x. indicator f x)``] THEN
  SIMP_TAC std_ss [] THEN
  KNOW_TAC ``integral (line n') (indicator (BIGUNION {f i | i < SUC m})) =
             integral (line n') ((\x. (\x. indicator (BIGUNION {f i | i < m}) x) x +
                                 (\x. indicator ((f:num->real->bool) m) x) x))`` THENL
  [FIRST_X_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
   ASM_SIMP_TAC std_ss [] THEN METIS_TAC [], DISC_RW_KILL] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN METIS_TAC [lebesgueD], DISCH_TAC] THEN
  ASM_SIMP_TAC std_ss [] THEN
  MATCH_MP_TAC (METIS [] ``!P. (P /\ Q) ==> Q``) THEN
  ONCE_REWRITE_TAC [METIS []
        ``(indicator (BIGUNION {(f:num->real->bool) i | i < n'})) =
     (\n'. indicator (BIGUNION {f i | i < n'})) n'``] THEN
  EXISTS_TAC ``(indicator (BIGUNION (IMAGE (f:num->real->bool) univ(:num))))
                integrable_on (line n)`` THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE THEN EXISTS_TAC ``\x:real. 1:real`` THEN
  REPEAT CONJ_TAC THENL
  [KNOW_TAC ``!m. BIGUNION {(f:num->real->bool) i | i < m} IN
                measurable_sets lebesgue`` THENL
  [GEN_TAC THEN MATCH_MP_TAC lebesgueI THEN GEN_TAC THEN
   ASSUME_TAC sigma_algebra_lebesgue THEN
   FULL_SIMP_TAC std_ss [SIGMA_ALGEBRA, GSPECIFICATION, subsets_def, space_def] THEN
   POP_ASSUM MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_UNIV] THEN CONJ_TAC THENL
   [REWRITE_TAC [pred_setTheory.COUNTABLE_ALT] THEN SET_TAC [], ALL_TAC] THEN METIS_TAC [],
    DISCH_TAC] THEN METIS_TAC [lebesgueD],
   SIMP_TAC std_ss [line, GSYM interval, INTEGRABLE_CONST],
   FULL_SIMP_TAC std_ss [DROP_INDICATOR_ABS_LE_1], ALL_TAC] THEN
  METIS_TAC [LIMSEQ_indicator_UN, IMAGE_DEF]
QED

val measure_space_lebesgue = store_thm ("measure_space_lebesgue",
  ``measure_space lebesgue``,
  SIMP_TAC std_ss [measure_space_def, positive_lebesgue] THEN
  SIMP_TAC std_ss [sets_lebesgue, space_lebesgue, sigma_algebra_lebesgue] THEN
  SIMP_TAC std_ss [countably_additive_lebesgue]);

Theorem borel_imp_lebesgue_sets : (* was: lebesgueI_borel *)
    !s. s IN subsets borel ==> s IN measurable_sets lebesgue
Proof
  RW_TAC std_ss [] THEN
  KNOW_TAC ``s IN subsets (sigma (m_space lebesgue)
                                 (IMAGE (\(a,b). {x:real | a <= x /\ x <= b}) UNIV))``
  >- (ASM_SIMP_TAC std_ss [space_lebesgue, GSYM borel_eq_ge_le])
  THEN
  ONCE_REWRITE_TAC [METIS [space_def] ``m_space lebesgue =
                                 space (m_space lebesgue, measurable_sets lebesgue)``] THEN
  GEN_REWR_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [METIS [subsets_def] ``measurable_sets lebesgue =
                          subsets (m_space lebesgue, measurable_sets lebesgue)``] THEN
  Q.SPEC_TAC (`s`,`s`) THEN SIMP_TAC std_ss [GSYM SUBSET_DEF] THEN
  MATCH_MP_TAC SIGMA_SUBSET THEN
  SIMP_TAC std_ss [space_lebesgue, sets_lebesgue, sigma_algebra_lebesgue] THEN
  SIMP_TAC std_ss [subsets_def] THEN RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV] THEN
  MP_TAC (ISPEC ``x':real#real`` ABS_PAIR_THM) THEN RW_TAC std_ss [] THEN
  SIMP_TAC std_ss [GSYM sets_lebesgue] THEN MATCH_MP_TAC lebesgueI THEN
  REWRITE_TAC [integrable_on, GSYM interval] THEN
  METIS_TAC [has_integral_interval_cube]
QED

val lebesgueI_borel = borel_imp_lebesgue_sets;

(* TODO: prove this theorem with PSUBSET, i.e. the existence of non-Borel
   Lebesgue-measurable sets. Currently it's useless. *)
Theorem lborel_subset_lebesgue :
    (measurable_sets lborel) SUBSET (measurable_sets lebesgue)
Proof
    RW_TAC std_ss [SUBSET_DEF, sets_lborel]
 >> MATCH_MP_TAC lebesgueI_borel >> art []
QED

Theorem borel_imp_lebesgue_measurable : (* was: borel_measurable_lebesgueI *)
    !f. f IN borel_measurable (space borel, subsets borel) ==>
        f IN borel_measurable (m_space lebesgue, measurable_sets lebesgue)
Proof
  RW_TAC std_ss [measurable_def, GSPECIFICATION] THENL
  [SIMP_TAC std_ss [sigma_algebra_lebesgue, sets_lebesgue, space_lebesgue],
   FULL_SIMP_TAC std_ss [space_lebesgue, space_borel, space_def],
   FULL_SIMP_TAC std_ss [space_def, subsets_def]] THEN
  FULL_SIMP_TAC std_ss [space_borel, space_lebesgue, INTER_UNIV] THEN
  MATCH_MP_TAC lebesgueI_borel THEN ASM_SET_TAC []
QED

val borel_measurable_lebesgueI = borel_imp_lebesgue_measurable;

Theorem negligible_in_sets_lebesgue : (* was: lebesgueI_negligible *)
    !s. negligible s ==> s IN measurable_sets lebesgue
Proof
    RW_TAC std_ss [negligible]
 >> MATCH_MP_TAC lebesgueI
 >> METIS_TAC [integrable_on, line, GSYM interval]
QED

val lebesgueI_negligible = negligible_in_sets_lebesgue;

Theorem lebesgue_negligible : (* was: lmeasure_eq_0 *)
    !s. negligible s ==> (measure lebesgue s = 0)
Proof
    RW_TAC std_ss [measure_lebesgue]
 >> Know `!n. integral (line n) (indicator s) = 0`
 >- (FULL_SIMP_TAC std_ss [integral, negligible, line, GSYM interval] \\
     GEN_TAC >> MATCH_MP_TAC SELECT_UNIQUE \\
     GEN_TAC \\
     reverse EQ_TAC >- METIS_TAC [] \\
     METIS_TAC [HAS_INTEGRAL_UNIQUE]) >> Rewr
 >> SIMP_TAC std_ss [GSYM extreal_of_num_def]
 >> REWRITE_TAC [SET_RULE ``{0 | n IN UNIV} = {0}``]
 >> SIMP_TAC std_ss [sup_sing]
QED

val lmeasure_eq_0 = lebesgue_negligible;

Theorem lebesgue_measure_iff_LIMSEQ : (* was: lmeasure_iff_LIMSEQ *)
    !A m. A IN measurable_sets lebesgue /\ 0 <= m ==>
         ((measure lebesgue A = Normal m) <=>
          ((\n. integral (line n) (indicator A)) --> m) sequentially)
Proof
  RW_TAC std_ss [] THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  `!n. Normal (integral (line n) (indicator A)) =
  Normal ((\n. integral (line n) (indicator A)) n)` by METIS_TAC [] THEN
  SIMP_TAC std_ss [measure_lebesgue, GSYM IMAGE_DEF] THEN
  ONCE_ASM_REWRITE_TAC [] THEN MATCH_MP_TAC sup_sequence THEN
  RW_TAC std_ss [mono_increasing_def] THEN MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE THEN
  ASM_SIMP_TAC std_ss [LINE_MONO, lebesgueD, DROP_INDICATOR_POS_LE]
QED

val lmeasure_iff_LIMSEQ = lebesgue_measure_iff_LIMSEQ;

(* It's hard to calculate `measure lebesgue` on intervals by "lebesgue_def",
   but once the following lemma is proven, by UNIQUENESS_OF_MEASURE we
   will have `lebesgue` and `lborel` coincide on `subsets borel`, and thus
  `measure lebesgue` of other intervals can be derived from lambda lemmas.

   Most steps are from "lborel_eqI" (HVG's lebesgue_measure_hvgScript.sml).
 *)
Theorem lebesgue_closed_interval :
    !a b. a <= b ==> (measure lebesgue (interval [a,b]) = Normal (b - a))
Proof
    RW_TAC std_ss [lebesgue_def, measure_def, GSYM CONTENT_CLOSED_INTERVAL]
 >> SIMP_TAC std_ss [sup_eq']
 >> CONJ_TAC >> GEN_TAC
 >- ( SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV] \\
      STRIP_TAC >> POP_ORW \\
      ASM_SIMP_TAC std_ss [extreal_le_def] \\
      ONCE_REWRITE_TAC [GSYM integral_indicator_UNIV] \\
      ONCE_REWRITE_TAC [INTER_COMM] \\
      REWRITE_TAC [integral_indicator_UNIV] \\
      GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID] \\
      MATCH_MP_TAC INTEGRAL_COMPONENT_UBOUND \\
      SIMP_TAC std_ss [DROP_INDICATOR_LE_1] \\
      ONCE_REWRITE_TAC [GSYM integrable_indicator_UNIV] \\
      SIMP_TAC std_ss [INTER_INTERVAL, line, GSYM interval, indicator] \\
      ONCE_REWRITE_TAC [METIS [] ``1 = (\x:real. 1:real) x``] \\
      REWRITE_TAC [INTEGRABLE_RESTRICT_UNIV, INTEGRABLE_CONST] )
 >> DISCH_THEN MATCH_MP_TAC
 >> SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV, extreal_11]
 >> MP_TAC (Q.SPECL [`abs a`, `abs b`] REAL_LE_TOTAL)
 >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
     `?n. abs b <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] \\
      Q.EXISTS_TAC `n` >> MATCH_MP_TAC INTEGRAL_UNIQUE \\
      Suff `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n`
      >- METIS_TAC [has_integral_interval_cube, GSYM interval] \\
      SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] \\
      GEN_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> REAL_ARITH_TAC,
      (* goal 2 (of 2) *)
     `?n. abs a <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] \\
      Q.EXISTS_TAC `n` THEN MATCH_MP_TAC INTEGRAL_UNIQUE \\
      Suff `{x | a <= x /\ x <= b} = {x | a <= x /\ x <= b} INTER line n`
      >- METIS_TAC [has_integral_interval_cube, GSYM interval] \\
      SIMP_TAC std_ss [EXTENSION, IN_INTER, GSPECIFICATION, line] \\
      GEN_TAC >> POP_ASSUM MP_TAC >> POP_ASSUM MP_TAC >> REAL_ARITH_TAC ]
QED

(* |- !c. measure lebesgue {c} = 0 *)
Theorem lebesgue_sing =
   ((Q.GEN `c`) o
    (SIMP_RULE real_ss [REAL_LE_REFL, GSYM extreal_of_num_def, INTERVAL_SING]) o
    (Q.SPECL [`c`,`c`])) lebesgue_closed_interval;

Theorem lebesgue_empty :
    measure lebesgue {} = 0
Proof
    MATCH_MP_TAC lebesgue_negligible
 >> REWRITE_TAC [NEGLIGIBLE_EMPTY]
QED

Theorem lebesgue_closed_interval_content :
    !a b. measure lebesgue (interval [a,b]) = Normal (content (interval [a,b]))
Proof
    rpt STRIP_TAC
 >> `a <= b \/ b < a` by PROVE_TAC [REAL_LTE_TOTAL]
 >- ASM_SIMP_TAC std_ss [CONTENT_CLOSED_INTERVAL, lebesgue_closed_interval]
 >> IMP_RES_TAC REAL_LT_IMP_LE
 >> fs [GSYM CONTENT_EQ_0, GSYM extreal_of_num_def]
 >> fs [INTERVAL_EQ_EMPTY, lebesgue_empty]
QED

(* from HVG but reworked using UNIQUENESS_OF_MEASURE --Chun *)
Theorem lambda_eq : (* was: lborel_eqI *)
    !m. (!a b. measure m (interval [a,b]) =
         Normal (content (interval [a,b]))) /\ measure_space m /\
        (m_space m = space borel) /\ (measurable_sets m = subsets borel) ==>
        !s. s IN subsets borel ==> (lambda s = measure m s)
Proof
    rpt STRIP_TAC >> irule UNIQUENESS_OF_MEASURE
 >> qexistsl_tac [`univ(:real)`, `{interval [a,b] | T}`]
 >> CONJ_TAC (* INTER_STABLE *)
 >- (POP_ASSUM K_TAC >> RW_TAC std_ss [GSPECIFICATION] \\
     Cases_on `x` >> Cases_on `x'` >> fs [] \\
     rename1 `t = interval [c,d]` \\
     rename1 `s = interval [a,b]` \\
     REWRITE_TAC [INTER_INTERVAL] \\
     Q.EXISTS_TAC `(max a c, min b d)` >> rw [])
 >> CONJ_TAC (* lambda = measure m *)
 >- (POP_ASSUM K_TAC >> RW_TAC std_ss [GSPECIFICATION] \\
     Cases_on `x` >> fs [lambda_closed_interval_content])
 >> Know `{interval [a,b] | T} = IMAGE (\(a,b). {x | a <= x /\ x <= b}) UNIV`
 >- (RW_TAC list_ss [Once EXTENSION, GSPECIFICATION, IN_IMAGE, IN_UNIV,
                     CLOSED_interval] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Cases_on `x'` >> fs [] \\
       Q.EXISTS_TAC `(q,r)` >> rw [],
       (* goal 2 (of 2) *)
       Cases_on `x'` >> fs [] \\
       Q.EXISTS_TAC `(q,r)` >> rw [] ]) >> Rewr'
 >> ASM_REWRITE_TAC [SYM borel_eq_ge_le]
 >> CONJ_TAC (* measure_space lborel *)
 >- (KILL_TAC \\
     REWRITE_TAC [GSYM space_lborel, GSYM sets_lborel, MEASURE_SPACE_REDUCE,
                  measure_space_lborel])
 >> CONJ_TAC (* measure_space m *)
 >- (REWRITE_TAC [SYM space_borel] \\
     Q.PAT_X_ASSUM `_ = space borel` (ONCE_REWRITE_TAC o wrap o SYM) \\
     Q.PAT_X_ASSUM `_ = subsets borel` (ONCE_REWRITE_TAC o wrap o SYM) \\
     ASM_REWRITE_TAC [MEASURE_SPACE_REDUCE])
 >> rw [sigma_finite_def, subset_class_def, IN_UNIV, IN_FUNSET,
        m_space_def, measurable_sets_def, measure_def] (* subset_class *)
 >> Q.EXISTS_TAC `\n. {x | -&n <= x /\ x <= &n}`
 >> CONJ_TAC (* in closed intervals *)
 >- (Q.X_GEN_TAC `n` >> BETA_TAC \\
     Q.EXISTS_TAC `(-&n,&n)` >> SIMP_TAC std_ss [])
 >> CONJ_TAC (* monotonic *)
 >- (RW_TAC std_ss [SUBSET_DEF, GSPECIFICATION] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       MATCH_MP_TAC REAL_LT_IMP_LE \\
       MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC `-&n` >> art [] \\
       RW_TAC real_ss [],
       (* goal 2 (of 2) *)
       MATCH_MP_TAC REAL_LT_IMP_LE \\
       MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC `&n` >> art [] \\
       RW_TAC real_ss [] ])
 >> CONJ_TAC (* BIGUNION = UNIV *)
 >- (RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV] \\
    `?n. abs x <= &n` by SIMP_TAC std_ss [SIMP_REAL_ARCH] \\
     Q.EXISTS_TAC `n` >> SIMP_TAC real_ss [GSPECIFICATION] \\
     fs [ABS_BOUNDS])
 >> RW_TAC std_ss [GSYM lt_infty, GSYM interval]
 >> `-&n <= (&n :real)` by PROVE_TAC [le_int]
 >> ASM_SIMP_TAC std_ss [lambda_closed_interval, extreal_not_infty]
QED

(* A direct application of the above theorem:
   |- measure_space (space borel,subsets borel,measure lebesgue) ==>
      !s. s IN subsets borel ==> lambda s = measure lebesgue s
 *)
val lemma =
    REWRITE_RULE [m_space_def, measurable_sets_def, measure_def,
                  lebesgue_closed_interval_content]
      (Q.SPEC `(space borel, subsets borel, measure lebesgue)` lambda_eq);

(* final theorem (in this section): lborel and lebesgue coincide on borel *)
Theorem lambda_eq_lebesgue :
    !s. s IN subsets borel ==> lambda s = measure lebesgue s
Proof
    MATCH_MP_TAC lemma
 >> ASSUME_TAC borel_imp_lebesgue_sets
 >> RW_TAC std_ss [measure_space_def, m_space_def, measurable_sets_def,
                   SPACE, sigma_algebra_borel] (* 2 subgoals *)
 >| [ (* goal 1 (of 2): positive *)
      MP_TAC positive_lebesgue \\
      RW_TAC std_ss [positive_def, measure_def, measurable_sets_def],
      (* goal 2 (of 2): countably_additive *)
      MP_TAC countably_additive_lebesgue \\
      RW_TAC std_ss [countably_additive_def, measure_def, measurable_sets_def,
                     IN_FUNSET, IN_UNIV] ]
QED

(* |- !s. s IN subsets borel ==> measure lebesgue s = lambda s *)
Theorem lebesgue_eq_lambda = GSYM lambda_eq_lebesgue;

(* a sample application of "lebesgue_eq_lambda" *)
Theorem lebesgue_open_interval :
    !a b. a <= b ==> (measure lebesgue (interval (a,b)) = Normal (b - a))
Proof
    rpt STRIP_TAC
 >> `interval (a,b) IN subsets borel`
       by METIS_TAC [borel_measurable_sets, interval]
 >> ASM_SIMP_TAC std_ss [lebesgue_eq_lambda, lambda_open_interval]
QED

(* ------------------------------------------------------------------------- *)
(*  Almost everywhere (a.e.) - basic binder definitions                      *)
(* ------------------------------------------------------------------------- *)

val almost_everywhere_def = Define
   `almost_everywhere m P = ?N. null_set m N /\ !x. x IN (m_space m DIFF N) ==> P x`;

(* This binder syntax is learnt from Thomas Tuerk. `lebesgue` is a required
   household measure space for `AE x. P x` without `::m`, but it's never used.
 *)
val AE_def = Define `$AE = \P. almost_everywhere lebesgue P`;

val _ = set_fixity "AE" Binder;
val _ = associate_restriction ("AE", "almost_everywhere");

(* LATIN CAPITAL LETTER AE (doesn't look good)
val _ = Unicode.unicode_version {u = UTF8.chr 0x00C6, tmnm = "AE"};
 *)

val AE_THM = store_thm
  ("AE_THM", ``!m P. (AE x::m. P x) <=> almost_everywhere m P``,
    SIMP_TAC std_ss [almost_everywhere_def]);

(* `lebesgue` is the default measure used in `AE x. ...` (without restriction) *)
val AE_default = store_thm
  ("AE_default", ``!P. (AE x. P x) <=> (AE x::lebesgue. P x)``,
    RW_TAC std_ss [AE_def]);

(* see [1, p.89] *)
Theorem AE_ALT :
    !m P. (AE x::m. P x) <=>
          ?N. null_set m N /\ {x | x IN m_space m /\ ~P x} SUBSET N
Proof
    RW_TAC std_ss [AE_THM, almost_everywhere_def, SUBSET_DEF, GSPECIFICATION, IN_DIFF]
 >> METIS_TAC []
QED

Theorem AE_filter : (* was: AE + ae_filter *)
    !m P. (AE x::m. P x) <=>
          ?N. N IN null_set m /\ {x | x IN m_space m /\ x NOTIN P} SUBSET N
Proof
    RW_TAC std_ss [AE_ALT]
 >> EQ_TAC >> rpt STRIP_TAC >> Q.EXISTS_TAC `N` (* 2 subgoals, same tactics *)
 >> fs [IN_APP]
QED

val FORALL_IMP_AE = store_thm
  ("FORALL_IMP_AE",
  ``!m P. measure_space m /\ (!x. x IN m_space m ==> P x) ==> AE x::m. P x``,
    RW_TAC std_ss [AE_THM, almost_everywhere_def]
 >> Q.EXISTS_TAC `{}`
 >> RW_TAC std_ss [NULL_SET_EMPTY, IN_DIFF, NOT_IN_EMPTY]);

(* ------------------------------------------------------------------------- *)
(* Some Useful Theorems about Almost everywhere (ported by Waqar Ahmed)      *)
(* ------------------------------------------------------------------------- *)

Theorem AE_I :
    !N M P. null_set M N ==> {x | x IN m_space M /\ ~P x} SUBSET N ==>
            AE x::M. P x
Proof
  RW_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [AE_ALT, almost_everywhere_def, null_set_def] THEN
  FULL_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN METIS_TAC []
QED

Theorem AE_iff_null :
    !M P. measure_space M /\
          {x | x IN m_space M /\ ~P x} IN measurable_sets M ==>
          ((AE x::M. P x) = (null_set M {x | x IN m_space M /\ ~P x}))
Proof
  RW_TAC std_ss [AE_ALT, null_set_def, GSPECIFICATION] THEN EQ_TAC THEN
  RW_TAC std_ss [] THENL [ALL_TAC, METIS_TAC [SUBSET_REFL]] THEN
  Q_TAC SUFF_TAC `measure M {x | x IN m_space M /\ ~P x} <=
                  measure M N` THENL
  [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
   METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
  MATCH_MP_TAC INCREASING THEN METIS_TAC [MEASURE_SPACE_INCREASING]
QED

Theorem AE_iff_null_sets :
    !N M. measure_space M /\ N IN measurable_sets M ==>
          ((null_set M N) = (AE x::M. {x | ~N x} x))
Proof
  REPEAT STRIP_TAC THEN EQ_TAC THEN RW_TAC std_ss [] THEN
  FULL_SIMP_TAC std_ss [AE_ALT, null_set_def] THENL
  [FULL_SIMP_TAC std_ss [GSPECIFICATION] THEN rw[EXTENSION] THEN ASM_SET_TAC [], ALL_TAC] THEN
  fs[EXTENSION] THEN
  Q_TAC SUFF_TAC `measure M N <= measure M N'` THENL
  [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
   METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
  MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING] THEN
  `N SUBSET m_space M` by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE] THEN
  ASM_SET_TAC []
QED

Theorem AE_NOT_IN :
    !N M. null_set M N ==> AE x::M. x NOTIN N
Proof
    rw [AE_ALT, EXTENSION] >> Q.EXISTS_TAC `N`
 >> ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] >> rw [IN_DEF]
QED

Theorem AE_not_in :
    !N M. null_set M N ==> AE x::M. {x | ~N x} x
Proof
  rw [AE_ALT, EXTENSION] THEN Q.EXISTS_TAC `N` THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN rw [IN_DEF]
QED

Theorem AE_iff_measurable :
    !N M P. measure_space M /\ N IN measurable_sets M ==>
            ({x | x IN m_space M /\ ~P x} = N) ==>
            ((AE x::M. P x) = (measure M N = 0))
Proof
  RW_TAC std_ss [AE_ALT, GSPECIFICATION] THEN
  EQ_TAC THEN RW_TAC std_ss [] THENL
  [FULL_SIMP_TAC std_ss [null_set_def, GSPECIFICATION] THEN
   Q_TAC SUFF_TAC `measure M {x | x IN m_space M /\ ~P x} <= measure M N'` THENL
   [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
    METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
   MATCH_MP_TAC INCREASING THEN ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING],
   ALL_TAC] THEN
  FULL_SIMP_TAC std_ss [null_set_def, GSPECIFICATION] THEN
  METIS_TAC [SUBSET_REFL]
QED

Theorem AE_impl :
    !P M Q. measure_space M ==> ((P ==> (AE x::M. Q x)) ==>
            (AE x::M. (\x. P ==> Q x) x))
Proof
    Cases
 >- (RW_TAC bool_ss [AE_ALT] >> POP_ASSUM MP_TAC \\
    rw [EXTENSION] >> Q.EXISTS_TAC `N` \\
    RW_TAC std_ss [] >> METIS_TAC[IN_DEF])
 >> RW_TAC bool_ss [AE_ALT]
 >> rw [EXTENSION]
 >> Q.EXISTS_TAC `{}`
 >> RW_TAC bool_ss [null_set_def, NOT_IN_EMPTY,
                    MEASURE_SPACE_EMPTY_MEASURABLE]
 >> rw [MEASURE_SPACE_EMPTY_MEASURABLE]
 >> RW_TAC std_ss [MEASURE_EMPTY]
QED

Theorem AE_all_countable :
    !(t :num->num->bool) M (P :num->'a->bool).
       measure_space M ==>
       ((!i:num. countable (t i) ==> AE x::M. (\x. P i x) x) <=>
        (!i. AE x::M. (\x. P i x) x))
Proof
    RW_TAC std_ss[]
 >> EQ_TAC
 >- (RW_TAC (srw_ss()) [AE_ALT] \\
     FIRST_X_ASSUM (MP_TAC o Q.SPEC `i`) \\
     FULL_SIMP_TAC (srw_ss()) [COUNTABLE_NUM])
 >> RW_TAC (srw_ss()) [AE_ALT]
QED

Theorem AE_all_S :
    !M S' P. measure_space M ==>
             (!i. (S' i ==> (AE x::M. (\x. P i x) x))) ==>
             (!(i':num). AE x::M. (\x. (S' (i':num)) ==> (P :num->'a->bool) i' x) x)
Proof
    rpt STRIP_TAC
 >> `(\x. (S' (i' :num)) ==> P i' x) x =
     ((\(i' :num) x. (S' (i' :num))  ==> P i' x) (i' :num)) x`
       by RW_TAC std_ss []
 >> POP_ORW
 >> Q.SPEC_TAC (`i'`, `i`)
 >> dep_rewrite.DEP_REWRITE_TAC [GSYM AE_all_countable]
 >> RW_TAC std_ss []
 >> POP_ORW
 >> RW_TAC std_ss[]
 >> metis_tac [AE_impl]
QED

(* NOTE: the need of complete measure space is necessary if P is a generic property.
   This is confirmed with Prof. Massimo Campanino (University of Bologna, Italy):

   "If P is a generic property, as you say this set is not necessarily measurable."
 *)
Theorem AE_IMP_MEASURABLE_SETS :
    !m P. complete_measure_space m /\ (AE x::m. P x) ==>
          {x | x IN m_space m /\ P x} IN measurable_sets m
Proof
    RW_TAC std_ss [complete_measure_space_def]
 >> fs [AE_ALT]
 >> ‘{x | x IN m_space m /\ P x} = m_space m DIFF {x | x IN m_space m /\ ~P x}’
      by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC MEASURE_SPACE_COMPL >> art []
 >> FIRST_X_ASSUM irule
 >> Q.EXISTS_TAC ‘N’ >> art []
QED

(* NOTE: the need of complete measure space is necessary.
   This is confirmed with Prof. Massimo Campanino (University of Bologna, Italy):

   "No, in general g is not measurable."
 *)
Theorem IN_MEASURABLE_BOREL_AE_EQ :
    !m f g. complete_measure_space m /\ (AE x::m. f x = g x) /\
            f IN measurable (m_space m,measurable_sets m) Borel ==>
            g IN measurable (m_space m,measurable_sets m) Borel
Proof
    rpt STRIP_TAC
 (* complete_measure_space is used here indirectly *)
 >> ‘{x | x IN m_space m /\ (f x = g x)} IN measurable_sets m’
      by METIS_TAC [AE_IMP_MEASURABLE_SETS]
 >> fs [complete_measure_space_def,
        AE_ALT, IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> ‘N IN measurable_sets m’ by PROVE_TAC [null_set_def]
 >> GEN_TAC
 >> ‘{x | g x < Normal c} = {x | g x < Normal c /\ (f x = g x)} UNION
                            {x | g x < Normal c /\ (f x <> g x)}’
      by SET_TAC [] >> POP_ORW
 >> ‘{x | g x < Normal c /\ (f x = g x)} = {x | f x < Normal c /\ (f x = g x)}’
      by SET_TAC [] >> POP_ORW
 >> ‘({x | f x < Normal c /\ f x = g x} UNION
      {x | g x < Normal c /\ f x <> g x}) INTER m_space m =
     ({x | f x < Normal c /\ f x = g x} INTER m_space m) UNION
     ({x | g x < Normal c /\ f x <> g x} INTER m_space m)’
      by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC MEASURE_SPACE_UNION >> art []
 (* complete_measure_space is used in this branch *)
 >> reverse CONJ_TAC
 >- (FIRST_X_ASSUM irule >> Q.EXISTS_TAC ‘N’ >> art [] \\
     MATCH_MP_TAC SUBSET_TRANS \\
     Q.EXISTS_TAC ‘{x | x IN m_space m /\ f x <> g x}’ >> art [] \\
     SET_TAC [])
 >> ‘{x | f x < Normal c /\ f x = g x} INTER m_space m =
     ({x | f x < Normal c} INTER m_space m) INTER {x | x IN m_space m /\ (f x = g x)}’
      by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC MEASURE_SPACE_INTER >> art []
QED

(* ------------------------------------------------------------------------- *)
(*  Fatou's lemma for measures (limsup and liminf) [1, p.78]                 *)
(* ------------------------------------------------------------------------- *)

val set_limsup_def = Define (* "infinitely often" *)
   `set_limsup (E :num -> 'a set) =
      BIGINTER (IMAGE (\m. BIGUNION {E n | m <= n}) UNIV)`;

val set_liminf_def = Define (* "almost always" *)
   `set_liminf (E :num -> 'a set) =
      BIGUNION (IMAGE (\m. BIGINTER {E n | m <= n}) UNIV)`;

val _ = overload_on ("limsup", ``set_limsup``);
val _ = overload_on ("liminf", ``set_liminf``);

(* alternative definition of `limsup` using `from` *)
val set_limsup_alt = store_thm
  ("set_limsup_alt",
  ``!E. set_limsup E = BIGINTER (IMAGE (\n. BIGUNION (IMAGE E (from n))) UNIV)``,
    GEN_TAC >> REWRITE_TAC [set_limsup_def]
 >> Suff `!m. BIGUNION (IMAGE E (from m)) = BIGUNION {E n | m <= n}`
 >- (Rewr' >> REWRITE_TAC [])
 >> RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_BIGUNION, GSPECIFICATION, from_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `E x'` >> art [] \\
     Q.EXISTS_TAC `x'` >> art [])
 >> Q.EXISTS_TAC `n` >> PROVE_TAC []);

(* this lemma implicitly assume `events p = UNIV` *)
val liminf_limsup = store_thm
  ("liminf_limsup", ``!(E :num -> 'a set). COMPL (liminf E) = limsup (COMPL o E)``,
    RW_TAC std_ss [set_limsup_def, set_liminf_def]
 >> SIMP_TAC std_ss [COMPL_BIGUNION_IMAGE, o_DEF]
 >> Suff `!m. COMPL (BIGINTER {E n | m <= n}) = BIGUNION {COMPL (E n) | m <= n}` >- Rewr
 >> GEN_TAC >> REWRITE_TAC [COMPL_BIGINTER]
 >> Suff `IMAGE COMPL {E n | m <= n} = {COMPL (E n) | m <= n}` >- Rewr
 >> SIMP_TAC std_ss [IMAGE_DEF, IN_COMPL, Once GSPECIFICATION]
 >> RW_TAC std_ss [Once EXTENSION, GSPECIFICATION, IN_COMPL]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (fs [COMPL_COMPL] >> Q.EXISTS_TAC `n` >> art [])
 >> fs []
 >> Q.EXISTS_TAC `E n` >> art []
 >> Q.EXISTS_TAC `n` >> art []);

val liminf_limsup_sp = store_thm (* more general form *)
  ("liminf_limsup_sp",
  ``!sp E. (!n. E n SUBSET sp) ==> (sp DIFF (liminf E) = limsup (\n. sp DIFF (E n)))``,
    RW_TAC std_ss [set_limsup_def, set_liminf_def]
 >> Q.ABBREV_TAC `f = (\m. BIGINTER {E n | m <= n})`
 >> Know `!m. f m SUBSET sp`
 >- (GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC \\
     RW_TAC std_ss [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] \\
     fs [SUBSET_DEF] >> LAST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `SUC m` \\
     POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `E (SUC m)`)) \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC `SUC m` >> RW_TAC arith_ss [])
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP GEN_COMPL_BIGUNION_IMAGE))
 >> Suff `!m. sp DIFF f m = BIGUNION {sp DIFF E n | m <= n}` >- Rewr
 >> GEN_TAC >> Q.UNABBREV_TAC `f` >> BETA_TAC
 >> Know `!x. x IN {E n | m <= n} ==> x SUBSET sp`
 >- (RW_TAC std_ss [GSPECIFICATION] >> art [])
 >> DISCH_THEN (REWRITE_TAC o wrap o (MATCH_MP GEN_COMPL_BIGINTER))
 >> Suff `(IMAGE (\x. sp DIFF x) {E n | m <= n}) = {sp DIFF E n | m <= n}` >- Rewr
 >> RW_TAC std_ss [Once EXTENSION, IMAGE_DEF, IN_DIFF, GSPECIFICATION]
 >> EQ_TAC >> rpt STRIP_TAC
 >- (Q.EXISTS_TAC `n` >> METIS_TAC [])
 >> Q.EXISTS_TAC `E n` >> art []
 >> Q.EXISTS_TAC `n` >> art []);

(* NOTE: added `measure p (BIGUNION (IMAGE A UNIV)) < PosInf` into antecendents,
   this is weaker than `measure p (m_space p) < PosInf` *)
val measure_limsup = store_thm
  ("measure_limsup",
  ``!p A. measure_space p /\ measure p (BIGUNION (IMAGE A UNIV)) < PosInf /\
         (!n. A n IN measurable_sets p) ==>
         (measure p (limsup A) = inf (IMAGE (\m. measure p (BIGUNION {A n | m <= n})) UNIV))``,
    RW_TAC std_ss []
 >> Know `(\m. measure p (BIGUNION {A n | m <= n})) =
          measure p o (\m. BIGUNION {A n | m <= n})`
 >- (FUN_EQ_TAC >> RW_TAC std_ss [o_DEF])
 >> Rewr'
 >> Suff `inf (IMAGE (measure p o (\m. BIGUNION {A n | m <= n})) UNIV) =
          measure p (BIGINTER (IMAGE (\m. BIGUNION {A n | m <= n}) UNIV))`
 >- (Rewr' >> REWRITE_TAC [set_limsup_def])
 >> MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER2
 >> Know `!m. BIGUNION {A n | m <= n} IN measurable_sets p`
 >- (GEN_TAC \\
     fs [measure_space_def, sigma_algebra_def, space_def, subsets_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [tail_countable, SUBSET_DEF, GSPECIFICATION] >> art [])
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [lt_infty] \\
      MATCH_MP_TAC let_trans \\
      Q.EXISTS_TAC `measure p (BIGUNION (IMAGE A UNIV))` >> art [] \\
      MATCH_MP_TAC INCREASING >> art [] \\
      CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
      CONJ_TAC
      >- (RW_TAC std_ss [SUBSET_DEF, IN_BIGUNION_IMAGE, IN_UNIV, IN_BIGUNION, GSPECIFICATION] \\
          Q.EXISTS_TAC `n'` >> art []) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `0`)) \\
      Suff `BIGUNION (IMAGE A UNIV) = BIGUNION {A n | 0 <= n}`
      >- DISCH_THEN (ASM_REWRITE_TAC o wrap) \\
      RW_TAC arith_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_BIGUNION, GSPECIFICATION] \\
      EQ_TAC >> RW_TAC std_ss [] >| (* 3 subgoals *)
      [ Q.EXISTS_TAC `A x'` >> art [] \\
        Q.EXISTS_TAC `x'` >> REWRITE_TAC [],
        Q.EXISTS_TAC `n` >> art [] ],
      (* goal 2 (of 2) *)
      RW_TAC arith_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION] \\
      Q.EXISTS_TAC `A n'` >> art [] \\
      Q.EXISTS_TAC `n'` >> RW_TAC arith_ss [] ]);

val measure_limsup_finite = store_thm
  ("measure_limsup_finite",
  ``!p A. measure_space p /\ measure p (m_space p) < PosInf /\
         (!n. A n IN measurable_sets p) ==>
         (measure p (limsup A) = inf (IMAGE (\m. measure p (BIGUNION {A n | m <= n})) UNIV))``,
    RW_TAC std_ss []
 >> Know `(\m. measure p (BIGUNION {A n | m <= n})) =
          measure p o (\m. BIGUNION {A n | m <= n})`
 >- (FUN_EQ_TAC >> RW_TAC std_ss [o_DEF])
 >> Rewr'
 >> Suff `inf (IMAGE (measure p o (\m. BIGUNION {A n | m <= n})) UNIV) =
          measure p (BIGINTER (IMAGE (\m. BIGUNION {A n | m <= n}) UNIV))`
 >- (Rewr' >> REWRITE_TAC [set_limsup_def])
 >> MATCH_MP_TAC MONOTONE_CONVERGENCE_BIGINTER2
 >> Know `!m. BIGUNION {A n | m <= n} IN measurable_sets p`
 >- (GEN_TAC \\
     fs [measure_space_def, sigma_algebra_def, space_def, subsets_def] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     RW_TAC std_ss [tail_countable, SUBSET_DEF, GSPECIFICATION] >> art [])
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [lt_infty] \\
      MATCH_MP_TAC let_trans >> Q.EXISTS_TAC `measure p (m_space p)` \\
      reverse CONJ_TAC >- art [] \\
      MATCH_MP_TAC INCREASING >> art [] \\
      CONJ_TAC >- PROVE_TAC [MEASURE_SPACE_INCREASING] \\
      fs [measure_space_def, sigma_algebra_def, space_def, subsets_def] \\
      reverse CONJ_TAC >- PROVE_TAC [ALGEBRA_SPACE, space_def, subsets_def] \\
      METIS_TAC [algebra_def, subset_class_def, space_def, subsets_def],
      (* goal 2 (of 2) *)
      RW_TAC arith_ss [SUBSET_DEF, IN_BIGUNION, GSPECIFICATION] \\
      Q.EXISTS_TAC `A n'` >> art [] \\
      Q.EXISTS_TAC `n'` >> RW_TAC arith_ss [] ]);

val measure_liminf = store_thm
  ("measure_liminf",
  ``!p A. measure_space p /\ (!n. A n IN measurable_sets p) ==>
         (measure p (liminf A) = sup (IMAGE (\m. measure p (BIGINTER {A n | m <= n})) UNIV))``,
    RW_TAC std_ss []
 >> Know `(\m. measure p (BIGINTER {A n | m <= n})) =
          measure p o (\m. BIGINTER {A n | m <= n})`
 >- (FUN_EQ_TAC >> RW_TAC std_ss [o_DEF]) >> Rewr'
 >> Suff `sup (IMAGE (measure p o (\m. BIGINTER {A n | m <= n})) UNIV) =
          measure p (BIGUNION (IMAGE (\m. BIGINTER {A n | m <= n}) UNIV))`
 >- (Rewr' >> REWRITE_TAC [set_liminf_def])
 >> MATCH_MP_TAC MONOTONE_CONVERGENCE2
 >> RW_TAC std_ss [IN_FUNSET, IN_UNIV] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      Know `{A n | m <= n} <> {}` >- METIS_TAC [tail_not_empty] \\
      Know `countable {A n | m <= n}` >- METIS_TAC [tail_countable] \\
      RW_TAC std_ss [COUNTABLE_ENUM] >> art [] \\
      MATCH_MP_TAC MEASURE_SPACE_BIGINTER >> art [] \\
      Q.PAT_X_ASSUM `{A n | m <= n} = X` (MP_TAC o (MATCH_MP EQ_SYM)) \\
      RW_TAC std_ss [Once EXTENSION, IN_IMAGE, IN_UNIV, GSPECIFICATION] \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `f (n :num)`)) \\
      Know `?x'. f n = f x'` >- (Q.EXISTS_TAC `n` >> REWRITE_TAC []) \\
      RW_TAC std_ss [] >> PROVE_TAC [],
      (* goal 2 (of 2) *)
      RW_TAC arith_ss [SUBSET_DEF, IN_BIGINTER, GSPECIFICATION] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC `n'` >> RW_TAC arith_ss [] ]);

(* A point belongs to `limsup E` if and only if it belongs to infinitely
   many terms of the sequence E. [2, p.76] *)
val IN_LIMSUP = store_thm
  ("IN_LIMSUP", ``!A x. x IN limsup A <=> ?N. INFINITE N /\ !n. n IN N ==> x IN (A n)``,
    rpt GEN_TAC >> EQ_TAC
 >> RW_TAC std_ss [set_limsup_def, IN_BIGINTER_IMAGE, IN_UNIV]
 >| [ (* goal 1 (of 2) *)
      Q.ABBREV_TAC `P = \n. x IN (A n)` \\
     `!n. x IN (A n) <=> P n` by PROVE_TAC [] >> POP_ORW \\
      CCONTR_TAC \\
     `?m. !n. m <= n ==> ~(P n)` by PROVE_TAC [infinitely_often_lemma] \\
      Q.UNABBREV_TAC `P` >> FULL_SIMP_TAC bool_ss [] \\
      Know `x NOTIN BIGUNION {A n | m <= n}`
      >- (SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] \\
          CCONTR_TAC >> FULL_SIMP_TAC bool_ss [] >> METIS_TAC []) \\
      DISCH_TAC >> METIS_TAC [],
      (* goal 2 (of 2) *)
      SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION] \\
      IMP_RES_TAC infinity_bound_lemma \\
      POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `m`)) \\
      Q.EXISTS_TAC `A n` >> CONJ_TAC >- PROVE_TAC [] \\
      Q.EXISTS_TAC `n` >> art [] ]);

(* A point belongs to `liminf E` if and only if it belongs to all terms
   of the sequence from a certain term on. [2, p.76] *)
val IN_LIMINF = store_thm
  ("IN_LIMINF", ``!A x. x IN liminf A <=> ?m. !n. m <= n ==> x IN (A n)``,
    rpt GEN_TAC
 >> ASSUME_TAC (SIMP_RULE std_ss [GSYM liminf_limsup, IN_COMPL, o_DEF]
                                 (Q.SPECL [`COMPL o A`, `x`] IN_LIMSUP))
 >> `x IN liminf A <=> ~(?N. INFINITE N /\ !n. n IN N ==> x NOTIN A n)` by PROVE_TAC []
 >> fs [infinitely_often_lemma]);

val limsup_suminf_indicator = store_thm
  ("limsup_suminf_indicator",
  ``!A. limsup A = {x | suminf (\n. indicator_fn (A n) x) = PosInf}``,
 (* proof *)
    RW_TAC std_ss [EXTENSION, IN_LIMSUP, GSPECIFICATION, indicator_fn_def]
 >> `(?N. INFINITE N /\ !n. n IN N ==> x IN A n) <=> ~(?m. !n. m <= n ==> x NOTIN A n)`
     by METIS_TAC [Q.SPEC `\n. x IN A n` infinitely_often_lemma]
 >> POP_ORW
 >> Suff `(?m. !n. m <= n ==> x NOTIN A n) <=> suminf (\n. if x IN A n then 1 else 0) <> PosInf`
 >- METIS_TAC []
 >> EQ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      STRIP_TAC \\
      Know `suminf (\n. if x IN A n then 1 else 0) = SIGMA (\n. if x IN A n then 1 else 0) (count m)`
      >- (MATCH_MP_TAC ext_suminf_sum \\
          RW_TAC std_ss [le_01, le_refl]) >> Rewr' \\
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
      RW_TAC std_ss [FINITE_COUNT, IN_COUNT, extreal_of_num_def, extreal_not_infty],
      (* goal 2 (of 2) *)
      Suff `~(?m. !n. m <= n ==> x NOTIN A n) ==> (suminf (\n. if x IN A n then 1 else 0) = PosInf)`
      >- METIS_TAC [] \\
      DISCH_TAC \\
      MATCH_MP_TAC ext_suminf_eq_infty \\
      CONJ_TAC >- RW_TAC std_ss [le_01, le_refl] \\
      RW_TAC std_ss [] >> fs [] \\
      Cases_on `e <= 0`
      >- (Q.EXISTS_TAC `0` >> ASM_SIMP_TAC std_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY]) \\
      fs [GSYM extreal_lt_def] \\
     `e <> NegInf /\ e <> PosInf` by PROVE_TAC [lt_imp_le, pos_not_neginf, lt_infty] \\
     `?r. Normal r = e` by PROVE_TAC [extreal_cases] \\
      fs [SKOLEM_THM] \\ (* n = f m *)
      STRIP_ASSUME_TAC (Q.SPEC `r` SIMP_REAL_ARCH) \\
     `e <= Normal (&n)` by PROVE_TAC [extreal_le_eq] \\
      fs [GSYM extreal_of_num_def] \\
      Know `!N. ?n. &N <= SIGMA (\n. if x IN A n then 1 else 0) (count n)`
      >- (Induct
          >- (Q.EXISTS_TAC `0` >> SIMP_TAC std_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY, le_refl]) \\
          POP_ASSUM STRIP_ASSUME_TAC \\
         `n' <= f n' /\ x IN A (f n')` by PROVE_TAC [] \\
         `0 <= f n' - n'` by RW_TAC arith_ss [] \\
          Q.EXISTS_TAC `SUC (f n')` \\
          Know `count (SUC (f n')) = count n' UNION {x | n' <= x /\ x <= f n'}`
          >- (RW_TAC arith_ss [EXTENSION, IN_COUNT, IN_UNION, GSPECIFICATION]) >> Rewr' \\
          Know `DISJOINT (count n') {x | n' <= x /\ x <= f n'}`
          >- (RW_TAC arith_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_COUNT, GSPECIFICATION,
                               IN_INTER]) >> DISCH_TAC \\
          Know `SIGMA (\n. if x IN A n then 1 else 0) (count n' UNION {x | n' <= x /\ x <= f n'}) =
                SIGMA (\n. if x IN A n then 1 else 0) (count n') +
                SIGMA (\n. if x IN A n then 1 else 0) {x | n' <= x /\ x <= f n'}`
          >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> art [FINITE_COUNT] \\
              CONJ_TAC >- (MATCH_MP_TAC SUBSET_FINITE_I \\
                           Q.EXISTS_TAC `count (SUC (f n'))` >> art [FINITE_COUNT] \\
                           RW_TAC arith_ss [SUBSET_DEF, IN_COUNT, GSPECIFICATION]) \\
              DISJ2_TAC >> RW_TAC std_ss [extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
          Know `&SUC N = &N + &1`
          >- (SIMP_TAC real_ss [extreal_of_num_def, extreal_add_def, extreal_11]) >> Rewr' \\
          MATCH_MP_TAC le_add2 >> art [] \\
          Know `{f n'} SUBSET {x | n' <= x /\ x <= f n'}`
          >- (RW_TAC arith_ss [SUBSET_DEF, IN_SING, GSPECIFICATION]) >> DISCH_TAC \\
          Know `SIGMA (\n. if x IN A n then 1 else 0) {f n'} = 1`
          >- (ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING]) \\
          DISCH_THEN
            ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM) \\
          MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
          RW_TAC std_ss [FINITE_SING, le_01, le_refl] \\
          MATCH_MP_TAC SUBSET_FINITE_I \\
          Q.EXISTS_TAC `count (SUC (f n'))` >> art [FINITE_COUNT] \\
          RW_TAC arith_ss [SUBSET_DEF, IN_COUNT, GSPECIFICATION]) \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPEC `n`)) \\
      Q.EXISTS_TAC `n'` \\
      MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `&n` >> art [] ]);

(* An extended version of `limsup_suminf_indicator` with spaces *)
val limsup_suminf_indicator_space = store_thm
  ("limsup_suminf_indicator_space",
  ``!a A. sigma_algebra a /\ (!n. A n IN subsets a) ==>
         (limsup A = {x | x IN space a /\ (suminf (\n. indicator_fn (A n) x) = PosInf)})``,
 (* proof *)
    RW_TAC std_ss [EXTENSION, IN_LIMSUP, GSPECIFICATION, indicator_fn_def]
 >> `(?N. INFINITE N /\ !n. n IN N ==> x IN A n) = ~(?m. !n. m <= n ==> x NOTIN A n)`
     by METIS_TAC [Q.SPEC `\n. x IN A n` infinitely_often_lemma]
 >> POP_ORW
 >> Suff `(?m. !n. m <= n ==> x NOTIN A n) <=>
          (x IN space a ==> suminf (\n. if x IN A n then 1 else 0) <> PosInf)`
 >- METIS_TAC []
 >> EQ_TAC (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      NTAC 2 STRIP_TAC \\
      Know `suminf (\n. if x IN A n then 1 else 0) = SIGMA (\n. if x IN A n then 1 else 0) (count m)`
      >- (MATCH_MP_TAC ext_suminf_sum \\
          RW_TAC std_ss [le_01, le_refl]) >> Rewr' \\
      MATCH_MP_TAC EXTREAL_SUM_IMAGE_NOT_POSINF \\
      RW_TAC std_ss [FINITE_COUNT, IN_COUNT, extreal_of_num_def, extreal_not_infty],
      (* goal 2 (of 2) *)
      Suff `~(?m. !n. m <= n ==> x NOTIN A n) ==>
               (x IN space a /\ (suminf (\n. if x IN A n then 1 else 0) = PosInf))`
      >- METIS_TAC [] \\
      DISCH_TAC \\
      CONJ_TAC >- (fs [SKOLEM_THM, sigma_algebra_def, algebra_def, subset_class_def] \\
                   PROVE_TAC [SUBSET_DEF]) \\
      MATCH_MP_TAC ext_suminf_eq_infty \\
      CONJ_TAC >- RW_TAC std_ss [le_01, le_refl] \\
      RW_TAC std_ss [] >> fs [] \\
      Cases_on `e <= 0`
      >- (Q.EXISTS_TAC `0` >> ASM_SIMP_TAC std_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY]) \\
      fs [GSYM extreal_lt_def] \\
     `e <> NegInf /\ e <> PosInf` by PROVE_TAC [lt_imp_le, pos_not_neginf, lt_infty] \\
     `?r. Normal r = e` by PROVE_TAC [extreal_cases] \\
      fs [SKOLEM_THM] \\ (* n = f m *)
      STRIP_ASSUME_TAC (Q.SPEC `r` SIMP_REAL_ARCH) \\
     `e <= Normal (&n)` by PROVE_TAC [extreal_le_eq] \\
      fs [GSYM extreal_of_num_def] \\
      Know `!N. ?n. &N <= SIGMA (\n. if x IN A n then 1 else 0) (count n)`
      >- (Induct
          >- (Q.EXISTS_TAC `0` >> SIMP_TAC std_ss [COUNT_ZERO, EXTREAL_SUM_IMAGE_EMPTY, le_refl]) \\
          POP_ASSUM STRIP_ASSUME_TAC \\
         `n' <= f n' /\ x IN A (f n')` by PROVE_TAC [] \\
         `0 <= f n' - n'` by RW_TAC arith_ss [] \\
          Q.EXISTS_TAC `SUC (f n')` \\
          Know `count (SUC (f n')) = count n' UNION {x | n' <= x /\ x <= f n'}`
          >- (RW_TAC arith_ss [EXTENSION, IN_COUNT, IN_UNION, GSPECIFICATION]) >> Rewr' \\
          Know `DISJOINT (count n') {x | n' <= x /\ x <= f n'}`
          >- (RW_TAC arith_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_COUNT, GSPECIFICATION,
                               IN_INTER]) >> DISCH_TAC \\
          Know `SIGMA (\n. if x IN A n then 1 else 0) (count n' UNION {x | n' <= x /\ x <= f n'}) =
                SIGMA (\n. if x IN A n then 1 else 0) (count n') +
                SIGMA (\n. if x IN A n then 1 else 0) {x | n' <= x /\ x <= f n'}`
          >- (irule EXTREAL_SUM_IMAGE_DISJOINT_UNION >> art [FINITE_COUNT] \\
              CONJ_TAC >- (MATCH_MP_TAC SUBSET_FINITE_I \\
                           Q.EXISTS_TAC `count (SUC (f n'))` >> art [FINITE_COUNT] \\
                           RW_TAC arith_ss [SUBSET_DEF, IN_COUNT, GSPECIFICATION]) \\
              DISJ2_TAC >> RW_TAC std_ss [extreal_of_num_def, extreal_not_infty]) >> Rewr' \\
          Know `&SUC N = &N + &1`
          >- (SIMP_TAC real_ss [extreal_of_num_def, extreal_add_def, extreal_11]) >> Rewr' \\
          MATCH_MP_TAC le_add2 >> art [] \\
          Know `{f n'} SUBSET {x | n' <= x /\ x <= f n'}`
          >- (RW_TAC arith_ss [SUBSET_DEF, IN_SING, GSPECIFICATION]) >> DISCH_TAC \\
          Know `SIGMA (\n. if x IN A n then 1 else 0) {f n'} = 1`
          >- (ASM_SIMP_TAC std_ss [EXTREAL_SUM_IMAGE_SING]) \\
          DISCH_THEN
            ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap o SYM) \\
          MATCH_MP_TAC EXTREAL_SUM_IMAGE_MONO_SET \\
          RW_TAC std_ss [FINITE_SING, le_01, le_refl] \\
          MATCH_MP_TAC SUBSET_FINITE_I \\
          Q.EXISTS_TAC `count (SUC (f n'))` >> art [FINITE_COUNT] \\
          RW_TAC arith_ss [SUBSET_DEF, IN_COUNT, GSPECIFICATION]) \\
      DISCH_THEN (STRIP_ASSUME_TAC o (Q.SPEC `n`)) \\
      Q.EXISTS_TAC `n'` \\
      MATCH_MP_TAC le_trans >> Q.EXISTS_TAC `&n` >> art [] ]);

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Mhamdi, T., Hasan, O., Tahar, S.: Formalization of Measure Theory and
      Lebesgue Integration for Probabilistic Analysis in HOL.
      ACM Trans. Embedded Comput. Syst. 12, 1--23 (2013).
  [3] Coble, A.R.: Anonymity, information, and machine-assisted proof, (2010).
  [4] Hurd, J.: Formal verification of probabilistic algorithms. (2001).
  [5] Wikipedia: https://en.wikipedia.org/wiki/Henri_Lebesgue
  [6] Chung, K.L.: A Course in Probability Theory, Third Edition. Academic Press (2001).
  [7] https://en.wikipedia.org/wiki/%C3%89mile_Borel
  [8] Hardy, G.H., Littlewood, J.E.: A Course of Pure Mathematics, Tenth Edition.
      Cambridge University Press, London (1967).
 *)
