(* ------------------------------------------------------------------------- *)
(* Borel Space and Borel-measurable functions                                *)
(* Authors: Tarek Mhamdi, Osman Hasan, Sofiene Tahar (2013) [2]              *)
(* HVG Group, Concordia University, Montreal                                 *)
(* ------------------------------------------------------------------------- *)
(* Based on the work of Aaron Coble [3] (2010)                               *)
(* Cambridge University                                                      *)
(* ------------------------------------------------------------------------- *)
(* Construction of one-dimensional household Borel measure space (lborel)    *)
(*                                                                           *)
(* Author: Chun Tian (binghe) <binghe.lisp@gmail.com> (2019 - 2021)          *)
(* Fondazione Bruno Kessler and University of Trento, Italy                  *)
(* ------------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;

open prim_recTheory arithmeticTheory numLib combinTheory res_quanTheory
     res_quanTools pairTheory pred_setTheory pred_setLib relationTheory;

open realTheory realLib seqTheory transcTheory real_sigmaTheory RealArith
     real_topologyTheory listTheory metricTheory;

open util_probTheory extrealTheory sigma_algebraTheory iterateTheory
     real_borelTheory measureTheory hurdUtils;

val _ = new_theory "borel";

val ASM_ARITH_TAC = rpt (POP_ASSUM MP_TAC) >> ARITH_TAC; (* numLib *)
val DISC_RW_KILL = DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC;
fun METIS ths tm = prove(tm, METIS_TAC ths);

val set_ss = std_ss ++ PRED_SET_ss;

val _ = hide "S";

val _ = intLib.deprecate_int ();
val _ = ratLib.deprecate_rat ();

(* ************************************************************************* *)
(*    Borel Space and Measurable functions                                   *)
(* ************************************************************************* *)

(* This is the (extreal-valued) Borel set. See ‘real_borel$borel’ for reals.

   Named after Emile Borel [7], a French mathematician and politician.

   See martingaleTheory for 2-dimensional Borel space based on pairTheory
   (term: ‘Borel CROSS Borel’).

   See examples/probability/stochastic_processesTheory for n-dimensional Borel
   spaces based on fcpTheory (term: ‘Borel of_dimension(:'N)’).

   See "Borel_def" for the old definition.

   Below is the new definition according to [1, p.61]:
 *)
Definition Borel :
    Borel = (univ(:extreal),
             {B' | ?B S. B' = (IMAGE Normal B) UNION S /\ B IN subsets borel /\
                         S IN {EMPTY; {NegInf}; {PosInf}; {NegInf; PosInf}}})
End

(* MATHEMATICAL DOUBLE-STRUCK CAPITAL B
val _ = Unicode.unicode_version {u = UTF8.chr 0x1D539, tmnm = "Borel"};
val _ = TeX_notation {hol = "Borel", TeX = ("\\ensuremath{{\\cal{B}}}", 1)};
 *)

(* for compatibility and abbreviation purposes *)
Overload Borel_measurable = “\a. measurable a Borel”;

(* Lemma 8.2 [1, p.61], another equivalent definition of ‘borel’ *)
Theorem borel_eq_real_set :
    borel = (univ(:real), IMAGE real_set (subsets Borel))
Proof
    REWRITE_TAC [Once (SYM (Q.ISPEC ‘borel’ SPACE)), space_borel]
 >> Suff ‘IMAGE real_set (subsets Borel) = subsets borel’ >- rw []
 >> rw [Borel, Once EXTENSION, IN_IMAGE, real_set_def]
 >> EQ_TAC >> rw [] (* 5 subgoals *)
 >| [ (* goal 1 (of 5) *)
      REWRITE_TAC [UNION_EMPTY] \\
      Suff ‘{real x | x <> PosInf /\ x <> NegInf /\ x IN IMAGE Normal B} = B’ >- rw [] \\
      rw [Once EXTENSION] >> EQ_TAC >> rw [] >- art [real_normal] \\
      Q.EXISTS_TAC ‘Normal x’ >> rw [extreal_not_infty, real_normal],
      (* goal 2 (of 5) *)
      Suff ‘{real x | x <> PosInf /\ x <> NegInf /\ x IN IMAGE Normal B UNION {NegInf}} = B’
      >- rw [] \\
      rw [Once EXTENSION] >> EQ_TAC >> rw [] >- art [real_normal] \\
      Q.EXISTS_TAC ‘Normal x’ >> rw [extreal_not_infty, real_normal],
      (* goal 3 (of 5) *)
      Suff ‘{real x | x <> PosInf /\ x <> NegInf /\ x IN IMAGE Normal B UNION {PosInf}} = B’
      >- rw [] \\
      rw [Once EXTENSION] >> EQ_TAC >> rw [] >- art [real_normal] \\
      Q.EXISTS_TAC ‘Normal x’ >> rw [extreal_not_infty, real_normal],
      (* goal 4 (of 5) *)
      Suff ‘{real x | x <> PosInf /\ x <> NegInf /\
                      x IN IMAGE Normal B UNION {NegInf; PosInf}} = B’ >- rw [] \\
      rw [Once EXTENSION] >> EQ_TAC >> rw [] >- art [real_normal] \\
      Q.EXISTS_TAC ‘Normal x’ >> rw [extreal_not_infty, real_normal],
      (* goal 5 (of 5) *)
      Q.EXISTS_TAC ‘IMAGE Normal x’ \\
      CONJ_TAC
      >- (Suff ‘{real y | y <> PosInf /\ y <> NegInf /\ y IN IMAGE Normal x} = x’ >- rw [] \\
          rw [Once EXTENSION] >> EQ_TAC >> rw [] >- art [real_normal] \\
          rename1 ‘y IN A’ \\
          Q.EXISTS_TAC ‘Normal y’ >> rw [extreal_not_infty, real_normal]) \\
      qexistsl_tac [‘x’, ‘EMPTY’] >> rw [] ]
QED

Theorem SPACE_BOREL :
    space Borel = UNIV
Proof
    rw [Borel]
QED

local (* small tactics for the last 16 subgoals *)
  val t_none =
      qexistsl_tac [‘B UNION B'’, ‘{}’] >> simp [] \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [];
  val t_neg =
      qexistsl_tac [‘B UNION B'’, ‘{NegInf}’] >> simp [] \\
      reverse CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []) \\
      rw [Once EXTENSION] >> METIS_TAC [];
  val t_pos =
      qexistsl_tac [‘B UNION B'’, ‘{PosInf}’] >> simp [] \\
      reverse CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []) \\
      rw [Once EXTENSION] >> METIS_TAC [];
  val t_both =
      qexistsl_tac [‘B UNION B'’, ‘{NegInf; PosInf}’] >> simp [] \\
      reverse CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []) \\
      rw [Once EXTENSION] >> METIS_TAC [];
in
Theorem SIGMA_ALGEBRA_BOREL :
    sigma_algebra Borel
Proof
    reverse (rw [Borel, SIGMA_ALGEBRA_ALT, IN_FUNSET, SUBSET_DEF])
 >- (fs [SKOLEM_THM] \\
     qexistsl_tac [‘BIGUNION (IMAGE f' UNIV)’, ‘BIGUNION (IMAGE f'' UNIV)’] \\
     CONJ_TAC >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] >> METIS_TAC []) \\
     reverse CONJ_TAC
     >- (rename1 ‘BIGUNION (IMAGE g univ(:num)) = {} \/ _’ \\
         Cases_on ‘!n. g n = {}’
         >- (DISJ1_TAC >> rw [Once EXTENSION, NOT_IN_EMPTY, IN_BIGUNION_IMAGE]) \\
         DISJ2_TAC \\
         Cases_on ‘!n. PosInf NOTIN (g n)’
         >- (DISJ1_TAC >> rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
             EQ_TAC >> rw [] >- ASM_SET_TAC [] \\
             fs [] >> Q.EXISTS_TAC ‘n’ >> ASM_SET_TAC []) \\
         DISJ2_TAC \\
         Cases_on ‘!n. NegInf NOTIN (g n)’
         >- (DISJ1_TAC >> rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
             EQ_TAC >> rw [] >- ASM_SET_TAC [] \\
             fs [] >> Q.EXISTS_TAC ‘n’ >> ASM_SET_TAC []) \\
         DISJ2_TAC \\
         fs [] >> rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         EQ_TAC >> rw [] >> ASM_SET_TAC []) \\
     MP_TAC sigma_algebra_borel \\
     rw [SIGMA_ALGEBRA_FN, IN_FUNSET])
 (* algebra Borel *)
 >> SIMP_TAC std_ss [algebra_def, subset_class_def, space_def, subsets_def,
                     GSPECIFICATION, SUBSET_UNIV]
 >> ASSUME_TAC sigma_algebra_borel
 (* 1st group *)
 >> CONJ_TAC
 >- (qexistsl_tac [‘{}’, ‘{}’] >> rw [] \\
     MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [])
 (* 2nd group *)
 >> CONJ_TAC
 >- (Q.X_GEN_TAC ‘A’ \\
     DISCH_THEN (qx_choosel_then [‘B’, ‘S’] STRIP_ASSUME_TAC) >| (* 4 subgoals *)
     [ (* goal 1 (of 4) *)
       POP_ASSUM (fs o wrap) \\
       qexistsl_tac [‘UNIV DIFF B’, ‘{NegInf; PosInf}’] >> simp [] \\
       reverse CONJ_TAC >- METIS_TAC [SIGMA_ALGEBRA_COMPL, space_borel] \\
       rw [Once EXTENSION] >> EQ_TAC >> rw [] >- METIS_TAC [extreal_cases] \\
       PROVE_TAC [],
       (* goal 2 (of 4) *)
       POP_ASSUM (fs o wrap) \\
       qexistsl_tac [‘UNIV DIFF B’, ‘{PosInf}’] >> simp [] \\
       reverse CONJ_TAC >- METIS_TAC [SIGMA_ALGEBRA_COMPL, space_borel] \\
       rw [Once EXTENSION] >> EQ_TAC >> rw [] >- METIS_TAC [extreal_cases] \\
       PROVE_TAC [],
       (* goal 3 (of 4) *)
       POP_ASSUM (fs o wrap) \\
       qexistsl_tac [‘UNIV DIFF B’, ‘{NegInf}’] >> simp [] \\
       reverse CONJ_TAC >- METIS_TAC [SIGMA_ALGEBRA_COMPL, space_borel] \\
       rw [Once EXTENSION] >> EQ_TAC >> rw [] >- METIS_TAC [extreal_cases] \\
       PROVE_TAC [],
       (* goal 3 (of 4) *)
       POP_ASSUM (fs o wrap) \\
       qexistsl_tac [‘UNIV DIFF B’, ‘{}’] >> simp [] \\
       reverse CONJ_TAC >- METIS_TAC [SIGMA_ALGEBRA_COMPL, space_borel] \\
       rw [Once EXTENSION] >> EQ_TAC >> rw [] >- METIS_TAC [extreal_cases] \\
       PROVE_TAC [] ])
 (* 3rd group *)
 >> rw [] (* 16 subgoals *)
 >| [ t_none, t_neg,  t_pos, t_both, t_neg,  t_neg,  t_both, t_both,
      t_pos,  t_both, t_pos, t_both, t_both, t_both, t_both, t_both ]
QED
end (* local env for SIGMA_ALGEBRA_BOREL *)

(* The old definition of ‘Borel’ now becomes a theorem (alternative definition),
   cf. borel_eq_less

   The proof follows Lemma 8.3 [1, p.61]
 *)

(* shared by Borel_def and Borel_eq_ge *)
val early_tactics =
 (* preparing for SIGMA_ALGEBRA_RESTRICT *)
    Q.ABBREV_TAC ‘R = IMAGE Normal UNIV’ (* the set of all normal extreals *)
 >> Know ‘R IN S’
 >- (Know ‘R = BIGUNION (IMAGE (\n. {x | Normal (-&n) <= x /\ x < Normal (&n)}) UNIV)’
     >- (Q.UNABBREV_TAC ‘R’ >> rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         reverse EQ_TAC >> rw []
         >- (Q.EXISTS_TAC ‘real x’ >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
             MATCH_MP_TAC normal_real >> REWRITE_TAC [lt_infty] \\
             CONJ_TAC >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘Normal (-&n)’ >> art [lt_infty],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘Normal (&n)’ >> art [lt_infty] ]) \\
         STRIP_ASSUME_TAC (Q.SPEC ‘x'’ SIMP_REAL_ARCH) \\
         rename1 ‘y <= &m’ \\
         STRIP_ASSUME_TAC (Q.SPEC ‘y’ SIMP_REAL_ARCH_NEG) \\
         Q.EXISTS_TAC ‘MAX (SUC m) n’ >> rw [extreal_lt_eq, extreal_le_eq] >|
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC ‘-&n’ >> rw [],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC ‘&m’ >> rw [] ]) >> Rewr' \\
     fs [SIGMA_ALGEBRA_FN, IN_FUNSET, SPACE_SIGMA, Abbr ‘S’])
 >> DISCH_TAC;

(* shared by Borel_eq_le and Borel_eq_gr *)
val early_tactics' =
 (* preparing for SIGMA_ALGEBRA_RESTRICT *)
    Q.ABBREV_TAC ‘R = IMAGE Normal UNIV’ (* the set of all normal extreals *)
 >> Know ‘R IN S’
 >- (Know ‘R = BIGUNION (IMAGE (\n. {x | Normal (-&n) < x /\ x <= Normal (&n)}) UNIV)’
     >- (Q.UNABBREV_TAC ‘R’ >> rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         reverse EQ_TAC >> rw []
         >- (Q.EXISTS_TAC ‘real x’ >> ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
             MATCH_MP_TAC normal_real >> REWRITE_TAC [lt_infty] \\
             CONJ_TAC >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘Normal (-&n)’ >> art [lt_infty],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘Normal (&n)’ >> art [lt_infty] ]) \\
         STRIP_ASSUME_TAC (Q.SPEC ‘x'’ SIMP_REAL_ARCH) \\
         rename1 ‘y <= &m’ \\
         STRIP_ASSUME_TAC (Q.SPEC ‘y’ SIMP_REAL_ARCH_NEG) \\
         Q.EXISTS_TAC ‘MAX (SUC n) m’ >> rw [extreal_lt_eq, extreal_le_eq] >|
         [ (* goal 1 (of 2) *)
           MATCH_MP_TAC REAL_LTE_TRANS >> Q.EXISTS_TAC ‘-&n’ >> rw [],
           (* goal 2 (of 2) *)
           MATCH_MP_TAC REAL_LE_TRANS >> Q.EXISTS_TAC ‘&m’ >> rw [] ]) >> Rewr' \\
     fs [SIGMA_ALGEBRA_FN, IN_FUNSET, SPACE_SIGMA, Abbr ‘S’])
 >> DISCH_TAC;

(* shared by Borel_def and Borel_eq_ge *)
val middle_tactics =
 (* applying PREIMAGE_SIGMA_ALGEBRA *)
    Know ‘sigma_algebra (UNIV, IMAGE (\s. PREIMAGE Normal s INTER UNIV)
                                     (subsets (R,IMAGE (\s. s INTER R) S)))’
 >- (MATCH_MP_TAC PREIMAGE_SIGMA_ALGEBRA >> rw [IN_FUNSET, Abbr ‘R’])
 >> REWRITE_TAC [INTER_UNIV, subsets_def, IMAGE_IMAGE]
 >> ‘((\s. PREIMAGE Normal s) o (\s. s INTER R)) = real_set’
       by rw [FUN_EQ_THM, Abbr ‘R’, normal_real_set, o_DEF, IN_APP] >> POP_ORW
 >> DISCH_TAC
 (* preparing for SIGMA_SUBSET *)
 >> Know ‘!a b. a <= b ==> {x | a <= x /\ x < b} IN IMAGE real_set S’
 >- (rw [real_set_def] \\
     Q.EXISTS_TAC ‘{x | Normal a <= x /\ x < Normal b}’ \\
     reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.EXISTS_TAC ‘Normal x’ \\
       rw [extreal_not_infty, real_normal, extreal_lt_eq, extreal_le_eq],
       (* goal 2 (of 3) *)
       rename1 ‘a <= real y’ >> REWRITE_TAC [GSYM extreal_le_eq] \\
       Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
       MATCH_MP_TAC normal_real >> art [],
       (* goal 3 (of 3) *)
       rename1 ‘real y < b’ >> REWRITE_TAC [GSYM extreal_lt_eq] \\
       Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
       MATCH_MP_TAC normal_real >> art [] ])
 >> DISCH_TAC
 (* applying SIGMA_SUBSET *)
 >> Know ‘subsets (sigma UNIV (IMAGE (\(a,b). {x | a <= x /\ x < b}) UNIV))
          SUBSET (IMAGE real_set S)’
 >- (MATCH_MP_TAC
       (REWRITE_RULE [space_def, subsets_def]
         (Q.ISPECL [‘IMAGE (\(a,b). {x | a <= x /\ x < b}) univ(:real # real)’,
                    ‘(univ(:real),IMAGE real_set S)’] SIGMA_SUBSET)) \\
     simp [SUBSET_DEF, IN_IMAGE, IN_UNIV, real_set_def] \\
     Q.X_GEN_TAC ‘z’ \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ MP_TAC) \\
     Cases_on ‘y’ >> rw [] \\
     Cases_on ‘q <= r’
     >- (Q.EXISTS_TAC ‘{x | Normal q <= x /\ x < Normal r}’ \\
         reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
         rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Q.EXISTS_TAC ‘Normal x’ \\
           rw [extreal_not_infty, real_normal, extreal_lt_eq, extreal_le_eq],
           (* goal 2 (of 3) *)
           rename1 ‘a <= real y’ >> REWRITE_TAC [GSYM extreal_le_eq] \\
           Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
           MATCH_MP_TAC normal_real >> art [],
           (* goal 3 (of 3) *)
           rename1 ‘real y < b’ >> REWRITE_TAC [GSYM extreal_lt_eq] \\
           Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
           MATCH_MP_TAC normal_real >> art [] ]) \\
     Know ‘{x | q <= x /\ x < r} = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
         ONCE_REWRITE_TAC [DISJ_COMM] >> STRONG_DISJ_TAC \\
        ‘r < q’ by METIS_TAC [real_lt] \\
         REWRITE_TAC [GSYM real_lt] \\
         MATCH_MP_TAC REAL_LT_TRANS >> Q.EXISTS_TAC ‘r’ >> art []) >> Rewr' \\
     Q.EXISTS_TAC ‘{}’ \\
     reverse CONJ_TAC
     >- (Q.UNABBREV_TAC ‘S’ \\
         MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art []) \\
     rw [NOT_IN_EMPTY, Once EXTENSION])
 >> REWRITE_TAC [GSYM borel_eq_ge_less] (* key step *)
 >> DISCH_TAC;

(* shared by Borel_eq_le and Borel_eq_gr *)
val middle_tactics' =
 (* applying PREIMAGE_SIGMA_ALGEBRA *)
    Know ‘sigma_algebra (UNIV, IMAGE (\s. PREIMAGE Normal s INTER UNIV)
                                     (subsets (R,IMAGE (\s. s INTER R) S)))’
 >- (MATCH_MP_TAC PREIMAGE_SIGMA_ALGEBRA >> rw [IN_FUNSET, Abbr ‘R’])
 >> REWRITE_TAC [INTER_UNIV, subsets_def, IMAGE_IMAGE]
 >> ‘((\s. PREIMAGE Normal s) o (\s. s INTER R)) = real_set’
       by rw [FUN_EQ_THM, Abbr ‘R’, normal_real_set, o_DEF, IN_APP] >> POP_ORW
 >> DISCH_TAC
 (* preparing for SIGMA_SUBSET *)
 >> Know ‘!a b. a <= b ==> {x | a < x /\ x <= b} IN IMAGE real_set S’
 >- (rw [real_set_def] \\
     Q.EXISTS_TAC ‘{x | Normal a < x /\ x <= Normal b}’ \\
     reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Q.EXISTS_TAC ‘Normal x’ \\
       rw [extreal_not_infty, real_normal, extreal_lt_eq, extreal_le_eq],
       (* goal 2 (of 3) *)
       rename1 ‘a < real y’ >> REWRITE_TAC [GSYM extreal_lt_eq] \\
       Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
       MATCH_MP_TAC normal_real >> art [],
       (* goal 3 (of 3) *)
       rename1 ‘real y <= b’ >> REWRITE_TAC [GSYM extreal_le_eq] \\
       Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
       MATCH_MP_TAC normal_real >> art [] ])
 >> DISCH_TAC
 (* applying SIGMA_SUBSET *)
 >> Know ‘subsets (sigma UNIV (IMAGE (\(a,b). {x | a < x /\ x <= b}) UNIV))
          SUBSET (IMAGE real_set S)’
 >- (MATCH_MP_TAC
       (REWRITE_RULE [space_def, subsets_def]
         (Q.ISPECL [‘IMAGE (\(a,b). {x | a < x /\ x <= b}) univ(:real # real)’,
                    ‘(univ(:real),IMAGE real_set S)’] SIGMA_SUBSET)) \\
     simp [SUBSET_DEF, IN_IMAGE, IN_UNIV, real_set_def] \\
     Q.X_GEN_TAC ‘z’ \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘y’ MP_TAC) \\
     Cases_on ‘y’ >> rw [] \\
     Cases_on ‘q <= r’
     >- (Q.EXISTS_TAC ‘{x | Normal q < x /\ x <= Normal r}’ \\
         reverse CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
         rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Q.EXISTS_TAC ‘Normal x’ \\
           rw [extreal_not_infty, real_normal, extreal_lt_eq, extreal_le_eq],
           (* goal 2 (of 3) *)
           rename1 ‘q < real y’ >> REWRITE_TAC [GSYM extreal_lt_eq] \\
           Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
           MATCH_MP_TAC normal_real >> art [],
           (* goal 3 (of 3) *)
           rename1 ‘real y <= r’ >> REWRITE_TAC [GSYM extreal_le_eq] \\
           Suff ‘Normal (real y) = y’ >- RW_TAC std_ss [] \\
           MATCH_MP_TAC normal_real >> art [] ]) \\
     Know ‘{x | q < x /\ x <= r} = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY] \\
         ONCE_REWRITE_TAC [DISJ_COMM] >> STRONG_DISJ_TAC \\
        ‘r < q’ by METIS_TAC [real_lt] \\
         REWRITE_TAC [real_lt] \\
         MATCH_MP_TAC REAL_LT_IMP_LE \\
         MATCH_MP_TAC REAL_LET_TRANS >> Q.EXISTS_TAC ‘r’ >> art []) >> Rewr' \\
     Q.EXISTS_TAC ‘{}’ \\
     reverse CONJ_TAC
     >- (Q.UNABBREV_TAC ‘S’ \\
         MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art []) \\
     rw [NOT_IN_EMPTY, Once EXTENSION])
 >> REWRITE_TAC [GSYM borel_eq_gr_le] (* key step *)
 >> DISCH_TAC;

val final_tactics = (* shared by all four Borel_eq theorems *)
    Know ‘IMAGE Normal B IN S’
 >- (Suff ‘IMAGE Normal B IN IMAGE (\s. s INTER R) S’
     >- (Suff ‘IMAGE (\s. s INTER R) S SUBSET S’ >- METIS_TAC [SUBSET_DEF] \\
         Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
         rw [SUBSET_DEF, Abbr ‘S’] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []) \\
     Q.PAT_X_ASSUM ‘subsets borel SUBSET IMAGE real_set S’ MP_TAC \\
     Know ‘B IN subsets borel’ >- rw [] \\
     Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
     rw [SUBSET_DEF, real_set_def] \\
     POP_ASSUM (MP_TAC o (Q.SPEC ‘B’)) >> RW_TAC std_ss [] \\
     rename1 ‘s IN S’ >> Q.EXISTS_TAC ‘s’ >> art [] \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       METIS_TAC [normal_real],
       (* goal 2 (of 3) *)
       Q.UNABBREV_TAC ‘R’ >> rw [],
       (* goal 3 (of 3) *)
       POP_ASSUM MP_TAC >> rw [Abbr ‘R’] \\
       rename1 ‘Normal r IN s’ \\
       Q.EXISTS_TAC ‘Normal r’ >> rw [real_normal, extreal_not_infty] ])
 >> DISCH_TAC
 >> fs [] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      Q.UNABBREV_TAC ‘S’ \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [],
      (* goal 2 (of 3) *)
      Q.UNABBREV_TAC ‘S’ \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [],
      (* goal 3 (of 3) *)
      Q.UNABBREV_TAC ‘S’ \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
     ‘{NegInf; PosInf} = {NegInf} UNION {PosInf}’ by SET_TAC [] >> POP_ORW \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] ];

(* The original definition of Borel now becomes a theorem *)
Theorem Borel_def :
    Borel = sigma univ(:extreal) (IMAGE (\a. {x | x < Normal a}) univ(:real))
Proof
    Suff ‘subsets (sigma UNIV (IMAGE (\a. {x | x < Normal a}) UNIV)) = subsets Borel’
 >- METIS_TAC [SPACE, SPACE_BOREL, SPACE_SIGMA]
 >> Q.ABBREV_TAC ‘S = subsets (sigma UNIV (IMAGE (\a. {x | x < Normal a}) UNIV))’
 >> Know ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | x < Normal a}) UNIV))’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def])
 >> DISCH_TAC
 >> MATCH_MP_TAC SUBSET_ANTISYM
 (* easy part *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC (REWRITE_RULE [SPACE_BOREL]
                                (Q.ISPECL [‘IMAGE (\a. {x | x < Normal a}) UNIV’, ‘Borel’]
                                          SIGMA_SUBSET)) \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL] \\
     rw [SUBSET_DEF, IN_IMAGE, Borel] \\
     qexistsl_tac [‘{y | y < a}’, ‘{NegInf}’] \\
     CONJ_TAC
     >- (rw [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Cases_on ‘x = NegInf’ >- rw [] >> DISJ1_TAC \\
           Know ‘x <> PosInf’
           >- (REWRITE_TAC [lt_infty] \\
               MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘Normal a’ >> art [lt_infty]) \\
           DISCH_TAC >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] \\
           Q.EXISTS_TAC ‘r’ >> fs [extreal_lt_eq],
           (* goal 2 (of 3) *)
           rw [extreal_lt_eq],
           (* goal 3 (of 3) *)
           REWRITE_TAC [lt_infty] ]) \\
     reverse CONJ_TAC >- rw [] \\
     REWRITE_TAC [borel_measurable_sets_less])
 (* more properties of S *)
 >> Know ‘!a b. a <= b ==> {x | Normal a <= x /\ x < Normal b} IN S’
 >- (rpt STRIP_TAC \\
    ‘{x | Normal a <= x /\ x < Normal b} =
     {x | x < Normal b} DIFF {x | x < Normal a}’ by SET_TAC [extreal_lt_def] >> POP_ORW \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_DIFF >> art [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff ‘{x | x < Normal b} IN (IMAGE (\a. {x | x < Normal a}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘b’ >> rw [],
       (* goal 2 (of 2) *)
       Suff ‘{x | x < Normal a} IN (IMAGE (\a. {x | x < Normal a}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘a’ >> rw [] ]) >> DISCH_TAC
 (* adding new assumptions:
    3.  Abbrev (R = IMAGE Normal univ(:real))
    4.  R IN S
  *)
 >> early_tactics
 (* applying SIGMA_ALGEBRA_RESTRICT *)
 >> Know ‘sigma_algebra (R,IMAGE (\s. s INTER R) S)’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT >> art [] \\
     Q.EXISTS_TAC ‘space (sigma UNIV (IMAGE (\a. {x | x < Normal a}) UNIV))’ \\
     rw [Abbr ‘S’, SPACE])
 >> DISCH_TAC
 (* adding new assumptions:
    6.  sigma_algebra (univ(:real),IMAGE real_set S)
    7.  !a b. a <= b ==> {x | a <= x /\ x < b} IN IMAGE real_set S
    8.  subsets borel SUBSET IMAGE real_set S
  *)
 >> middle_tactics
 (* stage work *)
 >> simp [SUBSET_DEF, Borel]
 >> GEN_TAC >> DISCH_THEN (qx_choosel_then [‘B’,‘X’] ASSUME_TAC)
 >> ‘x = IMAGE Normal B UNION X’ by PROVE_TAC [] >> POP_ORW
 >> Know ‘{NegInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
     Know ‘{NegInf} = BIGINTER (IMAGE (\n. {x | x < Normal (-&n)}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGINTER_IMAGE] \\
         EQ_TAC >- METIS_TAC [num_not_infty,lt_infty,extreal_ainv_def,extreal_of_num_def] \\
         RW_TAC std_ss [] \\
         SPOSE_NOT_THEN ASSUME_TAC \\
         METIS_TAC [SIMP_EXTREAL_ARCH_NEG, extreal_of_num_def,
                    extreal_lt_def, extreal_ainv_def, neg_neg, lt_neg]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | x < Normal a}) UNIV))’
        (STRIP_ASSUME_TAC o (MATCH_MP SIGMA_ALGEBRA_FN_BIGINTER)) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | x < Normal (-&n)} IN (IMAGE (\a. {x | x < Normal a}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘-&n’ >> rw [])
 >> DISCH_TAC
 >> Know ‘{PosInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
    ‘{PosInf} = (space (sigma UNIV (IMAGE (\a. {x | x < Normal a}) UNIV))) DIFF
                {x | x <> PosInf}’ by SET_TAC [SPACE_SIGMA] >> POP_ORW \\
     Know ‘{x | x <> PosInf} = BIGUNION (IMAGE (\n. {x | x < Normal (&n)}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         reverse EQ_TAC
         >- METIS_TAC [num_not_infty, lt_infty, extreal_ainv_def, extreal_of_num_def] \\
         RW_TAC std_ss [] \\
        ‘?n. x <= &n’ by METIS_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC ‘SUC n’ \\
         MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘Normal &n’ \\
         fs [extreal_of_num_def, extreal_lt_eq, extreal_le_eq]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [] \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | x < Normal a}) UNIV))’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [SIGMA_ALGEBRA_FN])) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | x < Normal (&n)} IN (IMAGE (\a. {x | x < Normal a}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘&n’ >> rw [])
 >> DISCH_TAC
 >> final_tactics
QED

Theorem Borel_eq_ge :
    Borel = sigma univ(:extreal) (IMAGE (\a. {x | Normal a <= x}) univ(:real))
Proof
    Suff ‘subsets (sigma UNIV (IMAGE (\a. {x | Normal a <= x}) UNIV)) = subsets Borel’
 >- METIS_TAC [SPACE, SPACE_BOREL, SPACE_SIGMA]
 >> Q.ABBREV_TAC ‘S = subsets (sigma UNIV (IMAGE (\a. {x | Normal a <= x}) UNIV))’
 >> Know ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | Normal a <= x}) UNIV))’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def])
 >> DISCH_TAC
 >> MATCH_MP_TAC SUBSET_ANTISYM
 (* easy part *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC (REWRITE_RULE [SPACE_BOREL]
                                (Q.ISPECL [‘IMAGE (\a. {x | Normal a <= x}) UNIV’, ‘Borel’]
                                          SIGMA_SUBSET)) \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL] \\
     rw [SUBSET_DEF, IN_IMAGE, Borel] \\
     qexistsl_tac [‘{y | a <= y}’, ‘{PosInf}’] >> simp [] \\
     CONJ_TAC
     >- (rw [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Cases_on ‘x = PosInf’ >- rw [] >> DISJ1_TAC \\
           Know ‘x <> NegInf’
           >- (REWRITE_TAC [lt_infty] \\
               MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘Normal a’ >> art [lt_infty]) \\
           DISCH_TAC >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] \\
           Q.EXISTS_TAC ‘r’ >> fs [extreal_le_eq],
           (* goal 2 (of 3) *)
           rw [extreal_le_eq],
           (* goal 3 (of 3) *)
           REWRITE_TAC [le_infty] ]) \\
     REWRITE_TAC [borel_measurable_sets_ge])
 (* more properties of S *)
 >> Know ‘!a b. a <= b ==> {x | Normal a <= x /\ x < Normal b} IN S’
 >- (rpt STRIP_TAC \\
    ‘{x | Normal a <= x /\ x < Normal b} =
     {x | Normal a <= x} DIFF {x | Normal b <= x}’ by SET_TAC [extreal_lt_def] >> POP_ORW \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_DIFF >> art [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff ‘{x | Normal a <= x} IN (IMAGE (\a. {x | Normal a <= x}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘a’ >> rw [],
       (* goal 2 (of 2) *)
       Suff ‘{x | Normal b <= x} IN (IMAGE (\a. {x | Normal a <= x}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘b’ >> rw [] ]) >> DISCH_TAC
 >> early_tactics
 (* applying SIGMA_ALGEBRA_RESTRICT *)
 >> Know ‘sigma_algebra (R,IMAGE (\s. s INTER R) S)’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT >> art [] \\
     Q.EXISTS_TAC ‘space (sigma UNIV (IMAGE (\a. {x | Normal a <= x}) UNIV))’ \\
     rw [Abbr ‘S’, SPACE])
 >> DISCH_TAC
 >> middle_tactics
 (* stage work *)
 >> simp [SUBSET_DEF, Borel]
 >> GEN_TAC >> DISCH_THEN (qx_choosel_then [‘B’,‘X’] ASSUME_TAC)
 >> ‘x = IMAGE Normal B UNION X’ by PROVE_TAC [] >> POP_ORW
 >> Know ‘{PosInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
     Know ‘{PosInf} = BIGINTER (IMAGE (\n. {x | Normal (&n) <= x}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGINTER_IMAGE] \\
         EQ_TAC >- rw [le_infty] \\
         RW_TAC std_ss [] \\
         SPOSE_NOT_THEN ASSUME_TAC \\
        ‘?n. x <= &n’ by METIS_TAC [SIMP_EXTREAL_ARCH] \\
         fs [extreal_of_num_def] \\
         Q.PAT_X_ASSUM ‘!n. Normal (&n) <= x’ (STRIP_ASSUME_TAC o (Q.SPEC ‘SUC n’)) \\
        ‘Normal (&SUC n) <= Normal (&n)’ by PROVE_TAC [le_trans] \\
         fs [extreal_le_eq]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | Normal a <= x}) UNIV))’
        (STRIP_ASSUME_TAC o (MATCH_MP SIGMA_ALGEBRA_FN_BIGINTER)) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | Normal (&n) <= x} IN (IMAGE (\a. {x | Normal a <= x}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘&n’ >> rw [])
 >> DISCH_TAC
 >> Know ‘{NegInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
    ‘{NegInf} = (space (sigma UNIV (IMAGE (\a. {x | Normal a <= x}) UNIV))) DIFF
                {x | x <> NegInf}’ by SET_TAC [SPACE_SIGMA] >> POP_ORW \\
     Know ‘{x | x <> NegInf} = BIGUNION (IMAGE (\n. {x | Normal (-&n) <= x}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         reverse EQ_TAC
         >- (rw [lt_infty] \\
             MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘Normal (-&n)’ >> rw [lt_infty]) \\
         RW_TAC std_ss [] \\
        ‘?n. -&n <= x’ by METIS_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC ‘n’ >> fs [extreal_of_num_def, extreal_ainv_def]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [] \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | Normal a <= x}) UNIV))’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [SIGMA_ALGEBRA_FN])) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | Normal (-&n) <= x} IN (IMAGE (\a. {x | Normal a <= x}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘-&n’ >> rw [])
 >> DISCH_TAC
 >> final_tactics
QED

Theorem Borel_eq_le : (* cf. borel_eq_le (borel_def) *)
    Borel = sigma univ(:extreal) (IMAGE (\a. {x | x <= Normal a}) univ(:real))
Proof
    Suff ‘subsets (sigma UNIV (IMAGE (\a. {x | x <= Normal a}) UNIV)) = subsets Borel’
 >- METIS_TAC [SPACE, SPACE_BOREL, SPACE_SIGMA]
 >> Q.ABBREV_TAC ‘S = subsets (sigma UNIV (IMAGE (\a. {x | x <= Normal a}) UNIV))’
 >> Know ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | x <= Normal a}) UNIV))’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def])
 >> DISCH_TAC
 >> MATCH_MP_TAC SUBSET_ANTISYM
 (* easy part *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC (REWRITE_RULE [SPACE_BOREL]
                                (Q.ISPECL [‘IMAGE (\a. {x | x <= Normal a}) UNIV’, ‘Borel’]
                                          SIGMA_SUBSET)) \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL] \\
     rw [SUBSET_DEF, IN_IMAGE, Borel] \\
     qexistsl_tac [‘{y | y <= a}’, ‘{NegInf}’] \\
     CONJ_TAC
     >- (rw [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Cases_on ‘x = NegInf’ >- rw [] >> DISJ1_TAC \\
           Know ‘x <> PosInf’
           >- (REWRITE_TAC [lt_infty] \\
               MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘Normal a’ >> art [lt_infty]) \\
           DISCH_TAC >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] \\
           Q.EXISTS_TAC ‘r’ >> fs [extreal_le_eq],
           (* goal 2 (of 3) *)
           fs [extreal_le_eq],
           (* goal 3 (of 3) *)
           REWRITE_TAC [le_infty] ]) \\
     reverse CONJ_TAC >- rw [] \\
     REWRITE_TAC [borel_measurable_sets_le])
 (* more properties of S *)
 >> Know ‘!a b. a <= b ==> {x | Normal a < x /\ x <= Normal b} IN S’
 >- (rpt STRIP_TAC \\
    ‘{x | Normal a < x /\ x <= Normal b} =
     {x | x <= Normal b} DIFF {x | x <= Normal a}’ by SET_TAC [extreal_lt_def] >> POP_ORW \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_DIFF >> art [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff ‘{x | x <= Normal b} IN (IMAGE (\a. {x | x <= Normal a}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘b’ >> rw [],
       (* goal 2 (of 2) *)
       Suff ‘{x | x <= Normal a} IN (IMAGE (\a. {x | x <= Normal a}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘a’ >> rw [] ]) >> DISCH_TAC
 >> early_tactics'
 (* applying SIGMA_ALGEBRA_RESTRICT *)
 >> Know ‘sigma_algebra (R,IMAGE (\s. s INTER R) S)’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT >> art [] \\
     Q.EXISTS_TAC ‘space (sigma UNIV (IMAGE (\a. {x | x <= Normal a}) UNIV))’ \\
     rw [Abbr ‘S’, SPACE])
 >> DISCH_TAC
 >> middle_tactics'
 (* stage work *)
 >> simp [SUBSET_DEF, Borel]
 >> GEN_TAC >> DISCH_THEN (qx_choosel_then [‘B’,‘X’] ASSUME_TAC)
 >> ‘x = IMAGE Normal B UNION X’ by PROVE_TAC [] >> POP_ORW
 >> Know ‘{NegInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
     Know ‘{NegInf} = BIGINTER (IMAGE (\n. {x | x <= Normal (-&n)}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGINTER_IMAGE] \\
         EQ_TAC >- rw [le_infty] \\
         RW_TAC std_ss [] \\
         SPOSE_NOT_THEN ASSUME_TAC \\
        ‘?n. -&n <= x’ by METIS_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         fs [extreal_of_num_def, extreal_ainv_def] \\
         Q.PAT_X_ASSUM ‘!n. x <= Normal (-&n)’ (STRIP_ASSUME_TAC o (Q.SPEC ‘SUC n’)) \\
        ‘Normal (-&n) <= Normal (-&SUC n)’ by PROVE_TAC [le_trans] \\
         fs [extreal_le_eq]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | x <= Normal a}) UNIV))’
        (STRIP_ASSUME_TAC o (MATCH_MP SIGMA_ALGEBRA_FN_BIGINTER)) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | x <= Normal (-&n)} IN (IMAGE (\a. {x | x <= Normal a}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘-&n’ >> rw [])
 >> DISCH_TAC
 >> Know ‘{PosInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
    ‘{PosInf} = (space (sigma UNIV (IMAGE (\a. {x | x <= Normal a}) UNIV))) DIFF
                {x | x <> PosInf}’ by SET_TAC [SPACE_SIGMA] >> POP_ORW \\
     Know ‘{x | x <> PosInf} = BIGUNION (IMAGE (\n. {x | x <= Normal (&n)}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         reverse EQ_TAC
         >- (rw [lt_infty] \\
             MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘Normal (&n)’ >> rw [lt_infty]) \\
         RW_TAC std_ss [] \\
        ‘?n. x <= &n’ by METIS_TAC [SIMP_EXTREAL_ARCH] \\
         Q.EXISTS_TAC ‘n’ >> fs [extreal_of_num_def]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [] \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | x <= Normal a}) UNIV))’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [SIGMA_ALGEBRA_FN])) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | x <= Normal (&n)} IN (IMAGE (\a. {x | x <= Normal a}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘&n’ >> rw [])
 >> DISCH_TAC
 >> final_tactics
QED

Theorem Borel_eq_gr : (* cf. borel_eq_gr *)
    Borel = sigma univ(:extreal) (IMAGE (\a. {x | Normal a < x}) univ(:real))
Proof
    Suff ‘subsets (sigma UNIV (IMAGE (\a. {x | Normal a < x}) UNIV)) = subsets Borel’
 >- METIS_TAC [SPACE, SPACE_BOREL, SPACE_SIGMA]
 >> Q.ABBREV_TAC ‘S = subsets (sigma UNIV (IMAGE (\a. {x | Normal a < x}) UNIV))’
 >> Know ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | Normal a < x}) UNIV))’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_SIGMA >> rw [subset_class_def])
 >> DISCH_TAC
 >> MATCH_MP_TAC SUBSET_ANTISYM
 (* easy part *)
 >> CONJ_TAC
 >- (Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC (REWRITE_RULE [SPACE_BOREL]
                                (Q.ISPECL [‘IMAGE (\a. {x | Normal a < x}) UNIV’, ‘Borel’]
                                          SIGMA_SUBSET)) \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL] \\
     rw [SUBSET_DEF, IN_IMAGE, Borel] \\
     qexistsl_tac [‘{y | a < y}’, ‘{PosInf}’] \\
     CONJ_TAC
     >- (rw [Once EXTENSION, IN_IMAGE, IN_UNIV] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ (* goal 1 (of 3) *)
           Cases_on ‘x = PosInf’ >- rw [] >> DISJ1_TAC \\
           Know ‘x <> NegInf’
           >- (REWRITE_TAC [lt_infty] \\
               MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘Normal a’ >> art [lt_infty]) \\
           DISCH_TAC >> ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] \\
           Q.EXISTS_TAC ‘r’ >> fs [extreal_lt_eq],
           (* goal 2 (of 3) *)
           fs [extreal_lt_eq],
           (* goal 3 (of 3) *)
           REWRITE_TAC [lt_infty] ]) \\
     reverse CONJ_TAC >- rw [] \\
     REWRITE_TAC [borel_measurable_sets_gr])
 (* more properties of S *)
 >> Know ‘!a b. a <= b ==> {x | Normal a < x /\ x <= Normal b} IN S’
 >- (rpt STRIP_TAC \\
    ‘{x | Normal a < x /\ x <= Normal b} =
     {x | Normal a < x} DIFF {x | Normal b < x}’ by SET_TAC [extreal_lt_def] >> POP_ORW \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_DIFF >> art [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff ‘{x | Normal a < x} IN (IMAGE (\a. {x | Normal a < x}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘a’ >> rw [],
       (* goal 2 (of 2) *)
       Suff ‘{x | Normal b < x} IN (IMAGE (\a. {x | Normal a < x}) UNIV)’
       >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
       rw [IN_IMAGE] >> Q.EXISTS_TAC ‘b’ >> rw [] ]) >> DISCH_TAC
 >> early_tactics'
 (* applying SIGMA_ALGEBRA_RESTRICT *)
 >> Know ‘sigma_algebra (R,IMAGE (\s. s INTER R) S)’
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_RESTRICT >> art [] \\
     Q.EXISTS_TAC ‘space (sigma UNIV (IMAGE (\a. {x | Normal a < x}) UNIV))’ \\
     rw [Abbr ‘S’, SPACE])
 >> DISCH_TAC
 >> middle_tactics'
 (* stage work *)
 >> simp [SUBSET_DEF, Borel]
 >> GEN_TAC >> DISCH_THEN (qx_choosel_then [‘B’,‘X’] ASSUME_TAC)
 >> ‘x = IMAGE Normal B UNION X’ by PROVE_TAC [] >> POP_ORW
 >> Know ‘{PosInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
     Know ‘{PosInf} = BIGINTER (IMAGE (\n. {x | Normal (&n) < x}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGINTER_IMAGE] \\
         EQ_TAC >- rw [lt_infty] \\
         RW_TAC std_ss [] \\
         SPOSE_NOT_THEN ASSUME_TAC \\
        ‘?n. x <= &n’ by METIS_TAC [SIMP_EXTREAL_ARCH] \\
         fs [extreal_of_num_def] \\
         Q.PAT_X_ASSUM ‘!n. Normal (&n) < x’ (STRIP_ASSUME_TAC o (Q.SPEC ‘n’)) \\
        ‘x < x’ by PROVE_TAC [let_trans] \\
         PROVE_TAC [lt_refl]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | Normal a < x}) UNIV))’
        (STRIP_ASSUME_TAC o (MATCH_MP SIGMA_ALGEBRA_FN_BIGINTER)) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | Normal (&n) < x} IN (IMAGE (\a. {x | Normal a < x}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘&n’ >> rw [])
 >> DISCH_TAC
 >> Know ‘{NegInf} IN S’
 >- (Q.PAT_X_ASSUM ‘x = IMAGE Normal B UNION X /\ _’ K_TAC \\
    ‘{NegInf} = (space (sigma UNIV (IMAGE (\a. {x | Normal a < x}) UNIV))) DIFF
                {x | x <> NegInf}’ by SET_TAC [SPACE_SIGMA] >> POP_ORW \\
     Know ‘{x | x <> NegInf} = BIGUNION (IMAGE (\n. {x | Normal (-&n) < x}) UNIV)’
     >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
         reverse EQ_TAC
         >- (rw [lt_infty] \\
             MATCH_MP_TAC lt_trans >> Q.EXISTS_TAC ‘Normal (-&n)’ >> rw [lt_infty]) \\
         RW_TAC std_ss [] \\
        ‘?n. -&n <= x’ by METIS_TAC [SIMP_EXTREAL_ARCH_NEG] \\
         Q.EXISTS_TAC ‘SUC n’ >> fs [extreal_of_num_def, extreal_ainv_def] \\
         MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘Normal (-&n)’ \\
         rw [extreal_lt_eq]) >> Rewr' \\
     Q.UNABBREV_TAC ‘S’ \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [] \\
     Q.PAT_X_ASSUM ‘sigma_algebra (sigma UNIV (IMAGE (\a. {x | Normal a < x}) UNIV))’
        (STRIP_ASSUME_TAC o (REWRITE_RULE [SIGMA_ALGEBRA_FN])) \\
     POP_ASSUM MATCH_MP_TAC \\
     rw [IN_FUNSET] \\
     Suff ‘{x | Normal (-&n) < x} IN (IMAGE (\a. {x | Normal a < x}) UNIV)’
     >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
     rw [] >> Q.EXISTS_TAC ‘-&n’ >> rw [])
 >> DISCH_TAC
 >> final_tactics
QED

(* NOTE: moved ‘sigma_algebra a’ to antecedents due to changes of ‘measurable’ *)
Theorem MEASURABLE_BOREL :
    !f a. sigma_algebra a ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c. ((PREIMAGE f {x| x < Normal c}) INTER (space a)) IN subsets a)
Proof
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
 >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL :
    !f a. sigma_algebra a ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c. ({x | f x < Normal c} INTER space a) IN subsets a)
Proof
  RW_TAC std_ss []
  >> `!c. {x | f x < Normal c} = PREIMAGE f {x| x < Normal c}`
       by RW_TAC std_ss [EXTENSION,IN_PREIMAGE,GSPECIFICATION]
  >> RW_TAC std_ss [MEASURABLE_BOREL]
QED

(* NOTE: added ‘sigma_algebra a’ due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_NEGINF :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          ({x | f x = NegInf} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET]
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_NOT_POSINF :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          ({x | f x <> PosInf} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET]
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | f x < c} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     rw [SIGMA_ALGEBRA_EMPTY])
 >- (REWRITE_TAC [GSYM lt_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [])
 >> rfs [IN_MEASURABLE_BOREL]
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c. {x | f x < c} INTER space a IN subsets a
 *)
Theorem IN_MEASURABLE_BOREL_RO = IN_MEASURABLE_BOREL_IMP

(* NOTE: moved ‘sigma_algebra a’ to antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT1 :
    !f a. sigma_algebra a ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c. ({x | Normal c <= f x} INTER space a) IN subsets a)
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL, GSPECIFICATION, IN_FUNSET, IN_UNIV]
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
 >> METIS_TAC []
QED

(* NOTE: moved ‘sigma_algebra a’ to antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT2 :
    !f a. sigma_algebra a ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c. ({x | f x <= Normal c} INTER space a) IN subsets a)
Proof
    rpt STRIP_TAC
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
 >> EQ_TAC
 >- (RW_TAC std_ss [] \\
     `!c. {x | f x <= Normal c} INTER (space a) =
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
             >> `(\n. c + (1 / 2) pow n) = (\n. (\n. c) n + (\n. (1 / 2) pow n) n)`
                    by RW_TAC real_ss [FUN_EQ_THM]
             >> `(\n. (1 / 2) pow n) --> 0` by RW_TAC real_ss [SEQ_POWER]
             >> `(\n. c + (1 / 2) pow n) --> c`
                    by METIS_TAC [SEQ_CONST,
                         Q.SPECL [`(\n:num. c)`,`c`,`(\n. (1/2) pow n)`,`0`] SEQ_ADD,REAL_ADD_RID]
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
 >> RW_TAC std_ss []
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
 >> RW_TAC std_ss [IN_FUNSET]
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT2_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | f x <= c} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >- (REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >> rfs [IN_MEASURABLE_BOREL_ALT2]
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c. {x | f x <= c} INTER space a IN subsets a

   NOTE: "RC" ("C" is at right of "R") means a right-closed (C) half-interval (R).
 *)
Theorem IN_MEASURABLE_BOREL_RC = IN_MEASURABLE_BOREL_ALT2_IMP

(* NOTE: moved ‘sigma_algebra a’ to antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT3 :
    !f a. sigma_algebra a ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c. ({x | Normal c < f x} INTER space a) IN subsets a)
Proof
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_POSINF :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          ({x | f x = PosInf} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL_ALT3, GSPECIFICATION, IN_FUNSET]
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_NOT_NEGINF :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          ({x | f x <> NegInf} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL_ALT3, GSPECIFICATION, IN_FUNSET]
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT1_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | c <= f x} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [le_infty, GSPEC_T, INTER_UNIV] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_SPACE])
 >- (REWRITE_TAC [le_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >> rfs [IN_MEASURABLE_BOREL_ALT1]
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c. {x | c <= f x} INTER space a IN subsets a

   NOTE: "CR" ("C" is at left of "R") means a left-closed (C) half-interval (R).
 *)
Theorem IN_MEASURABLE_BOREL_CR = IN_MEASURABLE_BOREL_ALT1_IMP

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT3_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | c < f x} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> Cases_on `c`
 >- (REWRITE_TAC [GSYM lt_infty] \\
     MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [])
 >- (REWRITE_TAC [lt_infty, GSPEC_F, INTER_EMPTY] \\
     fs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
 >> rfs [IN_MEASURABLE_BOREL_ALT3]
QED

(*  |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c. {x | c < f x} INTER space a IN subsets a

   NOTE: "OR" ("O" is at left of "R") means a left-open (O) half-interval (R).
 *)
Theorem IN_MEASURABLE_BOREL_OR = IN_MEASURABLE_BOREL_ALT3_IMP

(* changed ‘!x. f x <> NegInf’ to ‘!x. x IN space a ==> f x <> NegInf’

   NOTE: moved ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’
 *)
Theorem IN_MEASURABLE_BOREL_ALT4 :
    !f a. sigma_algebra a /\ (!x. x IN space a ==> f x <> NegInf) ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c d. ({x | Normal c <= f x /\ f x < Normal d} INTER space a) IN subsets a)
Proof
    RW_TAC std_ss []
 >> EQ_TAC
 >- (rpt STRIP_TAC >- rfs [IN_MEASURABLE_BOREL] \\
    `{x | f x < Normal d} INTER space a IN subsets a`
        by METIS_TAC [IN_MEASURABLE_BOREL] \\
    `{x | Normal c <= f x} INTER space a IN subsets a`
        by METIS_TAC [IN_MEASURABLE_BOREL_ALT1] \\
     rfs [IN_MEASURABLE_BOREL] \\
    `(({x | Normal c <= f x} INTER space a) INTER
      ({x | f x < Normal d} INTER space a)) IN subsets a`
        by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER] \\
    `({x | Normal c <= f x} INTER space a) INTER ({x | f x < Normal d} INTER space a) =
     ({x | Normal c <= f x} INTER {x | f x < Normal d} INTER space a)`
        by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT] \\
    `{x | Normal c <= f x} INTER {x | f x < Normal d} = {x | Normal c <= f x /\ f x < Normal d}`
        by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
     METIS_TAC [SIGMA_ALGEBRA_INTER])
 >> RW_TAC std_ss [IN_MEASURABLE_BOREL]
 >> `!c. {x | f x < Normal c} INTER (space a) =
         BIGUNION
           (IMAGE (\n:num. {x | Normal (- &n) <= f x /\ f x < Normal c} INTER space a) UNIV)`
        by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER] \\
            EQ_TAC >- (RW_TAC std_ss [GSPECIFICATION] \\
                      `f x <> PosInf` by METIS_TAC [lt_infty] \\
                      `?r. f x = Normal r` by METIS_TAC [extreal_cases] \\
                       METIS_TAC [SIMP_REAL_ARCH_NEG, extreal_le_def]) \\
            RW_TAC std_ss [GSPECIFICATION] \\
            METIS_TAC [lt_infty])
 >> `BIGUNION
       (IMAGE (\n:num. {x | Normal (- &n) <= f x /\ f x < Normal c} INTER space a) UNIV)
         IN subsets a`
        by (RW_TAC std_ss [] \\
            MP_TAC (Q.SPEC `a` SIGMA_ALGEBRA_FN) \\
            RW_TAC std_ss [] \\
           `(\n. {x | Normal (- &n) <= f x /\ f x < Normal c} INTER space a) IN (UNIV -> subsets a)`
                by (RW_TAC std_ss [IN_FUNSET]) \\
           `{x | Normal (-&n) <= f x /\ f x < Normal c} INTER space a IN subsets a` by METIS_TAC [] \\
            METIS_TAC [])
 >> METIS_TAC []
QED

(* changed ‘!x. f x <> NegInf’ to ‘!x. x IN space a ==> f x <> NegInf’

   NOTE: moved ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’
 *)
Theorem IN_MEASURABLE_BOREL_ALT5 :
    !f a. sigma_algebra a /\ (!x. x IN space a ==> f x <> NegInf) ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c d. ({x | Normal c < f x /\ f x <= Normal d} INTER space a) IN subsets a)
Proof
    RW_TAC std_ss []
 >> EQ_TAC
 >- (rpt STRIP_TAC >- rfs [IN_MEASURABLE_BOREL]
     >> `{x | f x <= Normal d} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
     >> `{x | Normal c < f x} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
     >> rfs [IN_MEASURABLE_BOREL]
     >> `({x | Normal c < f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a) IN subsets a`
          by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
     >> `({x | Normal c < f x} INTER space a) INTER ({x | f x <=  Normal d} INTER space a) =
          {x | Normal c < f x} INTER {x | f x <= Normal d} INTER space a`
          by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
     >> `{x | Normal c < f x} INTER {x | f x <= Normal d} = {x | Normal c < f x /\ f x <= Normal d}`
          by RW_TAC std_ss [EXTENSION ,GSPECIFICATION, IN_INTER]
     >> METIS_TAC [SIGMA_ALGEBRA_INTER])
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
 >> `BIGUNION (IMAGE (\n:num. {x | Normal (- &n) < f x /\ f x <= Normal c} INTER space a) UNIV) IN subsets a`
     by (RW_TAC std_ss []
         >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
         >> RW_TAC std_ss []
         >> `(\n. {x | Normal (-&n) < f x /\ f x <= Normal c} INTER space a) IN (UNIV -> subsets a)`
            by FULL_SIMP_TAC real_ss [IN_FUNSET, GSPECIFICATION, IN_INTER]
         >> `{x | Normal (-&n) < f x /\ f x <= Normal c} INTER space a IN subsets a` by METIS_TAC []
         >> METIS_TAC [])
 >> METIS_TAC []
QED

(* changed ‘!x. f x <> NegInf’ to ‘!x. x IN space a ==> f x <> NegInf’

   NOTE: ‘sigma_algebra a’ is moved to antecedents due to changes of ‘measurable’
 *)
Theorem IN_MEASURABLE_BOREL_ALT6 :
    !f a. sigma_algebra a /\ (!x. x IN space a ==> f x <> NegInf) ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c d. ({x | Normal c <= f x /\ f x <= Normal d} INTER space a) IN subsets a)
Proof
     RW_TAC std_ss []
  >> EQ_TAC
  >- (rpt STRIP_TAC >- rfs [IN_MEASURABLE_BOREL]
      >> `{x | f x <= Normal d} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
      >> `{x | Normal c <= f x} INTER space a IN subsets a` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
      >> rfs [IN_MEASURABLE_BOREL]
      >> `({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a) IN subsets a`
         by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
      >> `({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a) =
          ({x | Normal c <= f x} INTER {x | f x <= Normal d} INTER space a)`
         by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
      >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
         by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
         by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
      >> METIS_TAC [SIGMA_ALGEBRA_INTER])
  >> RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT4]
  >> `!c. {x | Normal c <= f x /\ f x < Normal d} INTER (space a) =
          BIGUNION (IMAGE (\n:num. {x | Normal c <= f x /\
                                        f x <= Normal (d - (1/2) pow n)} INTER space a) UNIV)`
      by (RW_TAC std_ss [EXTENSION, IN_BIGUNION_IMAGE, IN_UNIV, IN_INTER, GSPECIFICATION]
          >> `(\n. c - (1 / 2) pow n) = (\n. (\n. c) n - (\n. (1 / 2) pow n) n)`
             by RW_TAC real_ss [FUN_EQ_THM]
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
               `!n. - ((1 / 2) pow n) < 0:real`
                 by METIS_TAC [REAL_POW_LT, REAL_NEG_0, REAL_LT_NEG, EVAL ``0:real < 1/2``]
               >> `!n. d - (1 / 2) pow n < d` by METIS_TAC [REAL_LT_IADD, REAL_ADD_RID, real_sub]
               >> `f x <> PosInf` by METIS_TAC [le_infty,extreal_not_infty]
               >> `?r. f x = Normal r` by METIS_TAC [extreal_cases]
               >> FULL_SIMP_TAC std_ss [extreal_le_def,extreal_lt_eq]
               >> METIS_TAC [REAL_LET_TRANS],
               METIS_TAC [] ])
  >> `BIGUNION (IMAGE (\n:num. {x | Normal c <= f x /\
                                    f x <= Normal (d - ((1 / 2) pow n))} INTER space a) UNIV)
        IN subsets a`
      by (RW_TAC std_ss []
          >> (MP_TAC o Q.SPEC `a`) SIGMA_ALGEBRA_FN
          >> RW_TAC std_ss []
          >> `(\n. {x | Normal c <= f x /\ f x <= Normal (d - ((1 / 2) pow n))} INTER space a)
                IN (UNIV -> subsets a)`
             by FULL_SIMP_TAC real_ss [IN_FUNSET, GSPECIFICATION, IN_INTER]
          >> `{x | Normal c <= f x /\ f x <= Normal (d - ((1/2) pow n))} INTER space a IN subsets a`
             by METIS_TAC []
          >> METIS_TAC [])
  >> METIS_TAC []
QED

(* changed ‘!x. f x <> NegInf’ to ‘!x. x IN space a ==> f x <> NegInf’

   NOTE: ‘sigma_algebra a’ is moved to antecedents due to changes of ‘measurable’
 *)
Theorem IN_MEASURABLE_BOREL_ALT7 :
    !f a. sigma_algebra a /\ (!x. x IN space a ==> f x <> NegInf) ==>
         (f IN measurable a Borel <=>
          f IN (space a -> UNIV) /\
          !c d. ({x | Normal c < f x /\ f x < Normal d } INTER space a) IN subsets a)
Proof
  RW_TAC std_ss []
  >> EQ_TAC
  >- (rpt STRIP_TAC >- rfs [IN_MEASURABLE_BOREL]
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
  >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_ALT4_IMP_r[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x | Normal c <= f x /\ f x < Normal d} INTER space a) IN subsets a
Proof
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
 >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_ALT4_IMP_p[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | Normal c <= f x /\ f x < PosInf} INTER space a) IN subsets a
Proof
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT4_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x | c <= f x /\ f x < d} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> Cases_on `c` >> Cases_on `d` (* 9 subgoals *)
 >- ((* goal 1 (of 9) *)
     REWRITE_TAC [lt_infty, le_infty, GSPEC_F, INTER_EMPTY] \\
     rfs [IN_MEASURABLE_BOREL, sigma_algebra_def, ALGEBRA_EMPTY])
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
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT4_IMP_r >> art []
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c d. {x | c <= f x /\ f x < d} INTER space a IN subsets a

   NOTE: "CO" means left-closed (C) and right-open (O) intervals.
 *)
Theorem IN_MEASURABLE_BOREL_CO = IN_MEASURABLE_BOREL_ALT4_IMP

Theorem IN_MEASURABLE_BOREL_ALT5_IMP_r[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x | Normal c < f x /\ f x <= Normal d} INTER space a) IN subsets a
Proof
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
 >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_ALT5_IMP_n[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !d. ({x | NegInf < f x /\ f x <= Normal d} INTER space a) IN subsets a
Proof
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT5_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x | c < f x /\ f x <= d} INTER space a) IN subsets a
Proof
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
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT5_IMP_r >> art []
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c d. {x | c < f x /\ f x <= d} INTER space a IN subsets a
 *)
Theorem IN_MEASURABLE_BOREL_OC = IN_MEASURABLE_BOREL_ALT5_IMP

Theorem IN_MEASURABLE_BOREL_ALT6_IMP_r[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x| Normal c <= f x /\ f x <= Normal d} INTER space a) IN subsets a
Proof
    RW_TAC std_ss [IN_FUNSET,IN_UNIV]
 >> `(!d. {x | f x <= Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT2]
 >> `(!c. {x | Normal c <= f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT1]
 >> rfs [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def,ALGEBRA_INTER]
 >> `!c d. (({x | Normal c <= f x} INTER space a) INTER ({x | f x <= Normal d} INTER space a)) =
           ({x | Normal c <= f x} INTER {x | f x <= Normal d} INTER space a)`
    by (RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER] >> METIS_TAC [])
 >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
    by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
 >> `{x | Normal c <= f x} INTER {x | f x <= Normal d} = {x | Normal c <= f x /\ f x <= Normal d}`
    by RW_TAC std_ss [EXTENSION,GSPECIFICATION,IN_INTER]
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT6_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x| c <= f x /\ f x <= d} INTER space a) IN subsets a
Proof
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
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT6_IMP_r >> art []
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c d. {x | c <= f x /\ f x <= d} INTER space a IN subsets a: thm
 *)
Theorem IN_MEASURABLE_BOREL_CC = IN_MEASURABLE_BOREL_ALT6_IMP

Theorem IN_MEASURABLE_BOREL_ALT7_IMP_r[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x | Normal c < f x /\ f x < Normal d} INTER space a) IN subsets a
Proof
    RW_TAC std_ss [IN_FUNSET, IN_UNIV]
 >> `(!d. {x | f x < Normal d} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL]
 >> `(!c. {x | Normal c < f x} INTER space a IN subsets a)` by METIS_TAC [IN_MEASURABLE_BOREL_ALT3]
 >> rfs [IN_MEASURABLE_BOREL]
 >> `!c d. (({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a)) IN subsets a`
    by METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
 >> `!c d. ({x | Normal c < f x} INTER space a) INTER ({x | f x < Normal d} INTER space a) =
           ({x | Normal c < f x} INTER {x | f x < Normal d} INTER space a)`
    by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> `{x | Normal c < f x} INTER {x | f x < Normal d} = {x | Normal c < f x /\ f x < Normal d}`
    by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
 >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_ALT7_IMP_np[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          ({x | NegInf < f x /\ f x < PosInf} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> rfs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
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
 >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_ALT7_IMP_n[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !d. ({x | NegInf < f x /\ f x < Normal d} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> rfs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
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
 >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_ALT7_IMP_p[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | Normal c < f x /\ f x < PosInf} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r
 >> rfs [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT7_IMP :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c d. ({x | c < f x /\ f x < d} INTER space a) IN subsets a
Proof
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
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ALT7_IMP_r >> art []
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c d. {x | c < f x /\ f x < d} INTER space a IN subsets a
 *)
Theorem IN_MEASURABLE_BOREL_OO = IN_MEASURABLE_BOREL_ALT7_IMP

Theorem IN_MEASURABLE_BOREL_ALT8_r[local] :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | f x = Normal c} INTER space a) IN subsets a
Proof
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
 >> METIS_TAC [IN_MEASURABLE_BOREL]
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT8 :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | f x = c} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> Cases_on `c` (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      RW_TAC std_ss [IN_MEASURABLE_BOREL] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [IN_MEASURABLE_BOREL],
      (* goal 2 (of 3) *)
      RW_TAC std_ss [IN_MEASURABLE_BOREL_ALT3] \\
      MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [IN_MEASURABLE_BOREL_ALT3],
      (* goal 3 (of 3) *)
      IMP_RES_TAC IN_MEASURABLE_BOREL_ALT8_r >> art [] ]
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c. {x | f x = c} INTER space a IN subsets a
 *)
Theorem IN_MEASURABLE_BOREL_SING = IN_MEASURABLE_BOREL_ALT8

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_ALT9 :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
          !c. ({x | f x <> c} INTER space a) IN subsets a
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC IN_MEASURABLE_BOREL_SING
 >> Know `!c. {x | f x <> c} INTER (space a) =
              space a DIFF ({x | f x = c} INTER space a)`
 >- (RW_TAC std_ss [EXTENSION, IN_UNIV, IN_DIFF, IN_INTER, GSPECIFICATION] \\
     EQ_TAC >- (rpt STRIP_TAC >> art []) \\
     METIS_TAC []) >> Rewr
 >> rfs [IN_MEASURABLE_BOREL]
 >> MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art []
QED

(* |- !f a.
        sigma_algebra a /\ f IN Borel_measurable a ==>
        !c. {x | f x <> c} INTER space a IN subsets a
 *)
Theorem IN_MEASURABLE_BOREL_NOT_SING = IN_MEASURABLE_BOREL_ALT9

(* All IMP versions of IN_MEASURABLE_BOREL_ALTs

   NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’
 *)
Theorem IN_MEASURABLE_BOREL_ALL :
    !f a.
        sigma_algebra a /\ f IN measurable a Borel ==>
        (!c. {x | f x < c} INTER space a IN subsets a) /\
        (!c. {x | c <= f x} INTER space a IN subsets a) /\
        (!c. {x | f x <= c} INTER space a IN subsets a) /\
        (!c. {x | c < f x} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x < d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x < d} INTER space a IN subsets a) /\
        (!c. {x | f x = c} INTER space a IN subsets a) /\
        (!c. {x | f x <> c} INTER space a IN subsets a)
Proof
    METIS_TAC [IN_MEASURABLE_BOREL_RO,         (* f x < c *)
               IN_MEASURABLE_BOREL_CR,         (* c <= f x *)
               IN_MEASURABLE_BOREL_RC,         (* f x <= c *)
               IN_MEASURABLE_BOREL_OR,         (* c < f x *)
               IN_MEASURABLE_BOREL_CO,         (* c <= f x /\ f x < d *)
               IN_MEASURABLE_BOREL_OC,         (* c < f x /\ f x <= d *)
               IN_MEASURABLE_BOREL_CC,         (* c <= f x /\ f x <= d *)
               IN_MEASURABLE_BOREL_OO,         (* c < f x /\ f x < d *)
               IN_MEASURABLE_BOREL_SING,       (* f x = c *)
               IN_MEASURABLE_BOREL_NOT_SING]   (* f x <> c *)
QED

(* |- !f m.
        sigma_algebra (measurable_space m) /\ f IN Borel_measurable (measurable_space m) ==>
        (!c. {x | f x < c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | c <= f x} INTER m_space m IN measurable_sets m) /\
        (!c. {x | f x <= c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | c < f x} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c <= f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c < f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c <= f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c < f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
        (!c. {x | f x = c} INTER m_space m IN measurable_sets m) /\
        !c. {x | f x <> c} INTER m_space m IN measurable_sets m: thm
 *)
Theorem IN_MEASURABLE_BOREL_ALL_MEASURE =
  ((Q.GENL [`f`, `m`]) o
   (REWRITE_RULE [space_def, subsets_def]) o
   (Q.SPECL [`f`, `(m_space m,measurable_sets m)`])) IN_MEASURABLE_BOREL_ALL

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_LT :
    !f g a. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel ==>
            ({x | f x < g x} INTER space a) IN subsets a
Proof
  RW_TAC std_ss []
  >> `{x | f x < g x} INTER space a =
      BIGUNION (IMAGE (\r. {x | f x < r /\ r < g x} INTER space a) Q_set)`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGUNION_IMAGE, IN_INTER]
            >> EQ_TAC
            >- RW_TAC std_ss [Q_DENSE_IN_R]
            >> METIS_TAC [lt_trans])
  >> POP_ORW
  >> MATCH_MP_TAC BIGUNION_IMAGE_Q >> art []
  >> RW_TAC std_ss [IN_FUNSET]
  >> `{x | f x < r /\ r < g x} INTER space a =
     ({x | f x < r} INTER space a) INTER ({x | r < g x} INTER space a)`
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
  >> POP_ORW
  >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
  >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]
QED

(* changed quantifier orders (was: f g a)

   NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’
 *)
Theorem IN_MEASURABLE_BOREL_LE :
    !a f g. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel ==>
            ({x | f x <= g x} INTER space a) IN subsets a
Proof
    RW_TAC std_ss []
 >> `{x | f x <= g x} INTER space a = space a DIFF ({x | g x < f x} INTER space a)`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER, IN_DIFF] \\
          METIS_TAC [extreal_lt_def])
 >> `{x | g x < f x} INTER space a IN subsets a` by RW_TAC std_ss [IN_MEASURABLE_BOREL_LT]
 >> METIS_TAC [algebra_def, IN_MEASURABLE_BOREL, sigma_algebra_def]
QED

Theorem IN_MEASURABLE_BOREL_EQ' :
    !a f g. (!x. x IN space a ==> (f x = g x)) /\
            g IN measurable a Borel ==> f IN measurable a Borel
Proof
    rw [measurable_def, IN_FUNSET]
 >> Know ‘PREIMAGE f s INTER space a = PREIMAGE g s INTER space a’
 >- (rw [Once EXTENSION, PREIMAGE_def] \\
     METIS_TAC [])
 >> Rewr'
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

(* changed quantifier orders (was: f g m) for applications in martingaleTheory *)
Theorem IN_MEASURABLE_BOREL_EQ :
    !m f g. (!x. x IN m_space m ==> (f x = g x)) /\
            g IN measurable (m_space m,measurable_sets m) Borel ==>
            f IN measurable (m_space m,measurable_sets m) Borel
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ'
 >> Q.EXISTS_TAC ‘g’ >> rw []
QED

(* cf. IN_MEASURABLE_CONG (sigma_algebraTheory) for a more general version *)
Theorem IN_MEASURABLE_BOREL_CONG :
    !m f g. (!x. x IN m_space m ==> (f x = g x)) ==>
            (f IN measurable (m_space m,measurable_sets m) Borel <=>
             g IN measurable (m_space m,measurable_sets m) Borel)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ \\
      Q.EXISTS_TAC ‘f’ >> rw [],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ \\
      Q.EXISTS_TAC ‘g’ >> rw [] ]
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

Theorem BOREL_MEASURABLE_SETS_SING[simp] : (* was: BOREL_MEASURABLE_SING *)
    !c. {c} IN subsets Borel
Proof
    GEN_TAC >> Cases_on `c`
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_NEGINF']
 >- REWRITE_TAC [BOREL_MEASURABLE_SETS_POSINF']
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_SING_r]
QED

Theorem BOREL_MEASURABLE_SETS_FINITE :
    !s. FINITE s ==> s IN subsets Borel
Proof
    HO_MATCH_MP_TAC FINITE_INDUCT
 >> rpt STRIP_TAC
 >- (MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL])
 >> ‘e INSERT s = {e} UNION s’ by SET_TAC []
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION
 >> rw [BOREL_MEASURABLE_SETS_SING, SIGMA_ALGEBRA_BOREL]
QED

Theorem BOREL_MEASURABLE_SETS_SING' :
    !c. {x | x = c} IN subsets Borel
Proof
    GEN_TAC
 >> `{x | x = c} = {c}` by RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_SING]
 >> POP_ORW
 >> REWRITE_TAC [BOREL_MEASURABLE_SETS_SING]
QED

Theorem BOREL_MEASURABLE_SETS_NOT_SING :
    !c. {x | x <> c} IN subsets Borel
Proof
    RW_TAC std_ss []
 >> `{x | x <> c} = (space Borel) DIFF ({c})`
      by RW_TAC std_ss [SPACE_BOREL, EXTENSION, IN_DIFF, IN_SING, GSPECIFICATION,
                        IN_UNIV]
 >> POP_ORW
 >> METIS_TAC [SIGMA_ALGEBRA_BOREL, BOREL_MEASURABLE_SETS_SING,
               sigma_algebra_def, algebra_def]
QED

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

(* NOTE: This is similar with Borel_eq_le but this generator contains exhausting
   sequences, which is needed when generating product sigma-algebras.
 *)
Theorem Borel_eq_le_ext :
    Borel = sigma univ(:extreal) (IMAGE (\c. {x | x <= c}) univ(:extreal))
Proof
    Suff ‘subsets Borel =
          subsets (sigma univ(:extreal) (IMAGE (\c. {x | x <= c}) univ(:extreal)))’
 >- METIS_TAC [SPACE, SPACE_BOREL, SPACE_SIGMA]
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> reverse CONJ_TAC
 >- (rw [GSYM SPACE_BOREL] \\
     MATCH_MP_TAC SIGMA_SUBSET \\
     rw [SPACE_BOREL, SIGMA_ALGEBRA_BOREL] \\
     rw [SUBSET_DEF] \\
     rw [BOREL_MEASURABLE_SETS_RC])
 >> rw [Borel_eq_le]
 >> MATCH_MP_TAC SIGMA_MONOTONE
 >> rw [SUBSET_DEF]
 >> Q.EXISTS_TAC ‘Normal a’ >> rw []
QED

(* ******************************************* *)
(*        Borel measurable functions           *)
(* ******************************************* *)

Theorem IN_MEASURABLE_BOREL_CONST :
    !a k f. sigma_algebra a /\ (!x. x IN space a ==> (f x = k)) ==>
            f IN measurable a Borel
Proof
    RW_TAC std_ss [IN_MEASURABLE_BOREL, IN_FUNSET, IN_UNIV]
 >> Cases_on `Normal c <= k`
 >- (`{x | f x < Normal c} INTER space a = {}`
         by  (RW_TAC std_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, IN_INTER]
              >> METIS_TAC [extreal_lt_def])
      >> METIS_TAC [sigma_algebra_def, algebra_def])
 >> `{x | f x < Normal c} INTER space a = space a`
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER]
          >> METIS_TAC [extreal_lt_def])
 >> METIS_TAC [sigma_algebra_def, algebra_def, INTER_IDEMPOT,DIFF_EMPTY]
QED

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

Theorem IN_MEASURABLE_BOREL_AINV :
    !a f. sigma_algebra a /\ f IN measurable a Borel ==> (\x. -f x) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MINUS
 >> Q.EXISTS_TAC ‘f’ >> rw []
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

(* A few theorems enhancing the existing IN_MEASURABLE_BOREL_ALL with ‘abs’ *)

Theorem IN_MEASURABLE_BOREL_ALL_ABS :
    !f a. sigma_algebra a /\ f IN measurable a Borel ==>
        (!c. {x | f x < c} INTER space a IN subsets a) /\
        (!c. {x | c <= f x} INTER space a IN subsets a) /\
        (!c. {x | f x <= c} INTER space a IN subsets a) /\
        (!c. {x | c < f x} INTER space a IN subsets a) /\
        (!c. {x | abs (f x) < c} INTER space a IN subsets a) /\
        (!c. {x | c <= abs (f x)} INTER space a IN subsets a) /\
        (!c. {x | abs (f x) <= c} INTER space a IN subsets a) /\
        (!c. {x | c < abs (f x)} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x < d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c <= f x /\ f x <= d} INTER space a IN subsets a) /\
        (!c d. {x | c < f x /\ f x < d} INTER space a IN subsets a) /\
        (!c. {x | f x = c} INTER space a IN subsets a) /\
        (!c. {x | f x <> c} INTER space a IN subsets a) /\
        (!c. {x | abs (f x) = c} INTER space a IN subsets a) /\
        (!c. {x | abs (f x) <> c} INTER space a IN subsets a)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Q.ABBREV_TAC ‘g = \x. abs (f x)’ >> simp []
 >> Know ‘g IN measurable a Borel’
 >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS \\
     Q.EXISTS_TAC ‘f’ >> rw [Abbr ‘g’])
 >> DISCH_TAC
 >> rw [IN_MEASURABLE_BOREL_ALL]
QED

Theorem IN_MEASURABLE_BOREL_ALL_MEASURE_ABS :
   !m f. measure_space m /\ f IN Borel_measurable (measurable_space m) ==>
        (!c. {x | f x < c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | c <= f x} INTER m_space m IN measurable_sets m) /\
        (!c. {x | f x <= c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | c < f x} INTER m_space m IN measurable_sets m) /\
        (!c. {x | abs (f x) < c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | c <= abs (f x)} INTER m_space m IN measurable_sets m) /\
        (!c. {x | abs (f x) <= c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | c < abs (f x)} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c <= f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c < f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c <= f x /\ f x <= d} INTER m_space m IN measurable_sets m) /\
        (!c d. {x | c < f x /\ f x < d} INTER m_space m IN measurable_sets m) /\
        (!c. {x | f x = c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | f x <> c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | abs (f x) = c} INTER m_space m IN measurable_sets m) /\
        (!c. {x | abs (f x) <> c} INTER m_space m IN measurable_sets m)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> MP_TAC (REWRITE_RULE [space_def, subsets_def]
             (Q.SPECL [‘f’, ‘measurable_space m’] IN_MEASURABLE_BOREL_ALL_ABS))
 >> FULL_SIMP_TAC std_ss [measure_space_def]
QED

Theorem IN_MEASURABLE_BOREL_ALL_MEASURE_ABS' :
   !m f. measure_space m /\ f IN Borel_measurable (measurable_space m) ==>
        (!c. {x | x IN m_space m /\ f x < c} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ c <= f x} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ f x <= c} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ c < f x} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ abs (f x) < c} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ c <= abs (f x)} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ abs (f x) <= c} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ c < abs (f x)} IN measurable_sets m) /\
        (!c d. {x | x IN m_space m /\ c <= f x /\ f x < d} IN measurable_sets m) /\
        (!c d. {x | x IN m_space m /\ c < f x /\ f x <= d} IN measurable_sets m) /\
        (!c d. {x | x IN m_space m /\ c <= f x /\ f x <= d} IN measurable_sets m) /\
        (!c d. {x | x IN m_space m /\ c < f x /\ f x < d} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ f x = c} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ f x <> c} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ abs (f x) = c} IN measurable_sets m) /\
        (!c. {x | x IN m_space m /\ abs (f x) <> c} IN measurable_sets m)
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> ‘!P. {x | x IN m_space m /\ P x} = {x | P x} INTER m_space m’ by SET_TAC []
 >> simp []
 >> MP_TAC (Q.SPECL [‘m’, ‘f’] IN_MEASURABLE_BOREL_ALL_MEASURE_ABS)
 >> rw []
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

Theorem IN_MEASURABLE_BOREL_MUL_INDICATOR :
    !a f s. sigma_algebra a /\ f IN measurable a Borel /\ s IN subsets a ==>
            (\x. f x * indicator_fn s x) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL_ALT2, IN_FUNSET]
 >> Q.X_GEN_TAC ‘c’
 >> Cases_on `0 <= Normal c`
 >- (`{x | f x * indicator_fn s x <= Normal c} INTER space a =
      (({x | f x <= Normal c} INTER space a) INTER s) UNION (space a DIFF s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER,
                            IN_UNION, IN_DIFF] \\
             Cases_on `x IN s` >- RW_TAC std_ss [mul_rone, mul_rzero] \\
             RW_TAC std_ss [mul_rone, mul_rzero]) >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
     CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_COMPL >> art [])
 >> `{x | f x * indicator_fn s x <= Normal c} INTER space a =
     (({x | f x <= Normal c} INTER space a) INTER s)`
         by (RW_TAC std_ss [indicator_fn_def, EXTENSION, GSPECIFICATION, IN_INTER] \\
             Cases_on `x IN s` >- RW_TAC std_ss [mul_rone, mul_rzero] \\
             RW_TAC std_ss [mul_rone, mul_rzero]) >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
QED

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

Theorem IN_MEASURABLE_BOREL_MAX :
    !a f g. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel
        ==> (\x. max (f x) (g x)) IN measurable a Borel
Proof
    RW_TAC std_ss [extreal_max_def]
 >> rfs [IN_MEASURABLE_BOREL, IN_FUNSET]
 >> `!c. {x | (if f x <= g x then g x else f x) < c} = {x | f x < c} INTER {x | g x < c}`
        by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] \\
            EQ_TAC
            >- (RW_TAC std_ss [] >- METIS_TAC [let_trans] \\
                METIS_TAC [extreal_lt_def, lt_trans]) \\
            METIS_TAC [extreal_lt_def, lt_trans])
 >> `!c. {x | (if f x <= g x then g x else f x) < c} INTER space a =
         ({x | f x < c} INTER space a) INTER ({x | g x < c} INTER space a)`
        by METIS_TAC [INTER_ASSOC, INTER_COMM, INTER_IDEMPOT]
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_INTER]
QED

Theorem IN_MEASURABLE_BOREL_MIN :
    !a f g. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel
        ==> (\x. min (f x) (g x)) IN measurable a Borel
Proof
    RW_TAC std_ss [extreal_min_def]
 >> rfs [IN_MEASURABLE_BOREL, IN_FUNSET]
 >> Know `!c. {x | (if f x <= g x then f x else g x) < c} =
              {x | f x < c} UNION {x | g x < c}`
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION] \\
     EQ_TAC >- RW_TAC std_ss [] \\
     RW_TAC std_ss [] >- METIS_TAC [let_trans] \\
     METIS_TAC [extreal_lt_def, lt_trans]) >> DISCH_TAC
 >> `!c. {x | (if f x <= g x then f x else g x) < c} INTER space a =
         ({x | f x < c} INTER space a) UNION ({x | g x < c} INTER space a)`
       by ASM_SET_TAC []
 >> METIS_TAC [sigma_algebra_def, ALGEBRA_UNION]
QED

(* see extrealTheory.max_fn_seq_def *)
Theorem IN_MEASURABLE_BOREL_MAX_FN_SEQ :
    !a f. sigma_algebra a /\ (!i. f i IN measurable a Borel) ==>
          !n. max_fn_seq f n IN measurable a Borel
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> Induct_on ‘n’ >> rw [max_fn_seq_def]
 >> ‘max_fn_seq f (SUC n) = \x. max (max_fn_seq f n x) (f (SUC n) x)’
      by rw [max_fn_seq_def, FUN_EQ_THM]
 >> POP_ORW
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_MAX >> rw []
QED

(* TODO: ‘!n x. x IN space a ==> fn n x <= fn (SUC n) x’ (MONO) is unnecessary *)
Theorem IN_MEASURABLE_BOREL_MONO_SUP :
    !fi f a. sigma_algebra a /\ (!n:num. fi n IN measurable a Borel) /\
            (!n x. x IN space a ==> fi n x <= fi (SUC n) x) /\
            (!x. x IN space a ==> (f x = sup (IMAGE (\n. fi n x) UNIV)))
         ==> f IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL_ALT2, IN_FUNSET]
 >> Q.X_GEN_TAC ‘c’
 >> Know ‘{x | sup (IMAGE (\n. fi n x) UNIV) <= Normal c} INTER space a =
           BIGINTER (IMAGE (\n. {x | fi n x <= Normal c} INTER space a) UNIV)’
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER, sup_le'] \\
     EQ_TAC
     >- (RW_TAC std_ss [] \\
         Q.PAT_X_ASSUM `!y. P y ==> y <= Normal c` MATCH_MP_TAC \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         METIS_TAC []) \\
     RW_TAC std_ss [] \\
     POP_ASSUM MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘{x | f x <= Normal c} INTER space a =
     {x | sup (IMAGE (\n. fi n x) UNIV) <= Normal c} INTER space a’
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> ‘!c. BIGINTER (IMAGE (\n. {x | fi n x <= Normal c} INTER (space a)) UNIV) IN subsets a’
      by (RW_TAC std_ss [] \\
          (MP_TAC o Q.SPEC `(space a,subsets a)`) SIGMA_ALGEBRA_FN_BIGINTER \\
          RW_TAC std_ss [IN_FUNSET, IN_UNIV, space_def, subsets_def, SPACE])
 >> METIS_TAC []
QED

(* Here univ(:num) is replaced by a subset X *)
Theorem IN_MEASURABLE_BOREL_SUP :
    !a fi f X. sigma_algebra a /\ X <> {} /\
              (!n:num. n IN X ==> fi n IN measurable a Borel) /\
              (!x. x IN space a ==> (f x = sup (IMAGE (\n. fi n x) X)))
           ==> f IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL_ALT2, IN_FUNSET]
 >> Q.X_GEN_TAC ‘c’
 >> Know ‘{x | sup (IMAGE (\n. fi n x) X) <= Normal c} INTER space a =
           BIGINTER (IMAGE (\n. {x | fi n x <= Normal c} INTER space a) X)’
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER, sup_le'] \\
     EQ_TAC
     >- (RW_TAC std_ss [] \\
         Q.PAT_X_ASSUM `!y. P y ==> y <= Normal c` MATCH_MP_TAC \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         Q.EXISTS_TAC ‘n’ >> art []) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       POP_ASSUM MP_TAC \\
       RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
       METIS_TAC [],
       (* goal 2 (of 2) *)
      ‘?i. i IN X’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
       METIS_TAC [] ])
 >> DISCH_TAC
 >> ‘{x | f x <= Normal c} INTER space a =
     {x | sup (IMAGE (\n. fi n x) X) <= Normal c} INTER space a’
      by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> NTAC 2 POP_ORW
 >> Q.ABBREV_TAC ‘A = \n. {x | fi n x <= Normal c} INTER space a’
 >> ‘IMAGE A X = {A i | i IN X}’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC (Q.SPECL [‘space a’, ‘subsets a’] SIGMA_ALGEBRA_COUNTABLE_INT)
 >> rw [IN_FUNSET, space_def, subsets_def, SPACE, SUBSET_DEF, Abbr ‘A’]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem IN_MEASURABLE_BOREL_MONO_INF :
    !fi f a. sigma_algebra a /\ (!n:num. fi n IN measurable a Borel) /\
            (!x. x IN space a ==> (f x = inf (IMAGE (\n. fi n x) UNIV)))
         ==> f IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL_ALT1, IN_FUNSET]
 >> Q.X_GEN_TAC ‘c’
 >> Know ‘{x | Normal c <= inf (IMAGE (\n. fi n x) UNIV)} INTER space a =
           BIGINTER (IMAGE (\n. {x | Normal c <= fi n x} INTER space a) UNIV)’
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER, le_inf'] \\
     EQ_TAC
     >- (RW_TAC std_ss [] \\
         Q.PAT_X_ASSUM ‘!y. P y ==> Normal c <= y’ MATCH_MP_TAC \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         METIS_TAC []) \\
     RW_TAC std_ss [] \\
     POP_ASSUM MP_TAC \\
     RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     METIS_TAC [])
 >> DISCH_TAC
 >> ‘{x | Normal c <= f x} INTER space a =
     {x | Normal c <= inf (IMAGE (\n. fi n x) UNIV)} INTER space a’
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> ‘!c. BIGINTER (IMAGE (\n. {x | Normal c <= fi n x} INTER (space a)) UNIV) IN subsets a’
       by (RW_TAC std_ss [] \\
           (MP_TAC o Q.SPEC `(space a,subsets a)`) SIGMA_ALGEBRA_FN_BIGINTER \\
           RW_TAC std_ss [IN_FUNSET, IN_UNIV, space_def, subsets_def, SPACE])
 >> METIS_TAC []
QED

Theorem IN_MEASURABLE_BOREL_INF :
    !a fi f X. sigma_algebra a /\ X <> {} /\
              (!n:num. n IN X ==> fi n IN measurable a Borel) /\
              (!x. x IN space a ==> (f x = inf (IMAGE (\n. fi n x) X)))
           ==> f IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL_ALT1, IN_FUNSET]
 >> Q.X_GEN_TAC ‘c’
 >> Know ‘{x | Normal c <= inf (IMAGE (\n. fi n x) X)} INTER space a =
           BIGINTER (IMAGE (\n. {x | Normal c <= fi n x} INTER space a) X)’
 >- (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_BIGINTER_IMAGE, IN_UNIV, IN_INTER, le_inf'] \\
     EQ_TAC
     >- (RW_TAC std_ss [] \\
         Q.PAT_X_ASSUM ‘!y. P y ==> Normal c <= y’ MATCH_MP_TAC \\
         RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
         Q.EXISTS_TAC ‘n’ >> art []) \\
     RW_TAC std_ss [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       POP_ASSUM MP_TAC \\
       RW_TAC std_ss [IN_IMAGE, IN_UNIV] \\
       METIS_TAC [],
       (* goal 2 (of 2) *)
      ‘?i. i IN X’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
       METIS_TAC [] ])
 >> DISCH_TAC
 >> ‘{x | Normal c <= f x} INTER space a =
     {x | Normal c <= inf (IMAGE (\n. fi n x) X)} INTER space a’
       by (RW_TAC std_ss [EXTENSION, GSPECIFICATION, IN_INTER] >> METIS_TAC [])
 >> NTAC 2 POP_ORW
 >> Q.ABBREV_TAC ‘A = \n. {x | Normal c <= fi n x} INTER space a’
 >> ‘IMAGE A X = {A i | i IN X}’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC (Q.SPECL [‘space a’, ‘subsets a’] SIGMA_ALGEBRA_COUNTABLE_INT)
 >> rw [IN_FUNSET, space_def, subsets_def, SPACE, SUBSET_DEF, Abbr ‘A’]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

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

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_FN_PLUS :
    !a f. sigma_algebra a /\ f IN measurable a Borel ==> fn_plus f IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> rfs [IN_MEASURABLE_BOREL, IN_FUNSET, fn_plus_def]
 >> Q.X_GEN_TAC ‘c’
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
 >> METIS_TAC []
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’ *)
Theorem IN_MEASURABLE_BOREL_FN_MINUS :
    !a f. sigma_algebra a /\ f IN measurable a Borel ==> fn_minus f IN measurable a Borel
Proof
    RW_TAC std_ss [fn_minus_def]
 >> rw [IN_MEASURABLE_BOREL, IN_FUNSET]
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
 >> METIS_TAC [IN_MEASURABLE_BOREL_ALL]
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’

   This theorem is used in martingaleTheory.FUBINI.
 *)
Theorem IN_MEASURABLE_BOREL_PLUS_MINUS :
    !a f. sigma_algebra a ==>
         (f IN measurable a Borel <=>
          fn_plus f IN measurable a Borel /\ fn_minus f IN measurable a Borel)
Proof
    rpt STRIP_TAC
 >> EQ_TAC
 >- RW_TAC std_ss [IN_MEASURABLE_BOREL_FN_PLUS, IN_MEASURABLE_BOREL_FN_MINUS]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_SUB
 >> qexistsl_tac [`fn_plus f`, `fn_minus f`]
 >> RW_TAC std_ss [fn_plus_def, fn_minus_def, sub_rzero, lt_antisym, sub_rzero, add_lzero]
 >| [ (* goal 2 (of 8) *)
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

(* The reverse version of IN_MEASURABLE_BOREL_IMP_BOREL

   NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’
 *)
Theorem in_borel_measurable_from_Borel :
    !a f. sigma_algebra a /\ f IN measurable a Borel ==> (real o f) IN measurable a borel
Proof
    rpt GEN_TAC >> STRIP_TAC
 >> simp [IN_MEASURABLE, sigma_algebra_borel, IN_FUNSET, space_borel]
 >> Q.X_GEN_TAC ‘B’ >> STRIP_TAC
 >> rw [PREIMAGE_def]
 >> Know ‘{x | real (f x) IN B} INTER space a =
          if 0 IN B then
            ({x | f x IN (IMAGE Normal B)} INTER space a) UNION
            ({x | f x = PosInf} INTER space a) UNION
            ({x | f x = NegInf} INTER space a)
          else
            ({x | f x IN (IMAGE Normal B)} INTER space a)’
 >- (Cases_on ‘0 IN B’ >> rw [Once EXTENSION] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       EQ_TAC >> rw [] >> rw [real_def] \\
       Cases_on ‘f x’ >> fs [real_normal],
       (* goal 2 (of 2) *)
       EQ_TAC >> rw [] >> rw [real_def] \\
       Q.EXISTS_TAC ‘real (f x)’ >> art [] \\
       ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
       MATCH_MP_TAC normal_real \\
       CONJ_TAC >> CCONTR_TAC >> fs [real_def] ])
 >> Rewr'
 >> Cases_on ‘0 IN B’ >> ASM_SIMP_TAC std_ss []
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
      reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art []) \\
      MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
      reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art []) \\
      REWRITE_TAC [GSYM PREIMAGE_def] \\
      FULL_SIMP_TAC std_ss [Borel, IN_MEASURABLE, SPACE_BOREL, IN_FUNSET,
                            SIGMA_ALGEBRA_BOREL, IN_UNIV, subsets_def, GSPECIFICATION] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      qexistsl_tac [‘B’, ‘{}’] >> rw [],
      (* goal 2 (of 2) *)
      REWRITE_TAC [GSYM PREIMAGE_def] \\
      FULL_SIMP_TAC std_ss [Borel, IN_MEASURABLE, SPACE_BOREL, IN_FUNSET,
                            SIGMA_ALGEBRA_BOREL, IN_UNIV, subsets_def, GSPECIFICATION] \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      qexistsl_tac [‘B’, ‘{}’] >> rw [] ]
QED

Theorem IN_MEASURABLE_BOREL_IMP_BOREL : (* was: borel_IMP_Borel *)
    !f m. f IN measurable (m_space m,measurable_sets m) borel ==>
          (Normal o f) IN measurable (m_space m,measurable_sets m) Borel
Proof
    RW_TAC std_ss [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, o_DEF]
 >- (EVAL_TAC >> SRW_TAC[] [IN_DEF, IN_FUNSET])
 >> FULL_SIMP_TAC std_ss [space_def, subsets_def]
 >> Know ‘PREIMAGE (\x. Normal (f x)) s = PREIMAGE f (real_set s)’
 >- (SIMP_TAC std_ss [PREIMAGE_def, EXTENSION, GSPECIFICATION] \\
     RW_TAC std_ss [real_set_def, GSPECIFICATION] \\
     EQ_TAC >> RW_TAC std_ss []
     >- (Q.EXISTS_TAC `Normal (f x)` \\
         ASM_SIMP_TAC std_ss [extreal_not_infty, real_normal]) \\
     ASM_SIMP_TAC std_ss [normal_real])
 >> DISCH_TAC
 >> FULL_SIMP_TAC std_ss []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> UNDISCH_TAC ``s IN subsets Borel``
 >> FULL_SIMP_TAC std_ss [borel_eq_less, Borel_def]
 >> RW_TAC std_ss [subsets_def, sigma_def, IN_BIGINTER, GSPECIFICATION, SUBSET_DEF]
 >> FIRST_X_ASSUM (MP_TAC o Q.SPEC `{s | real_set s IN P}`)
 >> RW_TAC std_ss [IN_IMAGE, IN_UNIV, GSPECIFICATION]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> CONJ_TAC
 >- (RW_TAC std_ss [real_set_def] >> SIMP_TAC std_ss [GSPECIFICATION] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     SIMP_TAC std_ss [IN_IMAGE, IN_UNIV] \\
     SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] >> Q.EXISTS_TAC `a` \\
     GEN_TAC >> EQ_TAC >> RW_TAC std_ss []
     >- (ONCE_REWRITE_TAC [GSYM extreal_lt_eq] \\
         ASM_SIMP_TAC std_ss [normal_real]) \\
     Q.EXISTS_TAC `Normal x` \\
     ASM_SIMP_TAC std_ss [extreal_lt_eq, extreal_not_infty, real_normal])
 >> POP_ASSUM MP_TAC
 (* sigma_algebra (UNIV,P) ==> sigma_algebra (UNIV,{s | real_set s IN P}) *)
 >> RW_TAC std_ss [sigma_algebra_alt_pow]
 >| [ (* goal 1 (of 4) *)
      SIMP_TAC std_ss [SUBSET_DEF, IN_POW, IN_UNIV],
      (* goal 2 (of 4) *)
      SIMP_TAC std_ss [GSPECIFICATION, real_set_def, NOT_IN_EMPTY] \\
      ASM_SIMP_TAC std_ss [SET_RULE ``{real x | F} = {}``],
      (* goal 3 (of 4) *)
      POP_ASSUM MP_TAC >> SIMP_TAC std_ss [GSPECIFICATION] >> DISCH_TAC \\
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `real_set s'`) >> ASM_REWRITE_TAC [] \\
      SIMP_TAC std_ss [real_set_def, GSPECIFICATION, IN_DIFF, IN_UNIV] \\
      SIMP_TAC std_ss [DIFF_DEF, IN_UNIV, GSPECIFICATION] \\
      MATCH_MP_TAC EQ_IMPLIES >> AP_THM_TAC >> AP_TERM_TAC \\
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION] \\
      GEN_TAC >> EQ_TAC
      >- (RW_TAC std_ss [] >> Q.EXISTS_TAC `Normal x` \\
          POP_ASSUM (MP_TAC o Q.SPEC `Normal x`) \\
          SIMP_TAC std_ss [real_normal, extreal_not_infty]) \\
      RW_TAC std_ss [] >> ASM_CASES_TAC ``real x' <> real x''`` \\
      ASM_REWRITE_TAC [] \\
      ASM_CASES_TAC ``x'' = PosInf`` >> ASM_REWRITE_TAC [] \\
      ASM_CASES_TAC ``x'' = NegInf`` >> ASM_REWRITE_TAC [] \\
      FULL_SIMP_TAC std_ss [] >> UNDISCH_TAC ``real x' = real x''`` \\
      ONCE_REWRITE_TAC [GSYM extreal_11] >> FULL_SIMP_TAC std_ss [normal_real] \\
      METIS_TAC [],
      (* goal 4 (of 4) *)
      SIMP_TAC std_ss [GSPECIFICATION] \\
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `(\i. real_set (A i))`) \\
      Suff `real_set (BIGUNION {A i | i IN univ(:num)}) =
            BIGUNION {(\i. real_set (A i)) i | i IN univ(:num)}`
      >- (Rewr' >> DISCH_THEN (MATCH_MP_TAC) >> POP_ASSUM MP_TAC \\
          RW_TAC std_ss [SUBSET_DEF, IN_IMAGE, IN_UNIV, GSPECIFICATION] \\
          FIRST_X_ASSUM MATCH_MP_TAC >> METIS_TAC []) \\
      SIMP_TAC std_ss [real_set_def, EXTENSION, GSPECIFICATION, IN_BIGUNION] \\
      GEN_TAC >> EQ_TAC >> RW_TAC std_ss []
      >- (Q.EXISTS_TAC `real_set s'` \\
          CONJ_TAC
          >- (SIMP_TAC std_ss [real_set_def, GSPECIFICATION] >> METIS_TAC []) \\
          SIMP_TAC std_ss [IN_UNIV] \\
          Q.EXISTS_TAC `i` >> GEN_TAC \\
          SIMP_TAC std_ss [real_set_def, GSPECIFICATION] \\
          METIS_TAC []) \\
      UNDISCH_TAC ``(x:real) IN s'`` >> ASM_REWRITE_TAC [] \\
      RW_TAC std_ss [] >> Q.EXISTS_TAC `x'` \\
      ASM_REWRITE_TAC [IN_UNIV] >> Q.EXISTS_TAC `A i` \\
      METIS_TAC [] ]
QED

Theorem IN_MEASURABLE_BOREL_IMP_BOREL' :
    !a f. sigma_algebra a /\ f IN measurable a borel ==> (Normal o f) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘f’, ‘(space a,subsets a,(\s. 0))’] IN_MEASURABLE_BOREL_IMP_BOREL)
 >> Know ‘sigma_finite_measure_space (space a,subsets a,(\s. 0))’
 >- (MATCH_MP_TAC measure_space_trivial >> art [])
 >> rw [sigma_finite_measure_space_def]
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

Theorem in_borel_measurable_imp : (* was: borel_measurableI *)
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

(* ------------------------------------------------------------------------- *)
(*  Construction of Borel measure space by CARATHEODORY_SEMIRING             *)
(* ------------------------------------------------------------------------- *)

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

Overload lborel0 =
        “(space right_open_intervals,subsets right_open_intervals,lambda0)”

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
 (* Below are new proofs based on TOPOLOGICAL_SORT' *)
 >> Q.ABBREV_TAC ‘filtered = {i | i < n /\ f i <> {}}’
 >> ‘filtered SUBSET (count n)’ by rw [Abbr ‘filtered’, SUBSET_DEF]
 >> Know ‘FINITE filtered’
 >- (MATCH_MP_TAC SUBSET_FINITE_I \\
     Q.EXISTS_TAC ‘count n’ >> rw [IMAGE_FINITE])
 >> DISCH_TAC
 >> Q.ABBREV_TAC ‘N = CARD filtered’
 >> Know ‘0 < N /\ N <= n’
 >- (rw [Abbr ‘N’, GSYM NOT_ZERO_LT_ZERO, CARD_EQ_0, GSYM MEMBER_NOT_EMPTY] >|
     [ (* goal 1 (of 2) *)
       rw [Abbr ‘filtered’] \\
       Q.EXISTS_TAC ‘k’ >> rw [MEMBER_NOT_EMPTY],
       (* goal 2 (of 2) *)
      ‘n = CARD (count n)’ by PROVE_TAC [CARD_COUNT] >> POP_ORW \\
       irule CARD_SUBSET >> rw [] ])
 >> STRIP_TAC
 >> Q.PAT_X_ASSUM ‘k < n’     K_TAC
 >> Q.PAT_X_ASSUM ‘f k <> {}’ K_TAC
 >> ‘filtered HAS_SIZE N’ by PROVE_TAC [HAS_SIZE]
 (* preparing for TOPOLOGICAL_SORT' (on ‘filtered’) *)
 >> Q.ABBREV_TAC ‘R = \i j. i < n /\ j < n /\ f i <> {} /\ f j <> {} /\
                            interval_lowerbound (f i) <= interval_lowerbound (f j)’
 >> Know ‘transitive R /\ antisymmetric R’
 >- (rw [Abbr ‘R’, transitive_def, antisymmetric_def] >- PROVE_TAC [REAL_LE_TRANS] \\
    ‘interval_lowerbound (f i) = interval_lowerbound (f j)’ by PROVE_TAC [REAL_LE_ANTISYM] \\
    ‘?a1 b1. a1 < b1 /\ f i = right_open_interval a1 b1’
        by METIS_TAC [in_right_open_intervals_nonempty] \\
    ‘?a2 b2. a2 < b2 /\ f j = right_open_interval a2 b2’
        by METIS_TAC [in_right_open_intervals_nonempty] \\
     FULL_SIMP_TAC std_ss [right_open_interval_lowerbound] \\
     CCONTR_TAC \\
     Q.PAT_X_ASSUM ‘!i j. _ ==> DISJOINT (f i) (f j)’ (MP_TAC o (Q.SPECL [‘i’, ‘j’])) \\
     simp [DISJOINT_ALT] \\
    ‘a2 < min b1 b2’ by PROVE_TAC [REAL_LT_MIN] \\
    ‘?z. a2 < z /\ z < min b1 b2’ by METIS_TAC [REAL_MEAN] \\
     FULL_SIMP_TAC std_ss [REAL_LT_MIN] \\
     Q.EXISTS_TAC ‘z’ >> rw [in_right_open_interval, REAL_LT_IMP_LE])
 >> STRIP_TAC
 (* applying TOPOLOGICAL_SORT' *)
 >> drule_all TOPOLOGICAL_SORT'
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘g’ STRIP_ASSUME_TAC) (* this asserts ‘g’ *)
 >> Know ‘!i. i < N ==> g i < n /\ f (g i) <> {}’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘filtered = IMAGE g (count N)’ MP_TAC \\
     rw [Once EXTENSION, Abbr ‘filtered’] >> METIS_TAC [])
 >> DISCH_TAC
 >> Know ‘!i j. i < N /\ j < N /\ i < j ==>
                interval_lowerbound (f (g i)) < interval_lowerbound (f (g j))’
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘!j k. _ ==> ~R (g k) (g j)’ (MP_TAC o (Q.SPECL [‘i’, ‘j’])) \\
     rw [Abbr ‘R’, GSYM real_lt])
 >> DISCH_TAC
 >> Know ‘!i j. i < N /\ j < N /\ i <> j ==> g i <> g j’
 >- (rpt STRIP_TAC \\
    ‘i < j \/ j < i’ by rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Q.PAT_X_ASSUM ‘!i j. _ ==> interval_lowerbound (f (g i)) < interval_lowerbound (f (g j))’
         (MP_TAC o (Q.SPECL [‘i’, ‘j’])) >> rw [],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘!i j. _ ==> interval_lowerbound (f (g i)) < interval_lowerbound (f (g j))’
         (MP_TAC o (Q.SPECL [‘j’, ‘i’])) >> rw [] ])
 >> DISCH_TAC
 (* eliminate ‘R’ *)
 >> Q.PAT_X_ASSUM ‘!j k. _ ==> ~R (g k) (g j)’ K_TAC (* superseded *)
 >> Q.PAT_X_ASSUM ‘transitive R’        K_TAC
 >> Q.PAT_X_ASSUM ‘antisymmetric R’     K_TAC
 >> Q.PAT_X_ASSUM ‘filtered HAS_SIZE N’ K_TAC
 >> Q.UNABBREV_TAC ‘R’
 (* define h = f o g *)
 >> Q.ABBREV_TAC ‘h = f o g’
 (* LHS rewriting *)
 >> Know ‘BIGUNION (IMAGE f (count n)) = BIGUNION (IMAGE h (count N))’
 >- (Q.PAT_X_ASSUM ‘filtered = IMAGE g (count N)’ MP_TAC \\
     rw [Abbr ‘filtered’, Once EXTENSION] \\
     rw [Once EXTENSION, IN_BIGUNION_IMAGE, Abbr ‘h’] \\
     EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 ‘i < n’ >> ‘f i <> {}’ by METIS_TAC [MEMBER_NOT_EMPTY] \\
      ‘?j. i = g j /\ j < N’ by METIS_TAC [] \\
       Q.EXISTS_TAC ‘j’ >> rw [],
       (* goal 2 (of 2) *)
       rename1 ‘i < N’ >> Q.EXISTS_TAC ‘g i’ >> rw [] ])
 >> DISCH_THEN (REV_FULL_SIMP_TAC std_ss o wrap)
 (* RHS rewriting *)
 >> Know ‘SIGMA (lambda0 o f) (count n) = SIGMA (lambda0 o f) filtered’
 >- (Q.ABBREV_TAC ‘empties = {i | i < n /\ f i = {}}’ \\
     Know ‘filtered = (count n) DIFF empties’
     >- (qunabbrevl_tac [‘empties’, ‘filtered’] \\
         rw [Once EXTENSION] >> METIS_TAC []) >> Rewr' \\
     irule EXTREAL_SUM_IMAGE_ZERO_DIFF \\
     rw [Abbr ‘empties’, o_DEF, lambda0_empty] \\
     DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> DISCH_TAC \\
    ‘?a1 b1. f i = right_open_interval a1 b1’
        by METIS_TAC [in_right_open_intervals] >> POP_ORW \\
     PROVE_TAC [lambda0_not_infty])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘filtered = IMAGE g (count N)’ (REWRITE_TAC o wrap)
 >> Know ‘SIGMA (lambda0 o f) (IMAGE g (count N)) =
          SIGMA ((lambda0 o f) o g) (count N)’
 >- (irule EXTREAL_SUM_IMAGE_IMAGE >> simp [o_DEF] \\
     reverse CONJ_TAC >- (rw [INJ_DEF] >> METIS_TAC []) \\
     DISJ1_TAC >> Q.X_GEN_TAC ‘i’ >> STRIP_TAC >> rename1 ‘i = g j’ \\
    ‘?a1 b1. f i = right_open_interval a1 b1’
        by METIS_TAC [in_right_open_intervals] >> POP_ORW \\
     PROVE_TAC [lambda0_not_infty])
 >> Rewr'
 >> simp [GSYM o_ASSOC]
 (* clean up *)
 >> ‘!i. i < N ==> h i IN subsets right_open_intervals’ by rw [Abbr ‘h’]
 >> ‘!i j. i < N /\ j < N /\ i <> j ==> DISJOINT (h i) (h j)’ by rw [Abbr ‘h’]
 >> ‘!i j. i < N /\ j < N /\ i < j ==>
           interval_lowerbound (h i) < interval_lowerbound (h j)’ by rw [Abbr ‘h’]
 >> ‘!i. i < N ==> h i <> {}’ by rw [Abbr ‘h’]
 >> Q.PAT_X_ASSUM ‘!i. _ ==> f i IN subsets right_open_intervals’ K_TAC
 >> Q.PAT_X_ASSUM ‘!i j. _ ==> DISJOINT (f i) (f j)’              K_TAC
 >> Q.PAT_X_ASSUM ‘!i j. _ ==> interval_lowerbound (f (g i)) < _’ K_TAC
 >> Q.PAT_X_ASSUM ‘!i. i < N ==> g i < n /\ f (g i) <> {}’        K_TAC
 >> Q.PAT_X_ASSUM ‘FINITE filtered’         K_TAC
 >> Q.PAT_X_ASSUM ‘filtered SUBSET count n’ K_TAC
 >> Q.PAT_X_ASSUM ‘0 < n’ K_TAC
 >> Q.PAT_X_ASSUM ‘N <= n’ K_TAC
 >> Q.PAT_X_ASSUM ‘!i j. i < N /\ j < N /\ i <> j ==> g i <> g j’ K_TAC
 >> Q.UNABBREV_TAC ‘filtered’
 (* now the goal and assumptions are only about ‘h’ and ‘N’ *)
 >> Suff `!i. i <= N ==>
              BIGUNION (IMAGE h (count i)) IN subsets right_open_intervals`
 >- (DISCH_TAC \\
     Suff `!m. m <= N ==>
               (lambda0 (BIGUNION (IMAGE h (count m))) =
                SIGMA (lambda0 o h) (count m))`
     >- (DISCH_THEN MATCH_MP_TAC >> rw [LESS_EQ_REFL]) \\
     Induct_on `m` (* final induction *)
     >- rw [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY, lambda0_empty] \\
     DISCH_TAC \\
     SIMP_TAC std_ss [COUNT_SUC, IMAGE_INSERT, BIGUNION_INSERT] \\
     Know `lambda0 (h m UNION BIGUNION (IMAGE h (count m))) =
           lambda0 (h m) + lambda0 (BIGUNION (IMAGE h (count m)))`
     >- (MATCH_MP_TAC (REWRITE_RULE [measurable_sets_def, measure_def]
                                    (Q.ISPEC `lborel0` ADDITIVE)) \\
         rw [] >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
         REWRITE_TAC [GSYM BIGUNION_INSERT, GSYM IMAGE_INSERT, GSYM COUNT_SUC] \\
         FIRST_X_ASSUM MATCH_MP_TAC >> art []) >> Rewr' \\
     Q.PAT_X_ASSUM `m <= N ==> _` MP_TAC \\
    `m <= N` by RW_TAC arith_ss [] \\
     RW_TAC std_ss [] \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     Suff `SIGMA (lambda0 o h) (m INSERT count m) = (lambda0 o h) m +
           SIGMA (lambda0 o h) (count m DELETE m)`
     >- rw [o_DEF, COUNT_DELETE] \\
     irule EXTREAL_SUM_IMAGE_PROPERTY_NEG \\
     RW_TAC std_ss [GSYM COUNT_SUC, IN_COUNT, o_DEF, FINITE_COUNT] \\
     MATCH_MP_TAC pos_not_neginf \\
     fs [positive_def, measure_def, measurable_sets_def])
 (* h-property of upper- and lowerbounds *)
 >> Know `!i j. i < N /\ j < N /\ i <= j ==>
                interval_lowerbound (h i) <= interval_lowerbound (h j)`
 >- (rw [REAL_LE_LT] \\
    ‘j = i \/ i < j’ by rw [] >- rw [] >> DISJ1_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 >> DISCH_TAC
 >> Know `!i j. i < N /\ j < N /\ i < j ==>
                interval_upperbound (h i) <= interval_lowerbound (h j)`
 >- (rpt STRIP_TAC \\
     SPOSE_NOT_THEN (ASSUME_TAC o (REWRITE_RULE [GSYM real_lt])) \\
    ‘interval_lowerbound (h i) < interval_lowerbound (h j)’ by PROVE_TAC [] \\
    `?a1 b1. a1 < b1 /\ (h i = right_open_interval a1 b1)`
         by METIS_TAC [in_right_open_intervals_nonempty] \\
    `?a2 b2. a2 < b2 /\ (h j = right_open_interval a2 b2)`
         by METIS_TAC [in_right_open_intervals_nonempty] \\
     FULL_SIMP_TAC std_ss [right_open_interval_upperbound,
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
     >- (rw [in_right_open_interval] >> rw [REAL_LT_IMP_LE]) \\
     Know `a2 IN right_open_interval a2 b2`
     >- (rw [in_right_open_interval]) \\
     RW_TAC bool_ss []) >> DISCH_TAC
 (* h-property of upperbounds *)
 >> Know `!i j. i < N /\ j < N /\ i < j ==>
                interval_upperbound (h i) <= interval_upperbound (h j)`
 >- (rpt STRIP_TAC \\
     MATCH_MP_TAC REAL_LE_TRANS \\
     Q.EXISTS_TAC `interval_lowerbound (h j)` >> rw [] \\
    `h j IN subsets right_open_intervals` by PROVE_TAC [] \\
     POP_ASSUM (STRIP_ASSUME_TAC o
                (REWRITE_RULE [in_right_open_intervals])) >> POP_ORW \\
     REWRITE_TAC [right_open_interval_two_bounds]) >> DISCH_TAC
 (* h-compactness: there's no gap between each h(i) *)
 >> Know `!i. SUC i < N ==>
             (interval_lowerbound (h (SUC i)) = interval_upperbound (h i))`
 >- (rpt STRIP_TAC >> `i < N` by RW_TAC arith_ss [] \\
     ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
     Know `BIGUNION (IMAGE h (count N)) <> {} /\
           BIGUNION (IMAGE h (count N)) IN subsets right_open_intervals`
     >- (Q.UNABBREV_TAC `N` >> art [] \\
         RW_TAC std_ss [Once EXTENSION, IN_BIGUNION_IMAGE, IN_COUNT, NOT_IN_EMPTY] \\
        `h i <> {}` by METIS_TAC [] \\
         FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] \\
         qexistsl_tac [`x`, `i`] >> art []) \\
     REWRITE_TAC [in_right_open_intervals_nonempty] \\
     STRIP_TAC >> POP_ASSUM MP_TAC \\
     SIMP_TAC std_ss [GSPECIFICATION, right_open_interval, IN_BIGUNION_IMAGE,
                      IN_COUNT, Once EXTENSION] >> DISCH_TAC \\
  (* |- !x. (?x'. x' < N /\ x IN h x') <=> a <= x /\ x < b *)
     CCONTR_TAC \\ (* suppose there's a gap between h(i) and h(i+1) *)
    `i < SUC i` by RW_TAC arith_ss [] \\
     Q.PAT_X_ASSUM `!i j. _ ==> interval_upperbound (h i) <= interval_lowerbound (h j)`
       (MP_TAC o (Q.SPECL [`i`, `SUC i`])) >> rw [] \\
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
    `?j. j < N /\ z IN h j` by METIS_TAC [] \\
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
         >- (FIRST_X_ASSUM MATCH_MP_TAC >> rw []) \\
        `(interval_lowerbound (h (SUC i)) = a2) /\
         (interval_lowerbound (h j) = a3)` by PROVE_TAC [right_open_interval_lowerbound] \\
         NTAC 2 (POP_ASSUM (PURE_ONCE_REWRITE_TAC o wrap)) >> DISCH_TAC \\
        `z < a3` by PROVE_TAC [REAL_LTE_TRANS] \\
         METIS_TAC [REAL_LTE_ANTISYM]) >> DISCH_TAC \\
    `SUC i <= j` by RW_TAC arith_ss [] \\
     METIS_TAC [LESS_EQ_ANTISYM]) >> DISCH_TAC
 (* final strike *)
 >> NTAC 3 (Q.PAT_X_ASSUM `!i j. i < N /\ j < N /\ _ ==> A <= B` K_TAC)
 >> rpt STRIP_TAC
 >> Cases_on `i`
 >- (rw [COUNT_ZERO, IMAGE_EMPTY, BIGUNION_EMPTY, EXTREAL_SUM_IMAGE_EMPTY] \\
     MATCH_MP_TAC SEMIRING_EMPTY >> art [])
 >> rename1 `SUC i <= N`
 >> Suff `!j. SUC j <= N ==>
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
     CONJ_TAC >- PROVE_TAC [] (* h 0 <> {} *) \\
     Know `h 0 <> {} /\ h 0 IN subsets right_open_intervals` >- PROVE_TAC [] \\
     DISCH_THEN (STRIP_ASSUME_TAC o
                 (REWRITE_RULE [in_right_open_intervals_nonempty])) \\
     POP_ORW \\
     METIS_TAC [right_open_interval_lowerbound, right_open_interval_upperbound])
 >> DISCH_TAC
 >> `SUC j < N /\ SUC j <= N` by RW_TAC arith_ss []
 >> Q.PAT_X_ASSUM `SUC j <= N ==> P` MP_TAC
 >> Q.UNABBREV_TAC `N` >> RW_TAC std_ss []
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
(*  Extreal-based Borel measure space                                        *)
(* ------------------------------------------------------------------------- *)

Definition ext_lborel_def :
    ext_lborel = (space Borel, subsets Borel, lambda o real_set)
End

Theorem MEASURE_SPACE_LBOREL :
    measure_space ext_lborel
Proof
    simp [ext_lborel_def, measure_space_def, SIGMA_ALGEBRA_BOREL]
 >> Know ‘!B. real_set (IMAGE Normal B) = B /\
              real_set (IMAGE Normal B UNION {NegInf}) = B /\
              real_set (IMAGE Normal B UNION {PosInf}) = B /\
              real_set (IMAGE Normal B UNION {NegInf; PosInf}) = B’
 >- (rpt STRIP_TAC \\
     rw [Once EXTENSION, real_set_def] \\
     EQ_TAC >> rw [] >> art [real_normal] \\
     Q.EXISTS_TAC ‘Normal x’ >> rw [extreal_not_infty])
 >> rpt STRIP_TAC
 (* positive *)
 >- (rw [positive_def] >- rw [real_set_def, lambda_empty] \\
     STRIP_ASSUME_TAC
       (REWRITE_RULE [positive_def] (MATCH_MP MEASURE_SPACE_POSITIVE
                                              measure_space_lborel)) \\
     POP_ASSUM MATCH_MP_TAC >> fs [Borel, sets_lborel])
 (* countably_additive *)
 >> rw [countably_additive_def, SPACE_BOREL, IN_FUNSET, IN_UNIV]
 >> Q.ABBREV_TAC ‘rf = real_set o f’
 >> Know ‘!n. rf n IN subsets borel’
 >- (GEN_TAC \\
     Q.PAT_X_ASSUM ‘BIGUNION (IMAGE f UNIV) IN subsets Borel’ K_TAC \\
     Q.PAT_X_ASSUM ‘!i j. i <> j ==> DISJOINT (f i) (f j)’ K_TAC \\
     fs [Abbr ‘rf’, Borel] \\
     POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC ‘n’)) >> fs [])
 >> DISCH_TAC
 >> Know ‘real_set (BIGUNION (IMAGE f UNIV)) = BIGUNION (IMAGE rf UNIV)’
 >- (rw [Once EXTENSION, real_set_def, Abbr ‘rf’] \\
     EQ_TAC >> rw []
     >- (rename1 ‘y IN f n’ \\
         Q.EXISTS_TAC ‘(real_set o f) n’ \\
         rw [real_set_def] >- (Q.EXISTS_TAC ‘y’ >> rw []) \\
         Q.EXISTS_TAC ‘n’ >> rw []) \\
     fs [GSPECIFICATION] >> rename1 ‘y IN f n’ \\
     Q.EXISTS_TAC ‘y’ >> rw [] \\
     Q.EXISTS_TAC ‘f n’ >> rw [] \\
     Q.EXISTS_TAC ‘n’ >> rw []) >> Rewr'
 >> MATCH_MP_TAC EQ_SYM
 >> MATCH_MP_TAC (Q.ISPEC ‘lborel’ COUNTABLY_ADDITIVE)
 >> simp [IN_FUNSET, IN_UNIV, sets_lborel]
 >> CONJ_TAC >- METIS_TAC [measure_space_def, measure_space_lborel]
 (* DISJOINT (rf i) (rf j) *)
 >> CONJ_TAC
 >- (qx_genl_tac [‘m’, ‘n’] >> DISCH_TAC \\
     fs [DISJOINT_ALT, Abbr ‘rf’] \\
     rw [real_set_def] >> rename1 ‘y IN f m’ \\
     rename1 ‘real z = real y’ \\
     Cases_on ‘z = PosInf’ >- rw [] >> DISJ2_TAC \\
     Cases_on ‘z = NegInf’ >- rw [] >> DISJ2_TAC \\
    ‘?a. y = Normal a’ by METIS_TAC [extreal_cases] \\
    ‘?b. z = Normal b’ by METIS_TAC [extreal_cases] \\
     fs [real_normal] \\
     FIRST_X_ASSUM irule >> Q.EXISTS_TAC ‘m’ >> rw [])
 (* BIGUNION IN subsets borel *)
 >> STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_FN] sigma_algebra_borel)
 >> POP_ASSUM MATCH_MP_TAC
 >> rw [IN_FUNSET]
QED

Theorem SIGMA_FINITE_LBOREL :
    sigma_finite ext_lborel
Proof
    RW_TAC std_ss [MATCH_MP SIGMA_FINITE_ALT2 MEASURE_SPACE_LBOREL]
 >> Q.EXISTS_TAC `{NegInf; PosInf} INSERT {IMAGE Normal (line n) | n IN UNIV}`
 >> rpt CONJ_TAC (* 4 subgoals *)
 >- (REWRITE_TAC [countable_INSERT] \\
     Know ‘{IMAGE Normal (line n) | n IN UNIV} = IMAGE (IMAGE Normal) {line n | n IN UNIV}’
     >- (rw [Once EXTENSION] >> EQ_TAC >> rw []
         >- (Q.EXISTS_TAC ‘line n’ >> REWRITE_TAC [] \\
             Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
         Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) >> Rewr' \\
     MATCH_MP_TAC image_countable \\
    ‘{line n | n IN UNIV} = IMAGE line UNIV’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC image_countable \\
     SIMP_TAC std_ss [COUNTABLE_NUM])
 (* SUBSET *)
 >- (SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, measurable_sets_def,
                      ext_lborel_def, IN_UNIV, line] \\
     rw [IN_INSERT]
     >- (rw [Borel] >> qexistsl_tac [‘{}’, ‘{NegInf; PosInf}’] >> rw [] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> REWRITE_TAC [sigma_algebra_borel]) \\
     Know ‘IMAGE Normal {x | -&n <= x /\ x <= &n} = {x | Normal (-&n) <= x /\ x <= Normal (&n)}’
     >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] >> rw [extreal_le_eq] \\
         Q.EXISTS_TAC ‘real x’ \\
         STRONG_CONJ_TAC
         >- (MATCH_MP_TAC EQ_SYM >> MATCH_MP_TAC normal_real \\
             CONJ_TAC >> REWRITE_TAC [lt_infty] >| (* 2 subgoals *)
             [ (* goal 1 (of 2) *)
               MATCH_MP_TAC lte_trans >> Q.EXISTS_TAC ‘Normal (-&n)’ >> art [lt_infty],
               (* goal 2 (of 2) *)
               MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘Normal (&n)’ >> art [lt_infty] ]) \\
         DISCH_THEN (ASSUME_TAC o (ONCE_REWRITE_RULE [EQ_SYM_EQ])) \\
         ASM_SIMP_TAC std_ss [GSYM extreal_le_eq]) >> Rewr' \\
     REWRITE_TAC [BOREL_MEASURABLE_SETS_CC])
 (* BIGUNION *)
 >- (SIMP_TAC std_ss [Once EXTENSION, m_space_def, ext_lborel_def, IN_UNIV] \\
     SIMP_TAC std_ss [IN_BIGUNION, GSPECIFICATION, IN_INSERT, SPACE_BOREL, IN_UNIV] \\
     GEN_TAC >> ASSUME_TAC REAL_IN_LINE \\
     Cases_on ‘x = PosInf’
     >- (Q.EXISTS_TAC ‘{NegInf; PosInf}’ >> rw []) \\
     Cases_on ‘x = NegInf’
     >- (Q.EXISTS_TAC ‘{NegInf; PosInf}’ >> rw []) \\
    ‘?r. x = Normal r’ by METIS_TAC [extreal_cases] >> POP_ORW \\
     Q.PAT_X_ASSUM ‘!x. ?n. x IN line n’ (STRIP_ASSUME_TAC o Q.SPEC `r`) \\
     Q.EXISTS_TAC ‘IMAGE Normal (line n)’ \\
     CONJ_TAC >- (rw [IN_IMAGE]) \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘n’ >> REWRITE_TAC [])
 >> rw [GSPECIFICATION, IN_UNIV, line, ext_lborel_def]
 >- (Know ‘real_set {NegInf; PosInf} = {}’
     >- (rw [Once EXTENSION, NOT_IN_EMPTY, real_set_def] >> PROVE_TAC []) >> Rewr' \\
     REWRITE_TAC [lambda_empty, extreal_of_num_def, extreal_not_infty])
 >> Know ‘real_set (IMAGE Normal {x | -&n <= x /\ x <= &n}) = {x | -&n <= x /\ x <= &n}’
 >- (rw [Once EXTENSION, real_set_def] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rename1 ‘y <= &n’ >> art [real_normal],
       (* goal 2 (of 3) *)
       rename1 ‘-&n <= y’ >> art [real_normal],
       (* goal 3 (of 3) *)
       Q.EXISTS_TAC ‘Normal x’ >> rw [extreal_not_infty, real_normal] ])
 >> Rewr'
 >> `-&n <= (&n) :real` by RW_TAC real_ss []
 >> POP_ASSUM (MP_TAC o (SIMP_RULE list_ss [CLOSED_interval]) o
               (MATCH_MP lambda_closed_interval)) >> Rewr'
 >> REWRITE_TAC [extreal_not_infty]
QED

Theorem seq_le_imp_lim_le :
    !x y (f :num->real). (!n. f n <= x) /\ (f --> y) sequentially ==> y <= x
Proof
    RW_TAC bool_ss [LIM_SEQUENTIALLY]
 >> MATCH_MP_TAC REAL_LE_EPSILON
 >> RW_TAC bool_ss []
 >> Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`)
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o Q.SPEC `N`)
 >> Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
 >> REWRITE_TAC [dist]
 >> (RW_TAC bool_ss [GREATER_EQ, LESS_EQ_REFL, abs, REAL_LE_SUB_LADD, REAL_ADD_LID] \\
     FULL_SIMP_TAC bool_ss [REAL_NOT_LE, REAL_NEG_SUB, REAL_LT_SUB_RADD])
 >| [ (* goal 1 (of 2) *)
      MATCH_MP_TAC REAL_LE_TRANS \\
      Q.EXISTS_TAC `x` \\
      CONJ_TAC >- PROVE_TAC [REAL_LE_TRANS] \\
      PROVE_TAC [REAL_LE_ADDR, REAL_LT_LE],
      (* goal 2 (of 2) *)
      MATCH_MP_TAC REAL_LE_TRANS \\
      Q.EXISTS_TAC `f N + e` \\
      CONJ_TAC >- PROVE_TAC [REAL_LT_LE, REAL_ADD_SYM] \\
      PROVE_TAC [REAL_LE_ADD2, REAL_LE_REFL] ]
QED

(* cf. seqTheory.SEQ_MONO_LE *)
Theorem seq_mono_le :
    !(f :num->real) x n. (!n. f n <= f (n + 1)) /\ (f --> x) sequentially ==> f n <= x
Proof
   RW_TAC bool_ss [LIM_SEQUENTIALLY] THEN MATCH_MP_TAC REAL_LE_EPSILON THEN
   RW_TAC bool_ss [] THEN Q.PAT_X_ASSUM `!e. P e` (MP_TAC o Q.SPEC `e`) THEN
   RW_TAC bool_ss [GREATER_EQ] THEN MP_TAC (Q.SPECL [`N`, `n`] LESS_EQ_CASES) THEN
   STRIP_TAC THENL
   [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `n`) THEN ASM_REWRITE_TAC [dist] THEN
    REAL_ARITH_TAC, ALL_TAC] THEN FULL_SIMP_TAC std_ss [dist] THEN
   (SUFF_TAC ``!i : num. f (N - i) <= x + (e : real)`` THEN1 PROVE_TAC [LESS_EQUAL_DIFF]) THEN
   INDUCT_TAC
   THENL [Q.PAT_X_ASSUM `!n. P n` (MP_TAC o Q.SPEC `N`)
          THEN RW_TAC bool_ss [abs, LESS_EQ_REFL, SUB_0]
          THEN simpLib.FULL_SIMP_TAC bool_ss
               [REAL_LT_SUB_RADD, REAL_NEG_SUB, REAL_NOT_LE, REAL_ADD_LID,
                REAL_LE_SUB_LADD]
          THEN PROVE_TAC
               [REAL_LT_LE, REAL_ADD_SYM, REAL_LE_TRANS, REAL_LE_ADDR],
          MP_TAC (ARITH_PROVE
                  ``(N - i = N - SUC i) \/ (N - i = (N - SUC i) + 1)``)
          THEN PROVE_TAC [REAL_LE_REFL, REAL_LE_TRANS]]
QED

Theorem sup_seq' : (* was: sup_sequence *)
    !f l. mono_increasing f ==> ((f --> l) sequentially =
          (sup (IMAGE (\n. Normal (f n)) UNIV) = Normal l))
Proof
    rpt STRIP_TAC
 >> Suff ‘(f --> l) sequentially <=> (f --> l)’
 >- (Rewr' \\
     MATCH_MP_TAC sup_seq >> art [])
 >> REWRITE_TAC [LIM_SEQUENTIALLY_SEQ]
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

(* ------------------------------------------------------------------------- *)
(*  Almost everywhere (a.e.) - basic binder definitions                      *)
(* ------------------------------------------------------------------------- *)

val almost_everywhere_def = Define
   `almost_everywhere m P = ?N. null_set m N /\ !x. x IN (m_space m DIFF N) ==> P x`;

(* This binder syntax is learnt from Thomas Tuerk. ‘lborel’ is a required
   household measure space for `AE x. P x` without `::m`, but it's never used.
 *)
Definition AE_def :
    $AE = \P. almost_everywhere lborel P
End

val _ = set_fixity "AE" Binder;
val _ = associate_restriction ("AE", "almost_everywhere");

(* LATIN CAPITAL LETTER AE (doesn't look good)
val _ = Unicode.unicode_version {u = UTF8.chr 0x00C6, tmnm = "AE"};
 *)

Theorem AE_THM :
    !m P. (AE x::m. P x) <=> almost_everywhere m P
Proof
    SIMP_TAC std_ss [almost_everywhere_def]
QED

Theorem AE_DEF :
    !m P. (AE x::m. P x) <=>
          ?N. null_set m N /\ !x. x IN (m_space m DIFF N) ==> P x
Proof
    rw [AE_THM, almost_everywhere_def]
QED

Theorem AE_ALT :
    !m P. (AE x::m. P x) <=>
          ?N. null_set m N /\ {x | x IN m_space m /\ ~P x} SUBSET N
Proof
    RW_TAC std_ss [AE_DEF, SUBSET_DEF, GSPECIFICATION, IN_DIFF]
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

Theorem FORALL_IMP_AE :
    !m P. measure_space m /\ (!x. x IN m_space m ==> P x) ==> AE x::m. P x
Proof
    RW_TAC std_ss [AE_DEF]
 >> Q.EXISTS_TAC `{}`
 >> RW_TAC std_ss [NULL_SET_EMPTY, IN_DIFF, NOT_IN_EMPTY]
QED

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
          ((AE x::M. P x) <=> (null_set M {x | x IN m_space M /\ ~P x}))
Proof
  RW_TAC std_ss [AE_ALT, null_set_def, GSPECIFICATION] THEN EQ_TAC THEN
  RW_TAC std_ss [] THENL [ALL_TAC, METIS_TAC [SUBSET_REFL]] THEN
  Q_TAC SUFF_TAC `measure M {x | x IN m_space M /\ ~P x} <=
                  measure M N` THENL
  [DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM le_antisym] THEN
   METIS_TAC [measure_space_def, positive_def], ALL_TAC] THEN
  MATCH_MP_TAC INCREASING THEN METIS_TAC [MEASURE_SPACE_INCREASING]
QED

(* NOTE: changed ‘{x | ~N x} x’ to ‘~N x’ *)
Theorem AE_iff_null_sets :
    !N M. measure_space M /\ N IN measurable_sets M ==>
         (null_set M N <=> AE x::M. ~N x)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> RW_TAC std_ss [AE_ALT, null_set_def]
 >- (Q.EXISTS_TAC ‘N’ >> rw [SUBSET_DEF, IN_DEF])
 >> fs [SUBSET_DEF]
 >> Suff ‘measure M N <= measure M N'’
 >- (DISCH_TAC >> ONCE_REWRITE_TAC [GSYM le_antisym] \\
     METIS_TAC [measure_space_def, positive_def])
 >> MATCH_MP_TAC INCREASING
 >> ASM_SIMP_TAC std_ss [MEASURE_SPACE_INCREASING]
 >> ‘N SUBSET m_space M’ by METIS_TAC [MEASURABLE_SETS_SUBSET_SPACE]
 >> fs [SUBSET_DEF, IN_DEF]
QED

Theorem AE_NOT_IN :
    !N M. null_set M N ==> AE x::M. x NOTIN N
Proof
    RW_TAC std_ss [AE_ALT]
 >> Q.EXISTS_TAC ‘N’
 >> ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, IN_DEF]
QED

(* |- !N M. null_set M N ==> AE x::M. ~N x

   NOTE: changed ‘{x | ~N x} x’ to ‘~N x’
 *)
Theorem AE_not_in = SIMP_RULE std_ss [IN_DEF] AE_NOT_IN

Theorem AE_iff_measurable :
    !N M P. measure_space M /\ N IN measurable_sets M /\
            ({x | x IN m_space M /\ ~P x} = N) ==>
            ((AE x::M. P x) <=> (measure M N = 0))
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

(* Quantifier movement conversions for AE *)
Theorem RIGHT_IMP_AE_THM : (* was: AE_impl *)
    !m P Q. measure_space m ==> ((P ==> AE x::m. Q x) <=> (AE x::m. P ==> Q x))
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> RW_TAC bool_ss [AE_DEF]
 >- (Cases_on ‘P’ >- (fs [] >> Q.EXISTS_TAC ‘N’ >> rw []) \\
     rw [] >> Q.EXISTS_TAC ‘{}’ \\
     MATCH_MP_TAC NULL_SET_EMPTY >> art [])
 >> Q.EXISTS_TAC ‘N’ >> rw []
QED

Theorem RIGHT_IMP_AE_THM' : (* was: AE_all_S *)
    !m P Q. measure_space m ==>
           ((!i. P i ==> AE x::m. Q i x) <=> (!i. AE x::m. P i ==> Q i x))
Proof
    rpt STRIP_TAC
 >> reverse EQ_TAC >> RW_TAC bool_ss [AE_DEF]
 >- (Q.PAT_X_ASSUM ‘!i. _’ (MP_TAC o Q.SPEC ‘i’) >> STRIP_TAC \\
     Q.EXISTS_TAC ‘N’ >> rw [])
 >> Cases_on ‘P i’
 >- (Q.PAT_X_ASSUM ‘!i. _’ (MP_TAC o Q.SPEC ‘i’) >> STRIP_TAC \\
     POP_ASSUM MP_TAC >> RW_TAC bool_ss [])
 >> rw [] >> Q.EXISTS_TAC ‘{}’
 >> MATCH_MP_TAC NULL_SET_EMPTY >> art []
QED

(* Fixed statements by checking Isabelle's Measure_Space.thy *)
Theorem AE_FORALL_SWAP_THM : (* was: AE_all_countable *)
    !m P. measure_space m /\ countable univ(:'index) ==>
         ((AE x::m. !i. P i x) <=> !(i:'index). AE x::m. P i x)
Proof
    rpt STRIP_TAC
 >> EQ_TAC >> rw [AE_DEF] >- (Q.EXISTS_TAC `N` >> rw [])
 >> fs [SKOLEM_THM] (* this assert ‘f’ *)
 >> fs [COUNTABLE_ENUM]
 >> rename1 ‘IMAGE g univ(:num) = univ(:'index)’
 >> Q.EXISTS_TAC ‘BIGUNION (IMAGE (f o g) univ(:num))’
 >> CONJ_TAC
 >- (MATCH_MP_TAC (REWRITE_RULE [IN_APP] NULL_SET_BIGUNION) >> rw [o_DEF])
 >> rw [IN_BIGUNION]
 >> Q.PAT_X_ASSUM ‘!i. null_set m (f i) /\ _’ (MP_TAC o (Q.SPEC ‘i’))
 >> RW_TAC std_ss []
 >> FIRST_X_ASSUM MATCH_MP_TAC >> RW_TAC std_ss []
 >> CCONTR_TAC >> fs []
 >> Q.PAT_X_ASSUM ‘!s. x NOTIN s \/ _’ (MP_TAC o (Q.SPEC ‘f (i :'index)’))
 >> RW_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘IMAGE g univ(:num) = univ(:'index)’ MP_TAC
 >> rw [Once EXTENSION]
 >> METIS_TAC []
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
 >> fs [complete_measure_space_def, AE_ALT, IN_MEASURABLE_BOREL, IN_FUNSET]
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
 >> ‘sigma_algebra (measurable_space m)’ by PROVE_TAC [measure_space_def]
 >> fs [IN_MEASURABLE_BOREL]
QED

(* ------------------------------------------------------------------------- *)
(*   Unconditional IN_MEASURABLE_BOREL_ADD and IN_MEASURABLE_BOREL_SUB       *)
(*   (Author: Chun Tian)                                                     *)
(* ------------------------------------------------------------------------- *)

(* |- !s t u. (t UNION u) INTER s = t INTER s UNION u INTER s *)
val UNION_OVER_INTER' = ONCE_REWRITE_RULE [INTER_COMM] UNION_OVER_INTER;

val IN_MEASURABLE_BOREL_ADD_tactics_1 =
    Know ‘{x | ?r. f x + g x = Normal r /\ r IN B} INTER space a =
          {x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
               ?r. rf x + rg x = r /\ r IN B} INTER space a’
 >- (rw [Once EXTENSION] >> EQ_TAC
     >- (STRIP_TAC \\
         Know ‘f x <> PosInf’
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] >> rfs []) \\
         Know ‘f x <> NegInf’
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] >> rfs []) \\
         Know ‘g x <> PosInf’
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def] >> rfs []) \\
         Know ‘g x <> NegInf’
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def] >> rfs []) \\
         NTAC 4 STRIP_TAC >> art [] \\
        ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
        ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
        ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
        ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
         fs [extreal_add_def]) \\
     STRIP_TAC >> art [] \\
     Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
     rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
     simp [normal_real])
 >> Rewr'
 >> ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
          ?r. rf x + rg x = r /\ r IN B} INTER space a =
      ({x | ?r. rf x + rg x = r /\ r IN B} INTER space a) INTER
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x <> PosInf} INTER space a) INTER
      ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [])
 >> Q.ABBREV_TAC ‘h = \x. rf x + rg x’
 >> Know ‘{x | ?r. rf x + rg x = r /\ r IN B} = PREIMAGE h B’
 >- rw [PREIMAGE_def, Abbr ‘h’] >> Rewr'
 >> Suff ‘h IN measurable a borel’ >- rw [IN_MEASURABLE]
 >> MATCH_MP_TAC in_borel_measurable_add
 >> qexistsl_tac [‘rf’, ‘rg’] >> simp []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ (* goal 1.1 (of 2) *)
      Q.UNABBREV_TAC ‘rf’ \\
      MATCH_MP_TAC in_borel_measurable_from_Borel >> art [],
      (* goal 1.2 (of 2) *)
      Q.UNABBREV_TAC ‘rg’ \\
      MATCH_MP_TAC in_borel_measurable_from_Borel >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_3 =
    rename1 ‘NegInf + PosInf = Normal z’
 >> Know ‘{x | ?r. f x + g x = Normal r /\ r IN B} INTER space a =
          if z IN B then
            ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                  ?r. rf x + rg x = r /\ r IN B} INTER space a) UNION
            ({x | f x = NegInf /\ g x = PosInf} INTER space a)
          else
            ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                  ?r. rf x + rg x = r /\ r IN B} INTER space a)’
 >- (Cases_on ‘z IN B’ >> rw [Once EXTENSION] >| (* 2 subgoal *)
     [ (* goal 3.1 (of 2) *)
       EQ_TAC >> STRIP_TAC >| (* 3 subgoals *)
       [ (* goal 3.1.1 (of 3) *)
         Know ‘f x <> PosInf’
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] >> rfs []) \\
         Know ‘g x <> NegInf’
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def] >> rfs []) \\
         NTAC 2 STRIP_TAC >> simp [] \\
         Cases_on ‘f x = NegInf’
         >- (simp [] >> CCONTR_TAC \\
            ‘?y. g x = Normal y’ by METIS_TAC [extreal_cases] \\
             fs [extreal_add_def]) \\
         Cases_on ‘g x = PosInf’
         >- (simp [] \\
            ‘?y. f x = Normal y’ by METIS_TAC [extreal_cases] \\
             fs [extreal_add_def]) \\
         DISJ1_TAC >> art [] \\
        ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
        ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
        ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
        ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
         fs [extreal_add_def],
         (* goal 3.1.2 (of 3) *)
         simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
         rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
         simp [normal_real],
         (* goal 3.1.3 (of 3) *)
         simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] ],
       (* goal 3.2 (of 2) *)
       EQ_TAC >> STRIP_TAC >| (* 2 subgoals *)
       [ (* goal 3.2.1 (of 2) *)
         simp [] \\
         Know ‘f x <> PosInf’
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] >> rfs []) \\
         Know ‘g x <> NegInf’
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def] >> rfs []) \\
         NTAC 2 STRIP_TAC >> simp [] \\
         STRONG_CONJ_TAC
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] \\
             METIS_TAC [extreal_11]) >> DISCH_TAC \\
         STRONG_CONJ_TAC
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
         DISCH_TAC \\
        ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
        ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
        ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
        ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
         fs [extreal_add_def],
         (* goal 3.2.2 (of 2) *)
         simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
         rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
         simp [normal_real] ] ])
 >> Rewr'
 (* stage work *)
 >> Know ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
               ?r. rf x + rg x = r /\ r IN B} INTER space a IN subsets a’
 >- (‘{x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
           ?r. rf x + rg x = r /\ r IN B} INTER space a =
       ({x | ?r. rf x + rg x = r /\ r IN B} INTER space a) INTER
       ({x | f x <> PosInf} INTER space a) INTER
       ({x | f x <> NegInf} INTER space a) INTER
       ({x | g x <> PosInf} INTER space a) INTER
       ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art []) \\
     Q.ABBREV_TAC ‘h = \x. rf x + rg x’ \\
     Know ‘{x | ?r. rf x + rg x = r /\ r IN B} = PREIMAGE h B’
     >- rw [PREIMAGE_def, Abbr ‘h’] >> Rewr' \\
     Suff ‘h IN measurable a borel’ >- rw [IN_MEASURABLE] \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘rf’, ‘rg’] >> simp [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 2.1 (of 2) *)
       Q.UNABBREV_TAC ‘rf’ \\
       MATCH_MP_TAC in_borel_measurable_from_Borel >> art [],
       (* goal 2.2 (of 2) *)
       Q.UNABBREV_TAC ‘rg’ \\
       MATCH_MP_TAC in_borel_measurable_from_Borel >> art [] ])
 >> DISCH_TAC
 >> Cases_on ‘z IN B’ >> fs []
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> ‘{x | f x = NegInf /\ g x = PosInf} INTER space a =
      ({x | f x = NegInf} INTER space a) INTER
      ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_7 =
    rename1 ‘PosInf + NegInf = Normal z’
 >> Know ‘{x | ?r. f x + g x = Normal r /\ r IN B} INTER space a =
          if z IN B then
             ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                   ?r. rf x + rg x = r /\ r IN B} INTER space a) UNION
             ({x | f x = PosInf /\ g x = NegInf} INTER space a)
          else
             ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                   ?r. rf x + rg x = r /\ r IN B} INTER space a)’
 >- (Cases_on ‘z IN B’ >> rw [Once EXTENSION] >| (* 2 subgoal *)
     [ (* goal 7.1 (of 2) *)
       EQ_TAC >> STRIP_TAC >| (* 3 subgoals *)
       [ (* goal 7.1.1 (of 3) *)
         Know ‘f x <> NegInf’
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] >> rfs []) \\
         Know ‘g x <> PosInf’
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def] >> rfs []) \\
         NTAC 2 STRIP_TAC >> simp [] \\
         Cases_on ‘f x = PosInf’
         >- (simp [] >> CCONTR_TAC \\
            ‘?y. g x = Normal y’ by METIS_TAC [extreal_cases] \\
             fs [extreal_add_def]) \\
         Cases_on ‘g x = NegInf’
         >- (simp [] \\
            ‘?y. f x = Normal y’ by METIS_TAC [extreal_cases] \\
             fs [extreal_add_def]) \\
         DISJ1_TAC >> art [] \\
        ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
        ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
        ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
        ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
         fs [extreal_add_def],
         (* goal 7.1.2 (of 3) *)
         simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
         rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
         simp [normal_real],
         (* goal 7.1.3 (of 3) *)
         simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] ],
       (* goal 7.2 (of 2) *)
       EQ_TAC >> STRIP_TAC >| (* 2 subgoals *)
       [ (* goal 7.2.1 (of 2) *)
         simp [] \\
         Know ‘f x <> NegInf’
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] >> rfs []) \\
         Know ‘g x <> PosInf’
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def] >> rfs []) \\
         NTAC 2 STRIP_TAC >> simp [] \\
         STRONG_CONJ_TAC
         >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] \\
             METIS_TAC [extreal_11]) >> DISCH_TAC \\
         STRONG_CONJ_TAC
         >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
         DISCH_TAC \\
        ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
        ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
        ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
        ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
         fs [extreal_add_def],
         (* goal 3.2.2 (of 2) *)
         simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
         rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
         simp [normal_real] ] ])
 >> Rewr'
 (* stage work *)
 >> Know ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
               ?r. rf x + rg x = r /\ r IN B} INTER space a IN subsets a’
 >- (‘{x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
           ?r. rf x + rg x = r /\ r IN B} INTER space a =
      ({x | ?r. rf x + rg x = r /\ r IN B} INTER space a) INTER
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x <> PosInf} INTER space a) INTER
      ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art []) \\
     Q.ABBREV_TAC ‘h = \x. rf x + rg x’ \\
     Know ‘{x | ?r. rf x + rg x = r /\ r IN B} = PREIMAGE h B’
     >- (rw [PREIMAGE_def, Abbr ‘h’]) >> Rewr' \\
     Suff ‘h IN measurable a borel’ >- rw [IN_MEASURABLE] \\
     MATCH_MP_TAC in_borel_measurable_add \\
     qexistsl_tac [‘rf’, ‘rg’] >> simp [] \\
     CONJ_TAC >| (* 2 subgoals *)
     [ (* goal 2.1 (of 2) *)
       Q.UNABBREV_TAC ‘rf’ \\
       MATCH_MP_TAC in_borel_measurable_from_Borel >> art [],
       (* goal 2.2 (of 2) *)
       Q.UNABBREV_TAC ‘rg’ \\
       MATCH_MP_TAC in_borel_measurable_from_Borel >> art [] ])
 >> DISCH_TAC
 >> Cases_on ‘z IN B’ >> fs []
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> ‘{x | f x = PosInf /\ g x = NegInf} INTER space a =
      ({x | f x = PosInf} INTER space a) INTER
      ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC (* 2 subgoals *)
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_1p =
    Know ‘{x | f x + g x = PosInf} INTER space a =
           ({x | f x = PosInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a) UNION
           ({x | f x <> PosInf /\ f x <> NegInf /\ g x = PosInf} INTER space a) UNION
           ({x | f x = PosInf /\ g x = PosInf} INTER space a)’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rpt STRIP_TAC >> rw [extreal_add_def] >| (* 3 subgoals left *)
     [ (* goal 1.1 (of 3) *)
       Cases_on ‘f x = PosInf’ >> simp []
       >- (Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       STRONG_CONJ_TAC >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       DISCH_TAC \\
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       Cases_on ‘g x’ >> fs [extreal_add_def],
       (* goal 1.2 (of 3) *)
      ‘?r. g x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def],
       (* goal 1.3 (of 3) *)
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def] ])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x = PosInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x <> PosInf} INTER space a) INTER
       ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [] ])
 >> ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x = PosInf} INTER space a =
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_2p =
    Know ‘{x | f x + g x = PosInf} INTER space a =
           ({x | f x = PosInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a) UNION
           ({x | f x <> PosInf /\ f x <> NegInf /\ g x = PosInf} INTER space a) UNION
           ({x | f x = PosInf /\ g x = PosInf} INTER space a) UNION
           ({x | f x = NegInf /\ g x = PosInf} INTER space a)’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rpt STRIP_TAC >> rw [extreal_add_def] >| (* 3 subgoals left *)
     [ (* goal 2.1 (of 3) *)
       Cases_on ‘f x = PosInf’ >> simp []
       >- (Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       Suff ‘g x = PosInf’ >- PROVE_TAC [] \\
       CCONTR_TAC \\
       Cases_on ‘f x’ >> Cases_on ‘g x’ >> fs [extreal_add_def],
       (* goal 2.2 (of 3) *)
      ‘?r. g x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def],
       (* goal 2.3 (of 3) *)
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def] ])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x = PosInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x = PosInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x <> PosInf} INTER space a) INTER
       ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [] ])
 >> ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x = PosInf} INTER space a =
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_4p =
    Know ‘{x | f x + g x = PosInf} INTER space a =
           ({x | f x = PosInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a) UNION
           ({x | f x <> PosInf /\ f x <> NegInf /\ g x = PosInf} INTER space a) UNION
           ({x | f x = PosInf /\ g x = PosInf} INTER space a) UNION
           ({x | f x = PosInf /\ g x = NegInf} INTER space a)’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rpt STRIP_TAC >> rw [extreal_add_def] >| (* 3 subgoals left *)
     [ (* goal 4.1 (of 3) *)
       Cases_on ‘f x = PosInf’ >> simp []
       >- (Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       STRONG_CONJ_TAC >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       DISCH_TAC \\
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       CCONTR_TAC \\
       Cases_on ‘g x’ >> fs [extreal_add_def],
       (* goal 4.2 (of 3) *)
      ‘?r. g x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def],
       (* goal 4.3 (of 3) *)
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def] ])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x = NegInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x = PosInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x <> PosInf} INTER space a) INTER
       ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [] ])
 >> ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x = PosInf} INTER space a =
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_2n =
    Know ‘{x | f x + g x = NegInf} INTER space a =
               ({x | f x = NegInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a) UNION
               ({x | f x <> PosInf /\ f x <> NegInf /\ g x = NegInf} INTER space a) UNION
               ({x | f x = NegInf /\ g x = NegInf} INTER space a) UNION
               ({x | f x = PosInf /\ g x = NegInf} INTER space a)’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rpt STRIP_TAC >> rw [extreal_add_def] >| (* 3 subgoals left *)
     [ (* goal 2.1 (of 3) *)
       Cases_on ‘f x = NegInf’ >> simp []
       >- (Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       Suff ‘g x = NegInf’ >- PROVE_TAC [] \\
       CCONTR_TAC \\
       Cases_on ‘f x’ >> Cases_on ‘g x’ >> fs [extreal_add_def],
       (* goal 2.2 (of 3) *)
      ‘?r. g x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def],
       (* goal 2.3 (of 3) *)
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def] ])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = PosInf /\ g x = NegInf} INTER space a =
       ({x | f x = PosInf} INTER space a) INTER
       ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x = NegInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x <> PosInf} INTER space a) INTER
       ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [] ])
 >> ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x = NegInf} INTER space a =
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_4n =
    Know ‘{x | f x + g x = NegInf} INTER space a =
               ({x | f x = NegInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a) UNION
               ({x | f x <> PosInf /\ f x <> NegInf /\ g x = NegInf} INTER space a) UNION
               ({x | f x = NegInf /\ g x = NegInf} INTER space a) UNION
               ({x | f x = NegInf /\ g x = PosInf} INTER space a)’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rpt STRIP_TAC >> rw [extreal_add_def] >| (* 3 subgoals left *)
     [ (* goal 4.1 (of 3) *)
       Cases_on ‘f x = PosInf’ >> simp []
       >- (Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       Cases_on ‘f x = NegInf’ >> simp []
       >- (Cases_on ‘g x’ >> fs [extreal_add_def]) \\
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       CCONTR_TAC \\
       Cases_on ‘g x’ >> fs [extreal_add_def],
       (* goal 4.2 (of 3) *)
      ‘?r. g x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def],
       (* goal 4.3 (of 3) *)
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def] ])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x = PosInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x = NegInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x <> PosInf} INTER space a) INTER
       ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [] ])
 >> ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x = NegInf} INTER space a =
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [] ];

val IN_MEASURABLE_BOREL_ADD_tactics_5n =
    Know ‘{x | f x + g x = NegInf} INTER space a =
           ({x | f x = NegInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a) UNION
           ({x | f x <> PosInf /\ f x <> NegInf /\ g x = NegInf} INTER space a) UNION
           ({x | f x = NegInf /\ g x = NegInf} INTER space a)’
 >- (rw [Once EXTENSION] \\
     EQ_TAC >> rpt STRIP_TAC >> rw [extreal_add_def] >| (* 3 subgoals left *)
     [ (* goal 1.1 (of 3) *)
       Cases_on ‘f x = NegInf’ >> simp []
       >- (Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       STRONG_CONJ_TAC >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def]) \\
       DISCH_TAC \\
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       Cases_on ‘g x’ >> fs [extreal_add_def],
       (* goal 1.2 (of 3) *)
      ‘?r. g x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def],
       (* goal 1.3 (of 3) *)
      ‘?r. f x = Normal r’ by METIS_TAC [extreal_cases] \\
       rw [extreal_add_def] ])
 >> Rewr'
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> reverse CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x = NegInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []
 >> CONJ_TAC
 >- (‘{x | f x = NegInf /\ g x <> PosInf /\ g x <> NegInf} INTER space a =
       ({x | f x = NegInf} INTER space a) INTER
       ({x | g x <> PosInf} INTER space a) INTER
       ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
     CONJ_TAC >|
     [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
       MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [] ])
 >> ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x = NegInf} INTER space a =
      ({x | f x <> PosInf} INTER space a) INTER
      ({x | f x <> NegInf} INTER space a) INTER
      ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [])
 >> MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art []
 >> CONJ_TAC
 >| [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art [],
      MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art [] ];

Theorem IN_MEASURABLE_BOREL_ADD' : (* cf. IN_MEASURABLE_BOREL_ADD *)
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
              (!x. x IN space a ==> (h x = f x + g x)) ==> h IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> rw [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL, IN_FUNSET, SPACE_BOREL]
 >> Suff ‘(!B. B IN subsets borel ==> PREIMAGE h (IMAGE Normal B) INTER space a IN subsets a) /\
           PREIMAGE h {PosInf} INTER space a IN subsets a /\
           PREIMAGE h {NegInf} INTER space a IN subsets a’
 >- (STRIP_TAC \\
     Know ‘PREIMAGE h {NegInf; PosInf} INTER space a IN subsets a’
     >- (‘{NegInf; PosInf} = {NegInf} UNION {PosInf}’ by SET_TAC [] >> POP_ORW \\
         rw [PREIMAGE_UNION, UNION_OVER_INTER'] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art []) \\
     DISCH_TAC \\
     fs [Borel, PREIMAGE_UNION, UNION_OVER_INTER'] (* 3 subgoals, same tactics *) \\
     MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC >> art [])
 (* PREIMAGE h (IMAGE Normal B) INTER space a IN subsets a *)
 >> STRONG_CONJ_TAC
 >- (rpt STRIP_TAC \\
     Q.PAT_X_ASSUM ‘s IN subsets Borel’ K_TAC (* useless *) \\
     rw [PREIMAGE_def] \\
     Know ‘{x | ?x'. h x = Normal x' /\ x' IN B} INTER space a =
           {x | ?r. f x + g x = Normal r /\ r IN B} INTER space a’
     >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] \\
         rename1 ‘b IN B’ >> Q.EXISTS_TAC ‘b’ >> art [] \\
         PROVE_TAC []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!x. x IN space a ==> _’ K_TAC \\
     Q.ABBREV_TAC ‘rf = real o f’ \\
     Q.ABBREV_TAC ‘rg = real o g’ \\
     (* KEY: conditioning on infinities *)
     Cases_on ‘PosInf + NegInf’ >> Cases_on ‘NegInf + PosInf’ >| (* 9 subgoals *)
     [ (* goal 1 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1,
       (* goal 2 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1,
       (* goal 3 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_3,
       (* goal 4 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1,
       (* goal 5 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1,
       (* goal 6 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_3,
       (* goal 7 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_7,
       (* goal 8 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_7,
       (* goal 9 (of 9), the most complicated one! *)
       rename1 ‘PosInf + NegInf = Normal z1’ \\
       rename1 ‘NegInf + PosInf = Normal z2’ \\
       Know ‘{x | ?r. f x + g x = Normal r /\ r IN B} INTER space a =
             if z1 IN B /\ z2 IN B then
               ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                     ?r. rf x + rg x = r /\ r IN B} INTER space a) UNION
               ({x | f x = PosInf /\ g x = NegInf} INTER space a) UNION
               ({x | f x = NegInf /\ g x = PosInf} INTER space a)
             else if z1 IN B then
               ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                     ?r. rf x + rg x = r /\ r IN B} INTER space a) UNION
               ({x | f x = PosInf /\ g x = NegInf} INTER space a)
             else if z2 IN B then
               ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                     ?r. rf x + rg x = r /\ r IN B} INTER space a) UNION
               ({x | f x = NegInf /\ g x = PosInf} INTER space a)
             else
               ({x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                     ?r. rf x + rg x = r /\ r IN B} INTER space a)’
       >- (Cases_on ‘z1 IN B’ >> Cases_on ‘z2 IN B’ >> rw [Once EXTENSION] >| (* 4 subgoal *)
           [ (* goal 9.1 (of 4) *)
             EQ_TAC >> STRIP_TAC >| (* 4 subgoals *)
             [ (* goal 9.1.1 (of 4) *)
               Cases_on ‘f x = NegInf’
               >- (simp [] >> CCONTR_TAC \\
                   Cases_on ‘g x’ >> fs [extreal_add_def]) \\
               Cases_on ‘g x = PosInf’
               >- (simp [] >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
               Cases_on ‘f x = PosInf’
               >- (simp [] >> CCONTR_TAC \\
                  ‘?y. g x = Normal y’ by METIS_TAC [extreal_cases] \\
                   fs [extreal_add_def]) \\
               Cases_on ‘g x = NegInf’
               >- (simp [] \\
                  ‘?y. f x = Normal y’ by METIS_TAC [extreal_cases] \\
                   fs [extreal_add_def]) \\
               DISJ1_TAC >> art [] \\
              ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
              ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
              ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
              ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
               fs [extreal_add_def],
               (* goal 9.1.2 (of 4) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
               rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
               simp [normal_real],
               (* goal 9.1.3 (of 4) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [],
               (* goal 9.1.4 (of 4) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] ],
             (* goal 9.2 (of 4) *)
             EQ_TAC >> STRIP_TAC >| (* 3 subgoals *)
             [ (* goal 9.2.1 (of 3) *)
               simp [] \\
               Cases_on ‘f x = PosInf’
               >- (DISJ2_TAC >> art [] \\
                   CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def]) \\
               Cases_on ‘g x = NegInf’
               >- (DISJ2_TAC >> art [] \\
                   CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
               DISJ1_TAC >> art [] \\
               STRONG_CONJ_TAC
               >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] \\
                   METIS_TAC [extreal_11]) >> DISCH_TAC \\
               STRONG_CONJ_TAC
               >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
               DISCH_TAC \\
              ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
              ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
              ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
              ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
               fs [extreal_add_def],
               (* goal 9.2.2 (of 3) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
               rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
               simp [normal_real],
               (* goal 9.2.3 (of 3) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
               rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
               simp [normal_real] ],
             (* goal 9.3 (of 4) *)
             EQ_TAC >> STRIP_TAC >| (* 3 subgoals *)
             [ (* goal 9.3.1 (of 3) *)
               Cases_on ‘f x = NegInf’
               >- (simp [] >> CCONTR_TAC \\
                   Cases_on ‘g x’ >> fs [extreal_add_def]) \\
               Cases_on ‘g x = PosInf’
               >- (simp [] >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
               DISJ1_TAC >> art [] \\
               STRONG_CONJ_TAC
               >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] \\
                   METIS_TAC [extreal_11]) >> DISCH_TAC \\
               STRONG_CONJ_TAC
               >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
               DISCH_TAC \\
              ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
              ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
              ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
              ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
               fs [extreal_add_def],
               (* goal 9.3.2 (of 3) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
               rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
               simp [normal_real],
               (* goal 9.3.3 (of 3) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] ],
             (* goal 9.4 (of 4) *)
             EQ_TAC >> STRIP_TAC >| (* 2 subgoals *)
             [ (* goal 9.4.1 (of 2) *)
               Know ‘f x <> PosInf’
               >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] \\
                   METIS_TAC [extreal_11]) >> DISCH_TAC \\
               Know ‘f x <> NegInf’
               >- (CCONTR_TAC >> Cases_on ‘g x’ >> fs [extreal_add_def] \\
                   METIS_TAC [extreal_11]) >> DISCH_TAC \\
               Know ‘g x <> PosInf’
               >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
               DISCH_TAC \\
               Know ‘g x <> NegInf’
               >- (CCONTR_TAC >> Cases_on ‘f x’ >> fs [extreal_add_def]) \\
               DISCH_TAC \\
              ‘?s. f x = Normal s’ by METIS_TAC [extreal_cases] \\
              ‘?t. g x = Normal t’ by METIS_TAC [extreal_cases] \\
              ‘rf x = s’ by rw [Abbr ‘rf’, o_DEF] \\
              ‘rg x = t’ by rw [Abbr ‘rg’, o_DEF] \\
               fs [extreal_add_def],
               (* goal 9.4.2 (of 2) *)
               simp [] >> Q.EXISTS_TAC ‘rf x + rg x’ >> art [] \\
               rw [GSYM extreal_add_def, Abbr ‘rf’, Abbr ‘rg’] \\
               simp [normal_real] ] ]) >> Rewr' \\
       (* stage work *)
       Know ‘{x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                  ?r. rf x + rg x = r /\ r IN B} INTER space a IN subsets a’
       >- (‘{x | f x <> PosInf /\ f x <> NegInf /\ g x <> PosInf /\ g x <> NegInf /\
                 ?r. rf x + rg x = r /\ r IN B} INTER space a =
             ({x | ?r. rf x + rg x = r /\ r IN B} INTER space a) INTER
             ({x | f x <> PosInf} INTER space a) INTER
             ({x | f x <> NegInf} INTER space a) INTER
             ({x | g x <> PosInf} INTER space a) INTER
             ({x | g x <> NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
           MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
           reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
           MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
           reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art []) \\
           MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
           reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_NEGINF >> art []) \\
           MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
           reverse CONJ_TAC >- (MATCH_MP_TAC IN_MEASURABLE_BOREL_NOT_POSINF >> art []) \\
           Q.ABBREV_TAC ‘h = \x. rf x + rg x’ \\
           Know ‘{x | ?r. rf x + rg x = r /\ r IN B} = PREIMAGE h B’
           >- rw [PREIMAGE_def, Abbr ‘h’] >> Rewr' \\
           Suff ‘h IN measurable a borel’ >- rw [IN_MEASURABLE] \\
           MATCH_MP_TAC in_borel_measurable_add \\
           qexistsl_tac [‘rf’, ‘rg’] >> simp [] \\
           CONJ_TAC >| (* 2 subgoals *)
           [ (* goal 9.1 (of 2) *)
             Q.UNABBREV_TAC ‘rf’ \\
             MATCH_MP_TAC in_borel_measurable_from_Borel >> art [],
             (* goal 9.2 (of 2) *)
             Q.UNABBREV_TAC ‘rg’ \\
             MATCH_MP_TAC in_borel_measurable_from_Borel >> art [] ]) \\
       DISCH_TAC \\
       Cases_on ‘z1 IN B’ >> Cases_on ‘z2 IN B’ >> fs [] >| (* 3 subgoals *)
       [ (* goal 9.1 (of 3) *)
         MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
         reverse CONJ_TAC
         >- (‘{x | f x = NegInf /\ g x = PosInf} INTER space a =
              ({x | f x = NegInf} INTER space a) INTER
              ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
             MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
             CONJ_TAC >| (* 2 subgoals *)
             [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
               MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ]) \\
         MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
        ‘{x | f x = PosInf /\ g x = NegInf} INTER space a =
           ({x | f x = PosInf} INTER space a) INTER
           ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
           MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ],
         (* goal 9.2 (of 3) *)
         MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
        ‘{x | f x = PosInf /\ g x = NegInf} INTER space a =
           ({x | f x = PosInf} INTER space a) INTER
           ({x | g x = NegInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
           MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ],
         (* goal 9.3 (of 3) *)
         MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
        ‘{x | f x = NegInf /\ g x = PosInf} INTER space a =
           ({x | f x = NegInf} INTER space a) INTER
           ({x | g x = PosInf} INTER space a)’ by SET_TAC [] >> POP_ORW \\
         MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [] \\
         CONJ_TAC >| (* 2 subgoals *)
         [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
           MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ] ] ])
 >> DISCH_TAC
 (* PREIMAGE h {PosInf} INTER space a IN subsets a *)
 >> CONJ_TAC
 >- (rw [PREIMAGE_def] \\
     Know ‘{x | h x = PosInf} INTER space a = {x | f x + g x = PosInf} INTER space a’
     >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] \\
         PROVE_TAC []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!x. x IN space a ==> _’ K_TAC \\
     (* KEY: conditioning on infinities *)
     Cases_on ‘PosInf + NegInf’ >> Cases_on ‘NegInf + PosInf’ >| (* 9 subgoals *)
     [ (* goal 1 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1p,
       (* goal 2 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_2p,
       (* goal 3 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1p,
       (* goal 4 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_4p,
       (* goal 5 (of 9) *)
       Know ‘{x | f x + g x = PosInf} INTER space a =
               ({x | f x = PosInf} INTER space a) UNION
               ({x | g x = PosInf} INTER space a)’
       >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] >| (* 5 subgoals *)
           [ (* goal 5.1 (of 5) *)
             Cases_on ‘f x’ >> Cases_on ‘g x’ >> fs [extreal_add_def],
             (* goal 5.2 (of 5) *)
             Cases_on ‘g x’ >> rw [extreal_add_def],
             (* goal 5.3 (of 5) *)
             ASM_REWRITE_TAC [],
             (* goal 5.4 (of 5) *)
             Cases_on ‘f x’ >> rw [extreal_add_def],
             (* goal 5.5 (of 5) *)
             ASM_REWRITE_TAC [] ]) >> Rewr' \\
       MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
       CONJ_TAC >|
       [ MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [],
         MATCH_MP_TAC IN_MEASURABLE_BOREL_POSINF >> art [] ],
       (* goal 6 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_4p,
       (* goal 7 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1p,
       (* goal 8 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_2p,
       (* goal 9 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_1p ])
 (* PREIMAGE h {NegInf} INTER space a IN subsets a *)
 >> (rw [PREIMAGE_def] \\
     Know ‘{x | h x = NegInf} INTER space a = {x | f x + g x = NegInf} INTER space a’
     >- (rw [Once EXTENSION] >> EQ_TAC >> rw [] \\
         PROVE_TAC []) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!x. x IN space a ==> _’ K_TAC \\
     (* KEY: conditioning on infinities *)
     Cases_on ‘PosInf + NegInf’ >> Cases_on ‘NegInf + PosInf’ >| (* 9 subgoals *)
     [ (* goal 1 (of 9) *)
       Know ‘{x | f x + g x = NegInf} INTER space a =
               ({x | f x = NegInf} INTER space a) UNION
               ({x | g x = NegInf} INTER space a)’
       >- (rw [Once EXTENSION] \\
           EQ_TAC >> rpt STRIP_TAC >> rw [extreal_add_def] >| (* 3 subgoals left *)
           [ (* goal 5.1 (of 3) *)
             Cases_on ‘f x’ >> Cases_on ‘g x’ >> fs [extreal_add_def],
             (* goal 5.2 (of 3) *)
             Cases_on ‘g x’ >> rw [extreal_add_def],
             (* goal 5.3 (of 3) *)
             Cases_on ‘f x’ >> rw [extreal_add_def] ]) >> Rewr' \\
       MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [] \\
       CONJ_TAC >|
       [ MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [],
         MATCH_MP_TAC IN_MEASURABLE_BOREL_NEGINF >> art [] ],
       (* goal 2 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_2n,
       (* goal 3 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_2n,
       (* goal 4 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_4n,
       (* goal 5 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_5n,
       (* goal 6 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_5n,
       (* goal 7 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_4n,
       (* goal 8 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_5n,
       (* goal 9 (of 9) *)
       IN_MEASURABLE_BOREL_ADD_tactics_5n ])
QED

(* NOTE: this new, natural proof is only possible after the new ‘extreal_sub’ *)
Theorem IN_MEASURABLE_BOREL_SUB' :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
              (!x. x IN space a ==> (h x = f x - g x)) ==> h IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_ADD'
 >> qexistsl_tac [‘f’, ‘\x. -g x’]
 >> rw [extreal_sub, IN_MEASURABLE_BOREL_AINV]
QED

(* ------------------------------------------------------------------------- *)
(*  Two-dimensional Borel sigma-algebra (extreal version), author: Chun Tian *)
(* ------------------------------------------------------------------------- *)

Theorem SPACE_BOREL_2D :
    space (Borel CROSS Borel) = UNIV
Proof
    REWRITE_TAC [SPACE_PROD_SIGMA, SPACE_BOREL, CROSS_UNIV]
QED

Theorem SIGMA_ALGEBRA_BOREL_2D :
    sigma_algebra (Borel CROSS Borel)
Proof
    MATCH_MP_TAC SIGMA_ALGEBRA_PROD_SIGMA
 >> rw [SPACE_BOREL, subset_class_def]
QED

Theorem CROSS_UNION_R[local] :
    !a b c. a CROSS (b UNION c) = (a CROSS b) UNION (a CROSS c)
Proof
    rw [Once EXTENSION, IN_CROSS]
 >> METIS_TAC []
QED

Theorem CROSS_UNION_L[local] :
    !a b c. (a UNION b) CROSS c = (a CROSS c) UNION (b CROSS c)
Proof
    rw [Once EXTENSION, IN_CROSS]
 >> METIS_TAC []
QED

(* Alternative definition of ‘Borel CROSS Borel’ by ‘borel CROSS borel’

   Following the same idea in "borel_2d", the extreal-based Borel sets (2D) can
   be seen as the real-based Borel sets with optional "infinity" borders.
 *)
val corner_set_tm1 =
   “{(x,y) | (x = PosInf \/ x = NegInf) /\ (y = PosInf \/ y = NegInf)}”;

val corner_set_tm2 =
   “{(PosInf,PosInf); (PosInf,NegInf); (NegInf,PosInf); (NegInf,NegInf)}”;

(* The following terms re-define ‘Borel CROSS Borel’ in terms of ‘borel’ and
  ‘borel CROSS borel’.

   The first version involves only disjoint unions, easier in proving its own
   properties.
 *)
val borel_2d_sets_tm1 =
   “{B' | ?B S Z b1 b2 b3 b4.
           B' = (IMAGE (\(x,y). (Normal x,Normal y)) B) UNION S UNION Z /\
           B IN subsets (borel CROSS borel) /\
           S = ({PosInf} CROSS (IMAGE Normal b1)) UNION
               ({NegInf} CROSS (IMAGE Normal b2)) UNION
               ((IMAGE Normal b3) CROSS {PosInf}) UNION
               ((IMAGE Normal b4) CROSS {NegInf}) /\
           b1 IN subsets borel /\ b2 IN subsets borel /\
           b3 IN subsets borel /\ b4 IN subsets borel /\
           Z SUBSET ^corner_set_tm2}”;

(* The second version is shorter, and easier in applications. *)
val borel_2d_sets_tm2 =
   “{B' | ?B S B1 B2 B3 B4.
           B' = (IMAGE (\(x,y). (Normal x,Normal y)) B) UNION S /\
           B IN subsets (borel CROSS borel) /\
           S = ({PosInf} CROSS B1) UNION
               ({NegInf} CROSS B2) UNION
               (B3 CROSS {PosInf}) UNION
               (B4 CROSS {NegInf}) /\
           B1 IN subsets Borel /\ B2 IN subsets Borel /\
           B3 IN subsets Borel /\ B4 IN subsets Borel}”;

val borel_2d_tm1 = “(univ(:extreal # extreal), ^borel_2d_sets_tm1)”;
val borel_2d_tm2 = “(univ(:extreal # extreal), ^borel_2d_sets_tm2)”;

Theorem BOREL_MEASURABLE_SETS_NORMAL :
    !b. b IN subsets borel ==> IMAGE Normal b IN subsets Borel
Proof
    rw [Borel]
 >> qexistsl_tac [‘b’, ‘{}’] >> simp []
QED

Theorem BOREL_MEASURABLE_SETS_EMPTY[simp] :
    {} IN subsets Borel
Proof
    MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY
 >> REWRITE_TAC [SIGMA_ALGEBRA_BOREL]
QED

Theorem UNION_LEFT_CONG[local] :
    !A B C. B = C ==> A UNION B = A UNION C
Proof
    SET_TAC []
QED

Theorem IN_CROSS_SING[local] :
   !x A B. x IN {A} CROSS {B} <=> x = (A,B)
Proof
    rw [IN_CROSS]
 >> Cases_on ‘x’ >> rw []
QED

(* The equivalence of borel_2d_tm1 and borel_2d_tm2 *)
Theorem BOREL_2D_lemma1[local] :
    ^borel_2d_tm1 = ^borel_2d_tm2
Proof
    Suff ‘^borel_2d_sets_tm1 = ^borel_2d_sets_tm2’ >- Rewr
 >> MATCH_MP_TAC SUBSET_ANTISYM
 >> CONJ_TAC (* 2 subgoals, same initial tactics *)
 >> RW_TAC std_ss [Once SUBSET_DEF, GSPECIFICATION]
 >> Q.EXISTS_TAC ‘B’ >> art []
 >| [ (* goal 1 (of 2) *)
      qexistsl_tac
        [‘(IMAGE Normal b1) UNION if (PosInf,NegInf) IN Z then {NegInf} else {}’,
         ‘(IMAGE Normal b2) UNION if (NegInf,PosInf) IN Z then {PosInf} else {}’,
         ‘(IMAGE Normal b3) UNION if (PosInf,PosInf) IN Z then {PosInf} else {}’,
         ‘(IMAGE Normal b4) UNION if (NegInf,NegInf) IN Z then {NegInf} else {}’] \\
      reverse CONJ_TAC
      >- (rpt STRIP_TAC \\ (* 4 subgoals, same initial tactics *)
          (MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> REWRITE_TAC [SIGMA_ALGEBRA_BOREL] \\
           CONJ_TAC >- (MATCH_MP_TAC BOREL_MEASURABLE_SETS_NORMAL >> art [])) >|
          [ Cases_on ‘(PosInf,NegInf) IN Z’ >> rw [],
            Cases_on ‘(NegInf,PosInf) IN Z’ >> rw [],
            Cases_on ‘(PosInf,PosInf) IN Z’ >> rw [],
            Cases_on ‘(NegInf,NegInf) IN Z’ >> rw [] ]) \\
      REWRITE_TAC [GSYM UNION_ASSOC] \\
      MATCH_MP_TAC UNION_LEFT_CONG \\
      REWRITE_TAC [UNION_ASSOC] \\
      rw [] \\ (* 16 subgoals, same tactics *)
      MATCH_MP_TAC SUBSET_ANTISYM \\
      RW_TAC std_ss [SUBSET_DEF, IN_UNION, IN_CROSS_SING,
                     CROSS_UNION_L, CROSS_UNION_R] >> art [] \\
      FULL_SIMP_TAC std_ss [SUBSET_DEF] \\
      Q.PAT_X_ASSUM ‘!x. x IN Z ==> _’ (MP_TAC o (Q.SPEC ‘x’)) \\
      RW_TAC std_ss [IN_INSERT, NOT_IN_EMPTY] \\
      FULL_SIMP_TAC bool_ss [],
      (* goal 2 (of 2) *)
      FULL_SIMP_TAC std_ss [Borel, UNION_EMPTY, subsets_def, GSPECIFICATION] \\
      qexistsl_tac
        [‘({PosInf} CROSS S) UNION ({NegInf} CROSS S') UNION
          (S'' CROSS {PosInf}) UNION (S''' CROSS {NegInf})’,
         ‘B'’, ‘B''’, ‘B'3'’, ‘B'4'’] >> art [] \\
      reverse CONJ_TAC
      >- (rw [SUBSET_DEF] (* 4 subgoals, same tactics *) \\
          Cases_on ‘x’ \\
          FULL_SIMP_TAC std_ss [IN_SING, IN_INSERT] \\
          REV_FULL_SIMP_TAC std_ss [NOT_IN_EMPTY, IN_SING, IN_INSERT]) \\
      MATCH_MP_TAC SUBSET_ANTISYM \\
      RW_TAC std_ss [SUBSET_DEF, IN_UNION, IN_CROSS_SING,
                     CROSS_UNION_L, CROSS_UNION_R] >> art [] ]
QED

Theorem BOREL_2D_lemma2[local] :
    sigma_algebra ^borel_2d_tm1
Proof
    rw [sigma_algebra_alt_pow] (* 4 subgoals *)
 >| [ (* goal 1 (of 4) *)
      rw [SUBSET_DEF, IN_POW],
      (* goal 2 (of 4) *)
      qexistsl_tac [‘{}’, ‘{}’, ‘{}’, ‘{}’] >> simp [CROSS_EMPTY] \\
      CONJ_TAC >- (MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
                   REWRITE_TAC [sigma_algebra_borel_2d]) \\
      MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
      REWRITE_TAC [sigma_algebra_borel],
      (* goal 3 (of 4): DIFF (hard) *)
      qexistsl_tac [‘univ(:real # real) DIFF B’,
                    ‘^corner_set_tm2 DIFF Z’,
                    ‘univ(:real) DIFF b1’,
                    ‘univ(:real) DIFF b2’,
                    ‘univ(:real) DIFF b3’,
                    ‘univ(:real) DIFF b4’] \\
      reverse CONJ_TAC (* easy part *)
      >- (REWRITE_TAC [CONJ_ASSOC] \\
          reverse CONJ_TAC >- (POP_ASSUM MP_TAC >> SET_TAC []) \\
          METIS_TAC [space_borel, space_borel_2d, SIGMA_ALGEBRA_COMPL,
                     sigma_algebra_borel, sigma_algebra_borel_2d]) \\

      MATCH_MP_TAC SUBSET_ANTISYM \\
      CONJ_TAC (* "easy" part *)
      >- (REWRITE_TAC [SUBSET_DEF] \\
          Q.X_GEN_TAC ‘z’ >> DISCH_TAC \\
          FULL_SIMP_TAC std_ss [IN_DIFF, IN_UNIV, IN_UNION] \\
          CCONTR_TAC >> FULL_SIMP_TAC std_ss [] \\

          Know ‘z NOTIN {PosInf} CROSS UNIV’
          >- (Know ‘univ(:extreal) = (IMAGE Normal b1) UNION
                                     (IMAGE Normal (UNIV DIFF b1)) UNION {PosInf; NegInf}’
              >- (rw [Once EXTENSION] >> Cases_on ‘x’ >> rw []) >> Rewr' \\
              CCONTR_TAC \\
              POP_ASSUM (MP_TAC o (REWRITE_RULE [IN_UNION, CROSS_UNION_R])) \\
              RW_TAC std_ss [] \\
              Q.PAT_X_ASSUM ‘z NOTIN ^corner_set_tm2’ MP_TAC \\
              rw [IN_CROSS] >> Cases_on ‘z’ >> fs []) \\
          Q.PAT_X_ASSUM ‘z NOTIN {PosInf} CROSS (IMAGE Normal b1)’ K_TAC \\
          Q.PAT_X_ASSUM ‘z NOTIN {PosInf} CROSS (IMAGE Normal (UNIV DIFF b1))’ K_TAC \\
          DISCH_TAC \\

          Know ‘z NOTIN {NegInf} CROSS UNIV’
          >- (Know ‘univ(:extreal) = (IMAGE Normal b2) UNION
                                     (IMAGE Normal (UNIV DIFF b2)) UNION {PosInf; NegInf}’
              >- (rw [Once EXTENSION] >> Cases_on ‘x’ >> rw []) >> Rewr' \\
              CCONTR_TAC \\
              POP_ASSUM (MP_TAC o (REWRITE_RULE [IN_UNION, CROSS_UNION_R])) \\
              RW_TAC std_ss [] \\
              Q.PAT_X_ASSUM ‘z NOTIN ^corner_set_tm2’ MP_TAC \\
              rw [IN_CROSS] >> Cases_on ‘z’ >> fs []) \\
          Q.PAT_X_ASSUM ‘z NOTIN {NegInf} CROSS (IMAGE Normal b2)’ K_TAC \\
          Q.PAT_X_ASSUM ‘z NOTIN {NegInf} CROSS (IMAGE Normal (UNIV DIFF b2))’ K_TAC \\
          DISCH_TAC \\

          Know ‘z NOTIN UNIV CROSS {PosInf}’
          >- (Know ‘univ(:extreal) = (IMAGE Normal b3) UNION
                                     (IMAGE Normal (UNIV DIFF b3)) UNION {PosInf; NegInf}’
              >- (rw [Once EXTENSION] >> Cases_on ‘x’ >> rw []) >> Rewr' \\
              CCONTR_TAC \\
              POP_ASSUM (MP_TAC o (REWRITE_RULE [IN_UNION, CROSS_UNION_L])) \\
              RW_TAC std_ss [] \\
              Q.PAT_X_ASSUM ‘z NOTIN ^corner_set_tm2’ MP_TAC \\
              rw [IN_CROSS] >> Cases_on ‘z’ >> fs []) \\
          Q.PAT_X_ASSUM ‘z NOTIN (IMAGE Normal b3) CROSS {PosInf}’ K_TAC \\
          Q.PAT_X_ASSUM ‘z NOTIN (IMAGE Normal (UNIV DIFF b3)) CROSS {PosInf}’ K_TAC \\
          DISCH_TAC \\

          Know ‘z NOTIN UNIV CROSS {NegInf}’
          >- (Know ‘univ(:extreal) = (IMAGE Normal b4) UNION
                                     (IMAGE Normal (UNIV DIFF b4)) UNION {PosInf; NegInf}’
              >- (rw [Once EXTENSION] >> Cases_on ‘x’ >> rw []) >> Rewr' \\
              CCONTR_TAC \\
              POP_ASSUM (MP_TAC o (REWRITE_RULE [IN_UNION, CROSS_UNION_L])) \\
              RW_TAC std_ss [] \\
              Q.PAT_X_ASSUM ‘z NOTIN ^corner_set_tm2’ MP_TAC \\
              rw [IN_CROSS] >> Cases_on ‘z’ >> fs []) \\
          Q.PAT_X_ASSUM ‘z NOTIN (IMAGE Normal b4) CROSS {NegInf}’ K_TAC \\
          Q.PAT_X_ASSUM ‘z NOTIN (IMAGE Normal (UNIV DIFF b4)) CROSS {NegInf}’ K_TAC \\
          DISCH_TAC \\

          Know ‘z NOTIN IMAGE (\(x,y). (Normal x,Normal y)) univ(:real # real)’
          >- (‘univ(:real # real) = B UNION (univ(:real # real) DIFF B)’ by SET_TAC [] \\
              POP_ORW >> CCONTR_TAC \\
              POP_ASSUM (MP_TAC o (REWRITE_RULE [IN_UNION, IMAGE_UNION])) \\
              PROVE_TAC []) \\
          Q.PAT_X_ASSUM ‘z NOTIN IMAGE (\(x,y). (Normal x,Normal y)) B’ K_TAC \\
          Q.PAT_X_ASSUM ‘z NOTIN
                           IMAGE (\(x,y). (Normal x,Normal y)) (univ(:real # real) DIFF B)’ K_TAC \\
          DISCH_TAC \\

          NTAC 5 (POP_ASSUM MP_TAC) >> rw [] \\
          Cases_on ‘z’ >> fs [] \\
         ‘?a. q = Normal a’ by METIS_TAC [extreal_cases] >> POP_ORW \\
         ‘?b. r = Normal b’ by METIS_TAC [extreal_cases] >> POP_ORW \\
          Q.EXISTS_TAC ‘(a,b)’ >> rw []) \\
   (* hard part of CONJ_TAC *)
      REWRITE_TAC [SUBSET_DEF] \\
      Q.X_GEN_TAC ‘z’ >> STRIP_TAC \\
      REWRITE_TAC [IN_DIFF, IN_UNIV] \\
      RW_TAC std_ss [IN_UNION] >| (* 6 subgoals *)
      [ (* goal 3.1 (of 6) *)
       ‘B = UNIV DIFF (UNIV DIFF B)’ by SET_TAC [] >> POP_ORW \\
        CCONTR_TAC \\
        FULL_SIMP_TAC std_ss [IN_IMAGE, IN_UNION, IN_DIFF, IN_UNIV, IN_CROSS, IN_SING] \\
        rename1 ‘y IN B’ >|
        [ Cases_on ‘x’  >> Cases_on ‘y’ >> fs [] >> METIS_TAC [],
          Cases_on ‘y’ >> fs [],
          Cases_on ‘y’ >> fs [],
          Cases_on ‘y’ >> fs [],
          Cases_on ‘y’ >> fs [],
          Cases_on ‘y’ >> fs [] ],
        (* goal 3.2 (of 6) *)
        CCONTR_TAC >> fs [IN_IMAGE, IN_UNION, IN_DIFF, IN_UNIV, IN_CROSS, IN_SING] \\
        rename1 ‘y IN b1’ >|
        [ Cases_on ‘x’ >> Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] >> METIS_TAC [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] ],
        (* goal 3.3 (of 6) *)
        CCONTR_TAC >> fs [IN_IMAGE, IN_UNION, IN_DIFF, IN_UNIV, IN_CROSS, IN_SING] \\
        rename1 ‘y IN b2’ >|
        [ Cases_on ‘x’ >> Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] >> METIS_TAC [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] ],
        (* goal 3.4 (of 6) *)
        CCONTR_TAC >> fs [IN_IMAGE, IN_UNION, IN_DIFF, IN_UNIV, IN_CROSS, IN_SING] \\
        rename1 ‘y IN b3’ >|
        [ Cases_on ‘x’ >> Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] >> METIS_TAC [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] ],
        (* goal 3.5 (of 6) *)
        CCONTR_TAC >> fs [IN_IMAGE, IN_UNION, IN_DIFF, IN_UNIV, IN_CROSS, IN_SING] \\
        rename1 ‘y IN b4’ >|
        [ Cases_on ‘x’ >> Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] >> METIS_TAC [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] ],
        (* goal 3.6 (of 6) *)
        CCONTR_TAC \\
        fs [SUBSET_DEF, IN_IMAGE, IN_UNION, IN_DIFF, IN_UNIV, IN_CROSS, IN_SING] \\
        Q.PAT_X_ASSUM ‘!x. x IN Z ==> _’ (MP_TAC o Q.SPEC ‘z’) >|
        [ Cases_on ‘x’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [],
          Cases_on ‘z’ >> fs [] ] ],
      (* goal 4 (of 4) *)
      POP_ASSUM (MP_TAC o (REWRITE_RULE [Once SUBSET_DEF, IN_UNIV, IN_IMAGE])) >> rw [] \\
      Know ‘!n. ?B Z b1 b2 b3 b4.
                 A n = IMAGE (\(x,y). (Normal x,Normal y)) B UNION
                       ({PosInf} CROSS IMAGE Normal b1 UNION
                        {NegInf} CROSS IMAGE Normal b2 UNION
                        IMAGE Normal b3 CROSS {PosInf} UNION
                        IMAGE Normal b4 CROSS {NegInf}) UNION Z /\
                 B IN subsets (borel CROSS borel) /\
                 b1 IN subsets borel /\
                 b2 IN subsets borel /\
                 b3 IN subsets borel /\
                 b4 IN subsets borel /\
                 Z SUBSET ^corner_set_tm2’
      >- (GEN_TAC \\
          POP_ASSUM (MP_TAC o (Q.SPEC ‘A (n :num)’)) \\
          Know ‘?x'. A n = A x'’ >- METIS_TAC [] \\
          RW_TAC std_ss []) \\
      KILL_TAC >> STRIP_TAC \\
      FULL_SIMP_TAC std_ss [SKOLEM_THM] \\
      qexistsl_tac [‘BIGUNION (IMAGE f UNIV)’,
                    ‘BIGUNION (IMAGE f' UNIV)’,
                    ‘BIGUNION (IMAGE f'2' UNIV)’,
                    ‘BIGUNION (IMAGE f'3' UNIV)’,
                    ‘BIGUNION (IMAGE f'4' UNIV)’,
                    ‘BIGUNION (IMAGE f'5' UNIV)’] \\
      rw [Once EXTENSION, IN_BIGUNION] >| (* 7 subgoals *)
      [ (* goal 4.1 (of 7) *)
        RW_TAC std_ss [Once EXTENSION, IN_BIGUNION, GSPECIFICATION] \\
        reverse EQ_TAC
        >- (RW_TAC std_ss [IN_IMAGE, IN_UNIV, IN_UNION, IN_BIGUNION_IMAGE] >| (* 6 *)
            [ (* goal 4.1.1 (of 6) *)
              rename1 ‘y IN f n’ \\
              Q.EXISTS_TAC ‘IMAGE (\(x,y). (Normal x,Normal y)) (f n) UNION
                            ({PosInf} CROSS IMAGE Normal (f'' n) UNION
                             {NegInf} CROSS IMAGE Normal (f'3' n) UNION
                             IMAGE Normal (f'4' n) CROSS {PosInf} UNION
                             IMAGE Normal (f'5' n) CROSS {NegInf}) UNION f' n’ \\
              reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
              RW_TAC std_ss [IN_IMAGE, IN_UNION] \\
              METIS_TAC [],
              (* goal 4.1.2 (of 6) *)
              POP_ASSUM MP_TAC >> rw [] \\
              rename1 ‘y IN f'' n’ \\
              Q.EXISTS_TAC ‘IMAGE (\(x,y). (Normal x,Normal y)) (f n) UNION
                            ({PosInf} CROSS IMAGE Normal (f'' n) UNION
                             {NegInf} CROSS IMAGE Normal (f'3' n) UNION
                             IMAGE Normal (f'4' n) CROSS {PosInf} UNION
                             IMAGE Normal (f'5' n) CROSS {NegInf}) UNION f' n’ \\
              reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
              rw [IN_IMAGE, IN_UNION],
              (* goal 4.1.3 (of 6) *)
              POP_ASSUM MP_TAC >> rw [] \\
              rename1 ‘y IN f'3' n’ \\
              Q.EXISTS_TAC ‘IMAGE (\(x,y). (Normal x,Normal y)) (f n) UNION
                            ({PosInf} CROSS IMAGE Normal (f'' n) UNION
                             {NegInf} CROSS IMAGE Normal (f'3' n) UNION
                             IMAGE Normal (f'4' n) CROSS {PosInf} UNION
                             IMAGE Normal (f'5' n) CROSS {NegInf}) UNION f' n’ \\
              reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
              rw [IN_IMAGE, IN_UNION],
              (* goal 4.1.4 (of 6) *)
              POP_ASSUM MP_TAC >> rw [] \\
              rename1 ‘y IN f'4' n’ \\
              Q.EXISTS_TAC ‘IMAGE (\(x,y). (Normal x,Normal y)) (f n) UNION
                            ({PosInf} CROSS IMAGE Normal (f'' n) UNION
                             {NegInf} CROSS IMAGE Normal (f'3' n) UNION
                             IMAGE Normal (f'4' n) CROSS {PosInf} UNION
                             IMAGE Normal (f'5' n) CROSS {NegInf}) UNION f' n’ \\
              reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
              rw [IN_IMAGE, IN_UNION],
              (* goal 4.1.5 (of 6) *)
              POP_ASSUM MP_TAC >> rw [] \\
              rename1 ‘y IN f'5' n’ \\
              Q.EXISTS_TAC ‘IMAGE (\(x,y). (Normal x,Normal y)) (f n) UNION
                            ({PosInf} CROSS IMAGE Normal (f'' n) UNION
                             {NegInf} CROSS IMAGE Normal (f'3' n) UNION
                             IMAGE Normal (f'4' n) CROSS {PosInf} UNION
                             IMAGE Normal (f'5' n) CROSS {NegInf}) UNION f' n’ \\
              reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
              rw [IN_IMAGE, IN_UNION],
              (* goal 4.1.6 (of 6) *)
              rename1 ‘y IN f' n’ \\
              Q.EXISTS_TAC ‘IMAGE (\(x,y). (Normal x,Normal y)) (f n) UNION
                            ({PosInf} CROSS IMAGE Normal (f'' n) UNION
                             {NegInf} CROSS IMAGE Normal (f'3' n) UNION
                             IMAGE Normal (f'4' n) CROSS {PosInf} UNION
                             IMAGE Normal (f'5' n) CROSS {NegInf}) UNION f' n’ \\
              reverse CONJ_TAC >- (Q.EXISTS_TAC ‘n’ >> REWRITE_TAC []) \\
              rw [IN_IMAGE, IN_UNION] ]) \\
        STRIP_TAC \\
        FULL_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, IN_BIGUNION_IMAGE, IN_UNIV] >| (* 6 *)
        [ (* goal 4.1.1 (of 6) *)
          METIS_TAC [],
          (* goal 4.1.2 (of 6) *)
          Suff ‘x IN {PosInf} CROSS IMAGE Normal (BIGUNION (IMAGE f'' UNIV))’ >- rw [] \\
          fs [] >> rename1 ‘y IN f'' n’ \\
          METIS_TAC [],
          (* goal 4.1.3 (of 6) *)
          Suff ‘x IN {NegInf} CROSS IMAGE Normal (BIGUNION (IMAGE f'3' UNIV))’ >- rw [] \\
          fs [] >> rename1 ‘y IN f'3' n’ \\
          METIS_TAC [],
          (* goal 4.1.4 (of 6) *)
          Suff ‘x IN IMAGE Normal (BIGUNION (IMAGE f'4' UNIV)) CROSS {PosInf}’ >- rw [] \\
          fs [] >> rename1 ‘y IN f'4' n’ \\
          METIS_TAC [],
          (* goal 4.1.5 (of 6) *)
          Suff ‘x IN IMAGE Normal (BIGUNION (IMAGE f'5' UNIV)) CROSS {NegInf}’ >- rw [] \\
          fs [] >> rename1 ‘y IN f'5' n’ \\
          METIS_TAC [],
          (* goal 4.1.6 (of 6) *)
          METIS_TAC [] ],
        (* goal 4.2 (of 7) *)
        STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT] sigma_algebra_borel_2d) \\
        FIRST_X_ASSUM MATCH_MP_TAC \\
        rw [IN_FUNSET],
        (* goal 4.3 (of 7) *)
        STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT] sigma_algebra_borel) \\
        FIRST_X_ASSUM MATCH_MP_TAC \\
        rw [IN_FUNSET],
        (* goal 4.4 (of 7) *)
        STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT] sigma_algebra_borel) \\
        FIRST_X_ASSUM MATCH_MP_TAC \\
        rw [IN_FUNSET],
        (* goal 4.5 (of 7) *)
        STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT] sigma_algebra_borel) \\
        FIRST_X_ASSUM MATCH_MP_TAC \\
        rw [IN_FUNSET],
        (* goal 4.6 (of 7) *)
        STRIP_ASSUME_TAC (REWRITE_RULE [SIGMA_ALGEBRA_ALT] sigma_algebra_borel) \\
        FIRST_X_ASSUM MATCH_MP_TAC \\
        rw [IN_FUNSET],
        (* goal 4.7 (of 7) *)
        fs [SUBSET_DEF] >> METIS_TAC [] ] ]
QED

(* |- sigma_algebra ^borel_2d_tm2 *)
Theorem BOREL_2D_lemma3[local] = REWRITE_RULE [BOREL_2D_lemma1] BOREL_2D_lemma2

Theorem BOREL_2D_lemma4[local] :
    !A B. A IN subsets borel /\ B IN subsets borel ==>
          A CROSS B IN subsets (borel CROSS borel)
Proof
    rw [prod_sigma_def]
 >> Suff ‘A CROSS B IN (prod_sets (subsets borel) (subsets borel))’
 >- (METIS_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS])
 >> rw [IN_PROD_SETS]
 >> qexistsl_tac [‘A’, ‘B’] >> art []
QED

Theorem BOREL_2D_lemma5[local] :
    !A B. A IN subsets Borel /\ B IN subsets Borel ==>
          A CROSS B IN subsets (Borel CROSS Borel)
Proof
    rw [prod_sigma_def]
 >> Suff ‘A CROSS B IN (prod_sets (subsets Borel) (subsets Borel))’
 >- (METIS_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS])
 >> rw [IN_PROD_SETS]
 >> qexistsl_tac [‘A’, ‘B’] >> art []
QED

(* Main Theorem: alternative definition of ‘Borel CROSS Borel’  *)
Theorem BOREL_2D :
    Borel CROSS Borel = ^borel_2d_tm2
Proof
    Q.ABBREV_TAC ‘S = ^borel_2d_tm2’
 >> ONCE_REWRITE_TAC [GSYM SPACE]
 >> ‘space (Borel CROSS Borel) = space S’ by rw [SPACE_BOREL_2D, Abbr ‘S’]
 >> POP_ORW
 >> Suff ‘subsets (Borel CROSS Borel) = subsets S’ >- rw []
 >> MATCH_MP_TAC SUBSET_ANTISYM
 (* stage work *)
 >> reverse CONJ_TAC
 >- (rw [Once SUBSET_DEF, Abbr ‘S’] \\
     Suff ‘{PosInf} CROSS B1 IN subsets (Borel CROSS Borel) /\
           {NegInf} CROSS B2 IN subsets (Borel CROSS Borel) /\
           B3 CROSS {PosInf} IN subsets (Borel CROSS Borel) /\
           B4 CROSS {NegInf} IN subsets (Borel CROSS Borel) /\
           IMAGE (\(x,y). (Normal x,Normal y)) B IN subsets (Borel CROSS Borel)’
     >- (STRIP_TAC \\
         rpt (MATCH_MP_TAC SIGMA_ALGEBRA_UNION >> art [SIGMA_ALGEBRA_BOREL_2D])) \\
     CONJ_TAC >- (REWRITE_TAC [prod_sigma_def] \\
                  Suff ‘{PosInf} CROSS B1 IN (prod_sets (subsets Borel) (subsets Borel))’
                  >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
                  REWRITE_TAC [IN_PROD_SETS] \\
                  qexistsl_tac [‘{PosInf}’, ‘B1’] >> art [BOREL_MEASURABLE_SETS_SING]) \\
     CONJ_TAC >- (REWRITE_TAC [prod_sigma_def] \\
                  Suff ‘{NegInf} CROSS B2 IN (prod_sets (subsets Borel) (subsets Borel))’
                  >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
                  REWRITE_TAC [IN_PROD_SETS] \\
                  qexistsl_tac [‘{NegInf}’, ‘B2’] >> art [BOREL_MEASURABLE_SETS_SING]) \\
     CONJ_TAC >- (REWRITE_TAC [prod_sigma_def] \\
                  Suff ‘B3 CROSS {PosInf} IN (prod_sets (subsets Borel) (subsets Borel))’
                  >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
                  REWRITE_TAC [IN_PROD_SETS] \\
                  qexistsl_tac [‘B3’, ‘{PosInf}’] >> art [BOREL_MEASURABLE_SETS_SING]) \\
     CONJ_TAC >- (REWRITE_TAC [prod_sigma_def] \\
                  Suff ‘B4 CROSS {NegInf} IN (prod_sets (subsets Borel) (subsets Borel))’
                  >- METIS_TAC [SIGMA_SUBSET_SUBSETS, SUBSET_DEF] \\
                  REWRITE_TAC [IN_PROD_SETS] \\
                  qexistsl_tac [‘B4’, ‘{NegInf}’] >> art [BOREL_MEASURABLE_SETS_SING]) \\
  (* the rest is hard *)
     NTAC 4 (POP_ASSUM K_TAC) (* useless assumptions *) \\
     Q.ABBREV_TAC ‘D = {IMAGE (\(x,y). (Normal x,Normal y)) Z |
                        Z IN subsets (borel CROSS borel)}’ \\
     Suff ‘D SUBSET subsets (Borel CROSS Borel)’
     >- (rw [SUBSET_DEF, Abbr ‘D’] \\
         POP_ASSUM MATCH_MP_TAC >> Q.EXISTS_TAC ‘B’ >> art []) \\
     Q.ABBREV_TAC ‘E = IMAGE (\(x,y). (Normal x,Normal y)) (UNIV CROSS UNIV)’ \\
     Know ‘E IN subsets (Borel CROSS Borel)’
     >- (Q.UNABBREV_TAC ‘E’ \\
         Know ‘IMAGE (\(x,y). (Normal x,Normal y)) (univ(:real) CROSS univ(:real)) =
                 (IMAGE Normal UNIV) CROSS (IMAGE Normal UNIV)’
         >- (rw [Once EXTENSION, IN_CROSS] \\
             Cases_on ‘x’ >> EQ_TAC >> rw [] >| (* 3 subgoals *)
             [ Cases_on ‘x'’ >> fs [],
               Cases_on ‘x'’ >> fs [],
               Q.EXISTS_TAC ‘(x',x'')’ >> rw [] ]) >> Rewr' \\
         MATCH_MP_TAC BOREL_2D_lemma5 >> REWRITE_TAC [] \\
         rw [Borel] \\
         qexistsl_tac [‘UNIV’, ‘{}’] >> rw [] \\
         REWRITE_TAC [GSYM space_borel] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_SPACE \\
         REWRITE_TAC [sigma_algebra_borel]) >> DISCH_TAC \\
  (* applying TRACE_SIGMA_ALGEBRA *)
     Q.ABBREV_TAC ‘S = {A INTER E | A IN subsets (Borel CROSS Borel)}’ \\
     Know ‘sigma_algebra (E,S)’
     >- (Q.UNABBREV_TAC ‘S’ \\
         MATCH_MP_TAC TRACE_SIGMA_ALGEBRA \\
         rw [SPACE_BOREL_2D, SUBSET_UNIV, SIGMA_ALGEBRA_BOREL_2D]) >> DISCH_TAC \\
     Suff ‘D SUBSET S’
     >- (Q.UNABBREV_TAC ‘S’ >> DISCH_TAC \\
         MATCH_MP_TAC SUBSET_TRANS \\
         Q.EXISTS_TAC ‘{A INTER E | A IN subsets (Borel CROSS Borel)}’ >> art [] \\
         rw [SUBSET_DEF] \\
         MATCH_MP_TAC SIGMA_ALGEBRA_INTER >> art [SIGMA_ALGEBRA_BOREL_2D]) \\
  (* applying borel_2d_alt_box; preparing for PREIMAGE_SIGMA *)
     Q.ABBREV_TAC ‘f = \(x,y). (real x,real y)’ \\
     Know ‘D = IMAGE (\s. PREIMAGE f s INTER E)
                     (subsets (sigma univ(:real # real) {box a b CROSS box c d | T}))’
     >- (rw [Abbr ‘D’, Once EXTENSION, PREIMAGE_def, borel_2d_alt_box] \\
         EQ_TAC >> rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           Q.EXISTS_TAC ‘Z’ >> art [] \\
           rw [Once EXTENSION, Abbr ‘E’] \\
           EQ_TAC >> rw [] >| (* 3 subgoals *)
           [ (* goal 1.1 (of 3) *)
             Cases_on ‘x'’ >> rw [Abbr ‘f’, real_normal],
             (* goal 1.2 (of 3) *)
             Q.EXISTS_TAC ‘x'’ >> rw [],
             (* goal 1.3 (of 3) *)
             Q.EXISTS_TAC ‘x'’ >> rw [] \\
             Cases_on ‘x'’ >> fs [Abbr ‘f’, real_normal] ],
           (* goal 2 (of 2) *)
           rename1 ‘z IN subsets (sigma UNIV {box a b CROSS box c d | T})’ \\
           Q.EXISTS_TAC ‘z’ >> rw [] \\
           rw [Once EXTENSION] >> EQ_TAC >> rw [] >| (* 3 subgoals *)
           [ (* goal 2.1 (of 3) *)
             Q.EXISTS_TAC ‘f x’ >> art [] \\
             Cases_on ‘x’ >> rw [Abbr ‘f’, Abbr ‘E’] \\ (* 2 subgoals, same tactics *)
             fs [IN_IMAGE] >> Cases_on ‘x’ >> fs [],
             (* goal 2.2 (of 3) *)
             Cases_on ‘x'’ >> rw [Abbr ‘f’, real_normal],
             (* goal 2.3 (of 3) *)
             Cases_on ‘x'’ >> rw [Abbr ‘f’, Abbr ‘E’] ] ]) >> Rewr' \\
  (* applying PREIMAGE_SIGMA *)
     Know ‘IMAGE (\s. PREIMAGE f s INTER E)
                 (subsets (sigma univ(:real # real) {box a b CROSS box c d | T})) =
           subsets (sigma E (IMAGE (\s. PREIMAGE f s INTER E)
                                   {box a b CROSS box c d | T}))’
     >- (MATCH_MP_TAC PREIMAGE_SIGMA \\
         rw [subset_class_def, IN_FUNSET]) >> Rewr' \\
     Q.UNABBREV_TAC ‘D’ \\
  (* applying SIGMA_SUBSET *)
    ‘S = subsets (E,S)’ by rw [] >> POP_ORW \\
    ‘E = space (E,S)’ by rw [] \\
     POP_ASSUM ((GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites) o wrap) \\
     MATCH_MP_TAC SIGMA_SUBSET >> rw [] \\
     rw [SUBSET_DEF, PREIMAGE_def, Abbr ‘S’] \\
  (* stage work *)
     Q.EXISTS_TAC ‘IMAGE (\(x,y). (Normal x,Normal y)) (box a b CROSS box c d)’ \\
     CONJ_TAC
     >- (rw [Abbr ‘f’, Once EXTENSION] >> Cases_on ‘x’ >> rw [Abbr ‘E’] \\
         EQ_TAC >> rw [] >| (* 3 subgoals *)
         [ Q.EXISTS_TAC ‘(real q,real r)’ >> Cases_on ‘x’ >> fs [],
           Cases_on ‘x’ >> Cases_on ‘x'’ >> fs [],
           Cases_on ‘x’ >> Cases_on ‘x'’ >> fs [] ]) \\
  (* final stage *)
     rw [prod_sigma_def, SPACE_BOREL, GSYM CROSS_UNIV] \\
     Suff ‘IMAGE (\(x,y). (Normal x,Normal y)) (box a b CROSS box c d) IN
           prod_sets (subsets Borel) (subsets Borel)’
     >- METIS_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS] \\
     rw [IN_PROD_SETS, box] \\
     qexistsl_tac [‘{x | Normal a < x /\ x < Normal b}’,
                   ‘{x | Normal c < x /\ x < Normal d}’] \\
     rw [BOREL_MEASURABLE_SETS, Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 5 subgoals *)
     [ (* goal 1 (of 5) *) Cases_on ‘x'’ >> fs [extreal_lt_eq],
       (* goal 2 (of 5) *) Cases_on ‘x'’ >> fs [extreal_lt_eq],
       (* goal 3 (of 5) *) Cases_on ‘x'’ >> fs [extreal_lt_eq],
       (* goal 4 (of 5) *) Cases_on ‘x'’ >> fs [extreal_lt_eq],
       (* goal 5 (of 5) *)
       Cases_on ‘x’ >> fs [] \\
       Know ‘q <> PosInf /\ q <> NegInf’
       >- (CONJ_TAC >> CCONTR_TAC >> fs [lt_infty]) >> STRIP_TAC \\
       Know ‘r <> PosInf /\ r <> NegInf’
       >- (CONJ_TAC >> CCONTR_TAC >> fs [lt_infty]) >> STRIP_TAC \\
       Q.EXISTS_TAC ‘(real q,real r)’ >> rw [normal_real] \\ (* 4 subgoals, same tactics *)
       RW_TAC std_ss [GSYM extreal_lt_eq, normal_real] ])
 (* stage work (tedious part) *)
 >> REWRITE_TAC [prod_sigma_def]
 >> ‘space Borel CROSS space Borel = space S’ by rw [Abbr ‘S’, SPACE_BOREL, CROSS_UNIV]
 >> POP_ORW
 >> MATCH_MP_TAC SIGMA_SUBSET
 (* applying BOREL_2D_lemma3 *)
 >> CONJ_TAC >- rw [BOREL_2D_lemma3, Abbr ‘S’]
 >> ‘{} IN subsets borel’ by (MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY \\
                              REWRITE_TAC [sigma_algebra_borel])
 >> rw [Once SUBSET_DEF, IN_PROD_SETS, Borel, Abbr ‘S’] (* 16 subgoals *)
 >> ‘B CROSS B' IN subsets (borel CROSS borel)’
      by (MATCH_MP_TAC BOREL_2D_lemma4 >> art [])
 >> Q.EXISTS_TAC ‘B CROSS B'’
 >| [ (* goal 1 (of 16) *)
      qexistsl_tac [‘{}’, ‘{}’, ‘{}’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] \\
      rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
      Cases_on ‘x’ >> rw [] \\
      EQ_TAC >> rw [] >| (* 3 subgoals *)
      [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
        rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
        rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
      (* goal 2 (of 16) *)
      qexistsl_tac [‘{}’, ‘{}’, ‘{}’, ‘IMAGE Normal B’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 2 subgoals *)
      [ (* goal 2.1 (of 2) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 2.3 (of 2) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 3 (of 16) *)
      qexistsl_tac [‘{}’, ‘{}’, ‘IMAGE Normal B’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 2 subgoals *)
      [ (* goal 3.1 (of 2) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 3.3 (of 2) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 4 (of 16) *)
      qexistsl_tac [‘{}’, ‘{}’, ‘IMAGE Normal B’, ‘IMAGE Normal B’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 3 subgoals *)
      [ (* goal 4.1 (of 3) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 4.2 (of 3) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [],
        (* goal 4.3 (of 3) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 5 (of 16) *)
      qexistsl_tac [‘{}’, ‘IMAGE Normal B'’, ‘{}’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 2 subgoals *)
      [ (* goal 5.1 (of 2) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 5.2 (of 2) *)
        qexistsl_tac [‘B'’, ‘{}’] >> rw [] ],
      (* goal 6 (of 16) *)
      qexistsl_tac [‘{}’, ‘(IMAGE Normal B') UNION {NegInf}’, ‘{}’, ‘IMAGE Normal B’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 3 subgoals *)
      [ (* goal 6.1 (of 3) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 6.2 (of 3) *)
        qexistsl_tac [‘B'’, ‘{NegInf}’] >> rw [],
        (* goal 6.3 (of 3) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 7 (of 16) *)
      qexistsl_tac [‘{}’, ‘(IMAGE Normal B') UNION {PosInf}’, ‘IMAGE Normal B’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 3 subgoals *)
      [ (* goal 7.1 (of 3) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 7.2 (of 3) *)
        qexistsl_tac [‘B'’, ‘{PosInf}’] >> rw [],
        (* goal 7.3 (of 3) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 8 (of 16) *)
      qexistsl_tac [‘{}’, ‘(IMAGE Normal B') UNION {NegInf; PosInf}’,
                    ‘IMAGE Normal B’, ‘IMAGE Normal B’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 4 subgoals *)
      [ (* goal 8.1 (of 4) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 8.2 (of 4) *)
        qexistsl_tac [‘B'’, ‘{NegInf;PosInf}’] >> rw [],
        (* goal 8.3 (of 4) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [],
        (* goal 8.4 (of 4) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 9 (of 16) *)
      qexistsl_tac [‘IMAGE Normal B'’, ‘{}’, ‘{}’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 2 subgoals *)
      [ (* goal 9.1 (of 2) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 9.2 (of 2) *)
        qexistsl_tac [‘B'’, ‘{}’] >> rw [] ],
      (* goal 10 (of 16) *)
      qexistsl_tac [‘(IMAGE Normal B') UNION {NegInf}’, ‘{}’,
                    ‘{}’, ‘IMAGE Normal B’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 3 subgoals *)
      [ (* goal 10.1 (of 3) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 10.3 (of 3) *)
        qexistsl_tac [‘B'’, ‘{NegInf}’] >> rw [],
        (* goal 10.3 (of 3) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 11 (of 16) *)
      qexistsl_tac [‘(IMAGE Normal B') UNION {PosInf}’, ‘{}’,
                    ‘IMAGE Normal B’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 3 subgoals *)
      [ (* goal 11.1 (of 3) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 11.2 (of 3) *)
        qexistsl_tac [‘B'’, ‘{PosInf}’] >> rw [],
        (* goal 11.3 (of 3) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 12 (of 16) *)
      qexistsl_tac [‘(IMAGE Normal B') UNION {NegInf;PosInf}’, ‘{}’,
                    ‘IMAGE Normal B’, ‘IMAGE Normal B’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 4 subgoals *)
      [ (* goal 12.1 (of 4) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 12.2 (of 4) *)
        qexistsl_tac [‘B'’, ‘{NegInf;PosInf}’] >> rw [],
        (* goal 12.3 (of 4) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [],
        (* goal 12.4 (of 4) *)
        qexistsl_tac [‘B’, ‘{}’] >> rw [] ],
      (* goal 13 (of 16) *)
      qexistsl_tac [‘IMAGE Normal B'’, ‘IMAGE Normal B'’, ‘{}’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 3 subgoals *)
      [ (* goal 13.1 (of 3) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 13.2 (of 3) *)
        qexistsl_tac [‘B'’, ‘{}’] >> rw [],
        (* goal 13.3 (of 3) *)
        qexistsl_tac [‘B'’, ‘{}’] >> rw [] ],
      (* goal 14 (of 16) *)
      qexistsl_tac [‘(IMAGE Normal B') UNION {NegInf}’,
                    ‘(IMAGE Normal B') UNION {NegInf}’,
                    ‘{}’, ‘(IMAGE Normal B) UNION {NegInf;PosInf}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 4 subgoals *)
      [ (* goal 14.1 (of 4) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 14.2 (of 4) *)
        qexistsl_tac [‘B'’, ‘{NegInf}’] >> rw [],
        (* goal 14.3 (of 4) *)
        qexistsl_tac [‘B'’, ‘{NegInf}’] >> rw [],
        (* goal 14.4 (of 4) *)
        qexistsl_tac [‘B’, ‘{NegInf;PosInf}’] >> rw [] ],
      (* goal 15 (of 16) *)
      qexistsl_tac [‘(IMAGE Normal B') UNION {PosInf}’,
                    ‘(IMAGE Normal B') UNION {PosInf}’,
                    ‘(IMAGE Normal B) UNION {NegInf;PosInf}’, ‘{}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 4 subgoals *)
      [ (* goal 15.1 (of 4) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 15.2 (of 4) *)
        qexistsl_tac [‘B'’, ‘{PosInf}’] >> rw [],
        (* goal 15.3 (of 4) *)
        qexistsl_tac [‘B'’, ‘{PosInf}’] >> rw [],
        (* goal 15.4 (of 4) *)
        qexistsl_tac [‘B’, ‘{NegInf;PosInf}’] >> rw [] ],
      (* goal 16 (of 16) *)
      qexistsl_tac [‘(IMAGE Normal B') UNION {NegInf;PosInf}’,
                    ‘(IMAGE Normal B') UNION {NegInf;PosInf}’,
                    ‘(IMAGE Normal B) UNION {NegInf;PosInf}’,
                    ‘(IMAGE Normal B) UNION {NegInf;PosInf}’] \\
      rw [UNION_EMPTY, CROSS_EMPTY] >| (* 5 subgoals *)
      [ (* goal 16.1 (of 5) *)
        rw [Once EXTENSION, IN_IMAGE, IN_CROSS] \\
        Cases_on ‘x’ >> rw [] \\
        EQ_TAC >> rw [] >| (* 3 subgoals *)
        [ Q.EXISTS_TAC ‘(x',x'')’ >> rw [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [],
          rename1 ‘FST z IN B’ >> Cases_on ‘z’ >> fs [] ],
        (* goal 16.2 (of 5) *)
        qexistsl_tac [‘B'’, ‘{NegInf;PosInf}’] >> rw [],
        (* goal 16.3 (of 5) *)
        qexistsl_tac [‘B'’, ‘{NegInf;PosInf}’] >> rw [],
        (* goal 16.4 (of 5) *)
        qexistsl_tac [‘B’, ‘{NegInf;PosInf}’] >> rw [],
        (* goal 16.5 (of 5) *)
        qexistsl_tac [‘B’, ‘{NegInf;PosInf}’] >> rw [] ] ]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_I :
    (\x. x) IN measurable Borel Borel
Proof
    ‘(\x :extreal. x) = I’ by METIS_TAC [I_THM]
 >> POP_ORW
 >> MATCH_MP_TAC MEASURABLE_I
 >> REWRITE_TAC [SIGMA_ALGEBRA_BOREL]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_ABS :
    abs IN measurable Borel Borel
Proof
    MATCH_MP_TAC IN_MEASURABLE_BOREL_ABS
 >> Q.EXISTS_TAC ‘\x. x’
 >> rw [SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_I, SPACE_BOREL]
QED

(* NOTE: ‘Borel’ here can be generalized to any sigma_algebra

   cf. stochastic_processTheory.random_variable_sigma_of_dimension for a generalization
       of this theorem to arbitrary finite dimensions.
 *)
Theorem IN_MEASURABLE_BOREL_2D_VECTOR :
    !a X Y. sigma_algebra a /\
            X IN measurable a Borel /\ Y IN measurable a Borel ==>
            (\x. (X x,Y x)) IN measurable a (Borel CROSS Borel)
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘g = \x. (X x,Y x)’
 >> simp [IN_MEASURABLE, IN_FUNSET, SPACE_PROD_SIGMA, SPACE_BOREL]
 >> ‘sigma_algebra (Borel CROSS Borel)’ by PROVE_TAC [SIGMA_ALGEBRA_BOREL_2D]
 (* stage work *)
 >> Suff ‘IMAGE (\s. PREIMAGE g s INTER space a)
                (subsets (Borel CROSS Borel)) SUBSET subsets a’
 >- (rw [IN_IMAGE, SUBSET_DEF] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘s’ >> art [])
 >> Know ‘IMAGE (\s. PREIMAGE g s INTER space a)
                (prod_sets (subsets Borel) (subsets Borel)) SUBSET subsets a’
 >- (Q.UNABBREV_TAC ‘g’ \\
     rw [IN_IMAGE, SUBSET_DEF, IN_PROD_SETS] \\
     simp [PREIMAGE_CROSS, o_DEF, ETA_AX] \\
    ‘PREIMAGE X t INTER PREIMAGE Y u INTER space a =
       (PREIMAGE X t INTER space a) INTER (PREIMAGE Y u INTER space a)’
      by SET_TAC [] >> POP_ORW \\
     MATCH_MP_TAC SIGMA_ALGEBRA_INTER \\
     fs [IN_MEASURABLE])
 >> DISCH_TAC
 (* applying SIGMA_SUBSET *)
 >> Know ‘subsets (sigma (space a)
                         (IMAGE (\s. PREIMAGE g s INTER space a)
                                (prod_sets (subsets Borel) (subsets Borel)))) SUBSET
          subsets a’
 >- (MATCH_MP_TAC SIGMA_SUBSET >> rw [])
 >> POP_ASSUM K_TAC
 >> DISCH_TAC
 (* stage work *)
 >> Suff ‘IMAGE (\s. PREIMAGE g s INTER space a) (subsets (Borel CROSS Borel)) =
          subsets (sigma (space a)
                         (IMAGE (\s. PREIMAGE g s INTER space a)
                                (prod_sets (subsets Borel) (subsets Borel))))’
 >- (Rewr' >> art [])
 >> REWRITE_TAC [prod_sigma_def]
 (* applying PREIMAGE_SIGMA *)
 >> MATCH_MP_TAC PREIMAGE_SIGMA
 >> rw [IN_FUNSET, IN_CROSS, SPACE_BOREL, subset_class_def]
 >> MATCH_MP_TAC SUBSET_CROSS
 >> REWRITE_TAC [SUBSET_UNIV]
QED

Theorem IN_MEASURABLE_BOREL_2D_FUNCTION :
    !a X Y f. sigma_algebra a /\
              X IN measurable a Borel /\ Y IN measurable a Borel /\
              f IN measurable (Borel CROSS Borel) Borel ==>
              (\x. f (X x,Y x)) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘g = \x. (X x,Y x)’
 >> ‘(\x. f (X x,Y x)) = f o g’ by rw [Abbr ‘g’, o_DEF] >> POP_ORW
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘Borel CROSS Borel’ >> art []
 >> Q.UNABBREV_TAC ‘g’
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_2D_VECTOR >> art []
QED

Theorem IN_MEASURABLE_BOREL_2D_MUL :
    (\(x,y). x * y) IN measurable (Borel CROSS Borel) Borel
Proof
    simp [IN_MEASURABLE, SIGMA_ALGEBRA_BOREL_2D, SPACE_BOREL, IN_FUNSET,
          SIGMA_ALGEBRA_BOREL, SPACE_PROD_SIGMA, SYM CROSS_UNIV]
 >> Q.ABBREV_TAC ‘f = \(x :extreal,y). x * y’
 >> Suff ‘IMAGE (\s. PREIMAGE f s INTER (UNIV CROSS UNIV)) (subsets Borel) SUBSET
          subsets (Borel CROSS Borel)’
 >- (rw [SUBSET_DEF, IN_IMAGE] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘s’ \\
     rw [Once EXTENSION, SYM CROSS_UNIV])
 >> Q.ABBREV_TAC ‘Z = univ(:extreal) CROSS univ(:extreal)’
 >> GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) empty_rewrites [Borel_eq_gr]
 >> Q.ABBREV_TAC ‘sts = IMAGE (\a. {x | Normal a < x}) univ(:real)’
 (* applying PREIMAGE_SIGMA *)
 >> Know ‘IMAGE (\s. PREIMAGE f s INTER Z) (subsets (sigma UNIV sts)) =
          subsets (sigma Z (IMAGE (\s. PREIMAGE f s INTER Z) sts))’
 >- (MATCH_MP_TAC PREIMAGE_SIGMA >> rw [IN_FUNSET, subset_class_def])
 >> Rewr'
 >> Suff ‘(IMAGE (\s. PREIMAGE f s INTER Z) sts) SUBSET
            subsets (Borel CROSS Borel)’
 >- (DISCH_THEN (MP_TAC o (Q.SPEC ‘Z’) o (MATCH_MP SIGMA_MONOTONE)) \\
     Suff ‘sigma Z (subsets (Borel CROSS Borel)) = Borel CROSS Borel’ >- rw [] \\
     Know ‘Z = space (Borel CROSS Borel)’
     >- rw [Abbr ‘Z’, prod_sigma_def, SPACE_SIGMA, SPACE_BOREL] >> Rewr' \\
     MATCH_MP_TAC SIGMA_STABLE \\
     REWRITE_TAC [SIGMA_ALGEBRA_BOREL_2D])
 >> rw [SUBSET_DEF, Abbr ‘sts’, Abbr ‘Z’, SYM CROSS_UNIV]
 (* start using ‘*’ *)
 >> rw [Abbr ‘f’, PREIMAGE_def]
 >> ‘{x | Normal a < (\(x,y). x * y) x} = {(x,y) | Normal a < x * y}’ by SET_TAC []
 >> POP_ORW
 (* applying BOREL_2D, then case analysis on ‘a’ *)
 >> rw [BOREL_2D]
 >> Cases_on ‘0 <= a’
 >- (qexistsl_tac [‘{(x,y) | a < x * y}’,
                   ‘{y | 0 < y}’, ‘{y | y < 0}’, ‘{x | 0 < x}’, ‘{x | x < 0}’] \\
     rw [BOREL_MEASURABLE_SETS]
     >- (rw [Once EXTENSION] >> Cases_on ‘x’ \\
         EQ_TAC >> rw [GSYM extreal_of_num_def] >| (* 6 subgoals *)
         [ (* goal 1 (of 6) *)
           Cases_on ‘q’ >> Cases_on ‘r’ >> Cases_on ‘0 < r'’ \\
           rw [extreal_mul_def, extreal_of_num_def, extreal_lt_eq, lt_infty] \\
           fs [extreal_mul_def, lt_infty, extreal_of_num_def] >| (* 8 subgoals *)
           [ (* goal 1.1 (of 8) *)
            ‘r' <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] >> fs [lt_infty, extreal_of_num_def],
             (* goal 1.2 (of 8) *)
            ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
             >- fs [real_lte, extreal_lt_eq] \\
             fs [lt_infty, extreal_of_num_def],
             (* goal 1.3 (of 8) *)
            ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
             >- fs [real_lte, extreal_lt_eq] \\
             fs [lt_infty, extreal_of_num_def],
             (* goal 1.4 (of 8) *)
            ‘r' <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] >> fs [lt_infty, extreal_of_num_def],
             (* goal 1.5 (of 8) *)
            ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
             >- fs [real_lte, extreal_lt_eq] \\
             fs [lt_infty, extreal_of_num_def],
             (* goal 1.6 (of 8) *)
            ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
             >- fs [real_lte, extreal_lt_eq] \\
             fs [lt_infty, extreal_of_num_def],
             (* goal 1.7 (of 8) *)
             Q.EXISTS_TAC ‘(r',r'')’ >> rw [] >> fs [extreal_lt_eq],
             (* goal 1.8 (of 8) *)
             Q.EXISTS_TAC ‘(r',r'')’ >> rw [] >> fs [extreal_lt_eq] ],
           (* goal 2 (of 6) *)
           fs [extreal_mul_def, extreal_lt_eq] \\
           rw [extreal_of_num_def, extreal_lt_eq],
           (* goal 3 (of 6) *)
           rw [mul_infty, lt_infty],
           (* goal 4 (of 6) *)
           rw [mul_infty', lt_infty],
           (* goal 5 (of 6) *)
           rw [mul_infty, lt_infty],
           (* goal 6 (of 6) *)
           rw [mul_infty', lt_infty] ]) \\
      rw [borel_2d] \\
      Suff ‘{(x,y) | a < x * y} IN {s | open_in (mtop mr2) s}’
      >- METIS_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS] \\
      REWRITE_TAC [hyperbola_open_in_mr2])
 >> qexistsl_tac [‘{(x,y) | a < x * y}’,
                  ‘{y | 0 <= y}’, ‘{y | y <= 0}’, ‘{x | 0 <= x}’, ‘{x | x <= 0}’]
 >> rw [BOREL_MEASURABLE_SETS]
 >- (rw [Once EXTENSION] >> Cases_on ‘x’ \\
     EQ_TAC >> rw [GSYM extreal_of_num_def] >| (* 6 subgoals *)
     [ (* goal 1 (of 6) *)
       Cases_on ‘q’ >> Cases_on ‘r’ >> Cases_on ‘0 < r'’ \\
       rw [extreal_mul_def, extreal_of_num_def, extreal_lt_eq, lt_infty, le_infty] \\
       fs [extreal_mul_def, lt_infty, le_infty, extreal_of_num_def] >| (* 10 subgoals *)
       [ (* goal 1 (of 10) *)
        ‘r' <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] >> fs [le_infty, lt_infty, extreal_of_num_def],
         (* goal 2 (of 10) *)
        ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
         >- fs [real_lte, extreal_lt_eq, extreal_le_eq] \\
         fs [lt_infty, extreal_of_num_def, extreal_le_eq, real_lte],
         (* goal 3 (of 10) *)
        ‘r' <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         fs [le_infty, lt_infty, extreal_of_num_def, extreal_le_eq] \\
         DISJ2_TAC >> MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
         (* goal 4 (of 10) *)
        ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
         >- fs [real_lte, extreal_lt_eq, extreal_le_eq] \\
         fs [lt_infty, extreal_of_num_def, extreal_le_eq, real_lte],
         (* goal 5 (of 10) *)
        ‘r' <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         fs [le_infty, lt_infty, extreal_of_num_def, extreal_le_eq],
         (* goal 6 (of 10) *)
        ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
         >- fs [real_lte, extreal_lt_eq, extreal_le_eq] \\
         fs [lt_infty, extreal_of_num_def, extreal_le_eq, real_lte],
         (* goal 7 (of 10) *)
        ‘r' <> 0’ by PROVE_TAC [REAL_LT_IMP_NE] \\
         fs [le_infty, lt_infty, extreal_of_num_def, extreal_le_eq] \\
         DISJ2_TAC >> MATCH_MP_TAC REAL_LT_IMP_LE >> art [],
         (* goal 8 (of 10) *)
        ‘r' = 0 \/ (r' <> 0 /\ r' < 0)’ by PROVE_TAC [REAL_LT_TOTAL]
         >- fs [real_lte, extreal_lt_eq, extreal_le_eq] \\
         fs [lt_infty, extreal_of_num_def, extreal_le_eq, real_lte],
         (* goal 9 (of 10) *)
         Q.EXISTS_TAC ‘(r',r'')’ >> rw [] >> fs [extreal_lt_eq],
         (* goal 10 (of 10) *)
         Q.EXISTS_TAC ‘(r',r'')’ >> rw [] >> fs [extreal_lt_eq] ],
       (* goal 2 (of 6) *)
       fs [extreal_mul_def, extreal_lt_eq],
       (* goal 3 (of 6) *)
      ‘r = 0 \/ 0 < r’ by PROVE_TAC [le_lt]
       >- (rw [mul_rzero, extreal_of_num_def, extreal_lt_eq] \\
           fs [real_lte]) \\
       rw [mul_infty, lt_infty],
       (* goal 4 (of 6) *)
      ‘r = 0 \/ r < 0’ by PROVE_TAC [le_lt]
       >- (rw [mul_rzero, extreal_of_num_def, extreal_lt_eq] \\
           fs [real_lte]) \\
       rw [mul_infty', lt_infty],
       (* goal 5 (of 6) *)
      ‘q = 0 \/ 0 < q’ by PROVE_TAC [le_lt]
       >- (rw [mul_rzero, extreal_of_num_def, extreal_lt_eq] \\
           fs [real_lte]) \\
       rw [mul_infty, lt_infty],
       (* goal 6 (of 6) *)
      ‘q = 0 \/ q < 0’ by PROVE_TAC [le_lt]
       >- (rw [mul_rzero, extreal_of_num_def, extreal_lt_eq] \\
           fs [real_lte]) \\
       rw [mul_infty', lt_infty] ])
 >> rw [borel_2d]
 >> Suff ‘{(x,y) | a < x * y} IN {s | open_in (mtop mr2) s}’
 >- METIS_TAC [SUBSET_DEF, SIGMA_SUBSET_SUBSETS]
 >> REWRITE_TAC [hyperbola_open_in_mr2]
QED

Theorem IN_MEASURABLE_BOREL_TIMES' :
    !a f g h. sigma_algebra a /\ f IN measurable a Borel /\ g IN measurable a Borel /\
             (!x. x IN space a ==> h x = f x * g x) ==> h IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘ff = \(x :extreal,y). x * y’
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_EQ'
 >> Q.EXISTS_TAC ‘\x. ff (f x,g x)’ >> rw []
 >- rw [Abbr ‘ff’]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_2D_FUNCTION >> art []
 >> rw [Abbr ‘ff’, IN_MEASURABLE_BOREL_2D_MUL]
QED

Theorem IN_MEASURABLE_BOREL_TIMES :
  !m f g h.
     measure_space m /\
     f IN measurable (m_space m, measurable_sets m) Borel /\
     g IN measurable (m_space m, measurable_sets m) Borel /\
     (!x. x IN m_space m ==> (h x = f x * g x)) ==>
     h IN measurable (m_space m, measurable_sets m) Borel
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPECL [‘(m_space m,measurable_sets m)’, ‘f’, ‘g’, ‘h’]
                    IN_MEASURABLE_BOREL_TIMES')
 >> fs [measure_space_def]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_CONST :
    !c. (\x. c) IN measurable Borel Borel
Proof
    Q.X_GEN_TAC ‘c’
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CONST
 >> Q.EXISTS_TAC ‘c’
 >> rw [SIGMA_ALGEBRA_BOREL]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_AINV :
    extreal_ainv IN measurable Borel Borel
Proof
    Know ‘$extreal_ainv = \x. -1 * x’
 >- (rw [FUN_EQ_THM, Once neg_minus1])
 >> Rewr'
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_CMUL
 >> qexistsl_tac [‘\x. x’, ‘-1’]
 >> rw [SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_I, SPACE_BOREL,
        extreal_of_num_def, extreal_ainv_def, extreal_mul_def]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_MAX :
    !c. (\x. max x c) IN measurable Borel Borel
Proof
    Q.X_GEN_TAC ‘c’
 >> MATCH_MP_TAC
      (BETA_RULE (Q.SPECL [‘Borel’, ‘\x :extreal. x’, ‘\x :extreal. c’]
                          (INST_TYPE [“:'a” |-> “:extreal”] IN_MEASURABLE_BOREL_MAX)))
 >> rw [IN_MEASURABLE_BOREL_BOREL_I, IN_MEASURABLE_BOREL_BOREL_CONST,
        SIGMA_ALGEBRA_BOREL]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_MIN :
    !c. (\x. min x c) IN measurable Borel Borel
Proof
    Q.X_GEN_TAC ‘c’
 >> MATCH_MP_TAC
      (BETA_RULE (Q.SPECL [‘Borel’, ‘\x :extreal. x’, ‘\x :extreal. c’]
                          (INST_TYPE [“:'a” |-> “:extreal”] IN_MEASURABLE_BOREL_MIN)))
 >> rw [IN_MEASURABLE_BOREL_BOREL_I, IN_MEASURABLE_BOREL_BOREL_CONST,
        SIGMA_ALGEBRA_BOREL]
QED

Theorem IN_MEASURABLE_BOREL_BOREL_POW :
    !n. (\x. x pow n) IN measurable Borel Borel
Proof
    Induct_on ‘n’
 >- REWRITE_TAC [pow_0, IN_MEASURABLE_BOREL_BOREL_CONST]
 >> REWRITE_TAC [extreal_pow]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_TIMES'
 >> qexistsl_tac [‘\x. x’, ‘\x. x pow n’]
 >> rw [SPACE_BOREL, SIGMA_ALGEBRA_BOREL, IN_MEASURABLE_BOREL_BOREL_I]
QED

(* Improved without ‘f x <> NegInf /\ f x <> PosInf’ (and also ‘sigma_algebra a’) *)
Theorem IN_MEASURABLE_BOREL_POW :
    !n a f. f IN measurable a Borel ==> (\x. (f x) pow n) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> ‘(\x. f x pow n) = (\x. x pow n) o f’ by rw [o_DEF] >> POP_ORW
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘Borel’
 >> rw [IN_MEASURABLE_BOREL_BOREL_POW]
QED

(* IMPORTANT: every mono-increasing function is Borel measurable!

   This is also Problem 8.21 of [1, p.70], the easy part!
 *)
Theorem IN_MEASURABLE_BOREL_BOREL_MONO_INCREASING :
    !f. (!x y. x <= y ==> f x <= f y) ==> f IN measurable Borel Borel
Proof
    rpt STRIP_TAC
 >> ASSUME_TAC SIGMA_ALGEBRA_BOREL
 >> rw [IN_MEASURABLE_BOREL, IN_FUNSET, SPACE_BOREL]
 >> Q.ABBREV_TAC ‘A = {x | f x < Normal c}’
 (* step 1 *)
 >> Cases_on ‘!y. f y < Normal c’
 >- rw [Abbr ‘A’, GSYM SPACE_BOREL, SIGMA_ALGEBRA_SPACE]
 >> POP_ASSUM (STRIP_ASSUME_TAC o (SIMP_RULE bool_ss [extreal_lt_def]))
 (* step 2 *)
 >> Cases_on ‘!x. Normal c <= f x’
 >- (Know ‘A = EMPTY’
     >- (rw [Abbr ‘A’, NOT_IN_EMPTY, Once EXTENSION, extreal_lt_def]) >> Rewr' \\
     MATCH_MP_TAC SIGMA_ALGEBRA_EMPTY >> art [])
 >> fs [GSYM extreal_lt_def]
 >> Q.PAT_X_ASSUM ‘sigma_algebra Borel’ K_TAC (* not needed *)
 (* step 3 *)
 >> Cases_on ‘?z. f z = Normal c’
 >- (FULL_SIMP_TAC bool_ss [] (* but z may not be unique! *) \\
     Q.ABBREV_TAC ‘z0 = inf {x | f x = Normal c}’ \\
     Cases_on ‘f z0 = Normal c’ >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Suff ‘A = {x | x < z0}’ >- rw [BOREL_MEASURABLE_SETS] \\
       rw [Abbr ‘A’, Once EXTENSION] \\
       rename1 ‘f t < Normal c <=> t < z0’ \\
       EQ_TAC >> rw [Abbr ‘z0’] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         SPOSE_NOT_THEN (STRIP_ASSUME_TAC o (REWRITE_RULE [extreal_lt_def])) \\
         POP_ASSUM (MP_TAC o (REWRITE_RULE [inf_le'])) \\
         rw [GSYM extreal_lt_def] \\
         Q.PAT_X_ASSUM ‘Normal c <= f y’ K_TAC (* useless *) \\
         Q.PAT_X_ASSUM ‘f x < Normal c’  K_TAC (* useless *) \\
         Q.EXISTS_TAC ‘inf {x | f x = Normal c}’ \\
         reverse CONJ_TAC >- METIS_TAC [extreal_lt_def] \\
         Q.X_GEN_TAC ‘y’ >> rw [inf_le'],
         (* goal 1.2 (of 2) *)
         Q.PAT_X_ASSUM ‘f z = Normal c’ K_TAC (* useless *) \\
         Q.PAT_ASSUM ‘f _ = Normal c’ (ONCE_REWRITE_TAC o wrap o SYM) \\
         REWRITE_TAC [lt_le] \\
         CONJ_TAC >- (FIRST_X_ASSUM MATCH_MP_TAC \\
                      MATCH_MP_TAC lt_imp_le >> art []) \\
         SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE []) \\
         Q.PAT_X_ASSUM ‘f _ = Normal c’ (fs o wrap) \\
         Q.PAT_X_ASSUM ‘Normal c <= f y’ K_TAC (* useless *) \\
         Q.PAT_X_ASSUM ‘f x < Normal c’  K_TAC (* useless *) \\
         Suff ‘inf {x | f x = Normal c} <= t’ >- METIS_TAC [extreal_lt_def] \\
         Q.PAT_X_ASSUM ‘t < inf _’       K_TAC (* just used *) \\
         rw [inf_le'] ],
       (* goal 2 (of 2) *)
       Suff ‘A = {x | x <= z0}’ >- rw [BOREL_MEASURABLE_SETS] \\
       rw [Abbr ‘A’, Once EXTENSION] \\
       rename1 ‘f t < Normal c <=> t <= z0’ \\
       EQ_TAC >> rw [Abbr ‘z0’, le_inf'] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         MATCH_MP_TAC lt_imp_le >> METIS_TAC [extreal_lt_def],
         (* goal 2.2 (of 2) *)
         REWRITE_TAC [lt_le] \\
         CONJ_TAC
         >- (Q.PAT_ASSUM ‘f z = Normal c’ (ONCE_REWRITE_TAC o wrap o SYM) \\
             FIRST_X_ASSUM MATCH_MP_TAC \\
             FIRST_X_ASSUM MATCH_MP_TAC >> art []) \\
         SPOSE_NOT_THEN (STRIP_ASSUME_TAC o REWRITE_RULE []) \\
        ‘inf {x | f x = Normal c} <= t’ by rw [inf_le'] \\
        ‘f (inf {x | f x = Normal c}) <= f t’ by PROVE_TAC [] \\
        ‘f (inf {x | f x = Normal c}) < f t’ by METIS_TAC [le_lt] \\
        ‘inf {x | f x = Normal c} < t’ by METIS_TAC [extreal_lt_def] \\
        ‘t <= inf {x | f x = Normal c}’ by rw [le_inf'] \\
         METIS_TAC [let_antisym] ] ])
 (* step 4, now take ‘z’ as the last position where ‘f’ jumps over ‘Normal c’.
    Note that ‘f z’ as the function of ‘sup’ may be above or below ‘Normal c’. *)
 >> FULL_SIMP_TAC std_ss []
 >> Q.ABBREV_TAC ‘z = sup {x | f x < Normal c}’
 >> Cases_on ‘f z < Normal c’
 >- (Suff ‘A = {x | x <= z}’ >- rw [BOREL_MEASURABLE_SETS] \\
     rw [Abbr ‘A’, Once EXTENSION] \\
     rename1 ‘f t < Normal c <=> t <= z’ \\
     EQ_TAC >> rw [Abbr ‘z’, le_sup'] \\
     MATCH_MP_TAC let_trans \\
     Q.EXISTS_TAC ‘f (sup {x | f x < Normal c})’ >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     rw [le_sup'])
 >> POP_ASSUM (STRIP_ASSUME_TAC o (SIMP_RULE bool_ss [extreal_lt_def]))
 (* step 5 *)
 >> Suff ‘A = {x | x < z}’ >- rw [BOREL_MEASURABLE_SETS]
 >> rw [Abbr ‘A’, Once EXTENSION]
 >> rename1 ‘f t < Normal c <=> t < z’
 >> EQ_TAC >> rw [Abbr ‘z’]
 >| [ (* goal 1 (of 2) *)
     ‘f t < f (sup {x | f x < Normal c})’ by PROVE_TAC [lte_trans] \\
      METIS_TAC [extreal_lt_def],
      (* goal 2 (of 2) *)
      Q.PAT_X_ASSUM ‘Normal c <= f y’ K_TAC (* useless *) \\
      Q.PAT_X_ASSUM ‘f x < Normal c’  K_TAC (* useless *) \\
      Q.PAT_X_ASSUM ‘Normal c <= f _’ K_TAC (* useless *) \\
      fs [lt_sup] >> rename1 ‘t < y’ \\
      MATCH_MP_TAC let_trans >> Q.EXISTS_TAC ‘f y’ >> art [] \\
      FIRST_X_ASSUM MATCH_MP_TAC >> rw [lt_imp_le] ]
QED

(* An easy corollary of the previous theorem *)
Theorem IN_MEASURABLE_BOREL_BOREL_MONO_DECREASING :
    !f. (!x y. x <= y ==> f y <= f x) ==> f IN measurable Borel Borel
Proof
    rpt STRIP_TAC
 >> Q.ABBREV_TAC ‘g = numeric_negate o f’
 >> Know ‘f = numeric_negate o g’
 >- (rw [Abbr ‘g’, FUN_EQ_THM]) >> Rewr'
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘Borel’ >> rw [IN_MEASURABLE_BOREL_BOREL_AINV]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_BOREL_MONO_INCREASING
 >> rw [Abbr ‘g’, le_neg]
QED

(* NOTE: we put ‘abs’ together because ‘powr’ is only defined on [0, PosInf] *)
Theorem IN_MEASURABLE_BOREL_BOREL_ABS_POWR :
    !p. 0 <= p /\ p <> PosInf ==> (\x. (abs x) powr p) IN measurable Borel Borel
Proof
    rpt STRIP_TAC
 >> Cases_on ‘p = 0’ >- rw [IN_MEASURABLE_BOREL_BOREL_CONST]
 >> ‘0 < p’ by rw [lt_le]
 >> Q.ABBREV_TAC ‘g = \x. if 0 <= x then x powr p else 0’
 >> ‘(\x. abs x powr p) = g o abs’ by (rw [FUN_EQ_THM, Abbr ‘g’]) >> POP_ORW
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘Borel’
 >> rw [IN_MEASURABLE_BOREL_BOREL_ABS]
 >> MATCH_MP_TAC IN_MEASURABLE_BOREL_BOREL_MONO_INCREASING
 >> rpt GEN_TAC
 >> Cases_on ‘0 <= x’ >> Cases_on ‘0 <= y’
 >> rw [Abbr ‘g’] (* 3 subgoals *)
 >| [ (* goal 1 (of 3) *)
      Suff ‘x powr p <= y powr p <=> x <= y’ >- rw [] \\
      MATCH_MP_TAC powr_mono_eq >> art [],
      (* goal 2 (of 3) *)
      fs [GSYM extreal_lt_def] \\
     ‘x < 0’ by PROVE_TAC [let_trans] \\
      METIS_TAC [let_antisym],
      (* goal 3 (of 3) *)
      rw [powr_pos] ]
QED

Theorem IN_MEASURABLE_BOREL_ABS_POWR :
    !a p f. f IN measurable a Borel /\ 0 <= p /\ p <> PosInf ==>
           (\x. (abs (f x)) powr p) IN measurable a Borel
Proof
    rpt STRIP_TAC
 >> ‘(\x. (abs (f x)) powr p) = (\x. (abs x) powr p) o f’ by rw [o_DEF] >> POP_ORW
 >> MATCH_MP_TAC MEASURABLE_COMP
 >> Q.EXISTS_TAC ‘Borel’
 >> rw [IN_MEASURABLE_BOREL_BOREL_ABS_POWR]
QED

(***********************)
(*   Further Results   *)
(***********************)

(*  I add these results at the end
      in order to manipulate the simplifier without breaking anything
      - Jared Yeager                                                    *)

val _ = augment_srw_ss [realSimps.REAL_ARITH_ss];

val _ = reveal "C";

(*** IN_MEASURABLE_BOREL Theorems ***)

(* There is already an IN_MEASURABLE_BOREL_CONG earlier in this theory *)
Theorem IN_MEASURABLE_BOREL_CONG':
    !a f g. (!x. x IN space a ==> f x = g x) ==>
            (f IN Borel_measurable a <=> g IN Borel_measurable a)
Proof
    rw[] >> eq_tac >> rw[] >> dxrule_at_then (Pos $ el 2) irule IN_MEASURABLE_BOREL_EQ' >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_COMP:
    !a b f g h. f IN Borel_measurable b /\ g IN measurable a b /\
        (!x. x IN space a ==> h x = f (g x)) ==> h IN Borel_measurable a
Proof
    rw[] >> dxrule_all_then assume_tac MEASURABLE_COMP >>
    irule IN_MEASURABLE_BOREL_EQ' >> qexists_tac ‘f o g’ >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_COMP_BOREL:
    !a f g h. f IN Borel_measurable Borel /\ g IN Borel_measurable a /\
        (!x. x IN space a ==> h x = f (g x)) ==> h IN Borel_measurable a
Proof
    rw[] >> dxrule_all_then assume_tac MEASURABLE_COMP >>
    irule IN_MEASURABLE_BOREL_EQ' >> qexists_tac ‘f o g’ >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_SUM':
    !a f g s. FINITE s /\ sigma_algebra a /\ (!i. i IN s ==> f i IN Borel_measurable a) /\
        (!x. x IN space a ==> g x = EXTREAL_SUM_IMAGE (λi. f i x) s) ==> g IN Borel_measurable a
Proof
    ‘!a f g l. sigma_algebra a /\ (!i. MEM i l ==> f i IN Borel_measurable a) /\
      (!x. x IN space a ==> g x = FOLDR (λi acc. f i x + acc) 0 l) ==> g IN Borel_measurable a’ suffices_by (
        rw[] >> last_x_assum irule >> simp[] >> qexistsl_tac [‘f’,‘REVERSE (SET_TO_LIST s)’] >>
        simp[EXTREAL_SUM_IMAGE_ALT_FOLDR,SF SFY_ss]) >>
    Induct_on ‘l’ >> rw[FOLDR]
    >- (irule IN_MEASURABLE_BOREL_CONST >> simp[] >> qexists_tac ‘0’ >> simp[]) >>
    irule IN_MEASURABLE_BOREL_ADD' >> simp[] >>
    qexistsl_tac [‘f h’,‘λx. FOLDR (λi acc. f i x + acc) 0 l’] >> simp[] >>
    last_x_assum irule >> simp[] >> qexists_tac ‘f’ >> simp[]
QED

(* This is just a naming consistence thing, the _TIMES suffix deviates from convention *)
Theorem IN_MEASURABLE_BOREL_MUL' = IN_MEASURABLE_BOREL_TIMES';

Theorem IN_MEASURABLE_BOREL_PROD:
    !a f g s. FINITE s /\ sigma_algebra a /\ (!i. i IN s ==> f i IN Borel_measurable a) /\
        (!i x. i IN s /\ x IN space a ==> f i x <> NegInf /\ f i x <> PosInf) /\
        (!x. x IN space a ==> g x = EXTREAL_PROD_IMAGE (λi. f i x) s) ==>
        g IN Borel_measurable a
Proof
    NTAC 2 gen_tac >> simp[Once SWAP_FORALL_THM,Once $ GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    Induct_on ‘s’ >> rw[]
    >- (fs[EXTREAL_PROD_IMAGE_EMPTY] >> irule IN_MEASURABLE_BOREL_CONST >>
        simp[] >> qexists_tac ‘1’ >> simp[]) >>
    rfs[EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT] >>
    irule IN_MEASURABLE_BOREL_MUL >> simp[] >> qexistsl_tac [‘f e’,‘λx. EXTREAL_PROD_IMAGE (λi. f i x) s’] >>
    simp[] >> NTAC 2 strip_tac >> irule EXTREAL_PROD_IMAGE_NOT_INFTY >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_PROD':
    !a f g s. FINITE s /\ sigma_algebra a /\ (!i. i IN s ==> f i IN Borel_measurable a) /\
        (!x. x IN space a ==> g x = EXTREAL_PROD_IMAGE (λi. f i x) s) ==> g IN Borel_measurable a
Proof
    NTAC 2 gen_tac >> simp[Once SWAP_FORALL_THM,Once $ GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM]
 >> Induct_on ‘s’ >> rw[]
 >- (fs[EXTREAL_PROD_IMAGE_EMPTY] >> irule IN_MEASURABLE_BOREL_CONST >>
     simp[] >> qexists_tac ‘1’ >> simp[])
 >> rfs[EXTREAL_PROD_IMAGE_PROPERTY,DELETE_NON_ELEMENT_RWT]
 >> irule IN_MEASURABLE_BOREL_MUL' >> simp[]
 >> qexistsl_tac [‘f e’,‘λx. EXTREAL_PROD_IMAGE (λi. f i x) s’] >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_INV:
    !a f g. sigma_algebra a /\ f IN Borel_measurable a /\
        (!x. x IN space a ==> g x = extreal_inv (f x) * indicator_fn {y | f y <> 0} x) ==>
        g IN Borel_measurable a
Proof
    rw[]
 >> simp[IN_MEASURABLE_BOREL,FUNSET]
 >> ‘(!c. c <= 0 ==> {x | g x < Normal c} INTER space a IN subsets a) /\
      {x | g x = 0} INTER space a IN subsets a /\
      (!c. 0 < c ==> {x | 0 < g x /\ g x < Normal c} INTER space a IN subsets a)’ suffices_by (
        rw[] >> Cases_on ‘c <= 0’ >> simp[] >> fs[REAL_NOT_LE] >>
        first_x_assum $ drule_then assume_tac >> first_x_assum $ qspec_then ‘0’ assume_tac >>
        fs[normal_0] >> drule_then (fn th => NTAC 2 $ dxrule_all_then assume_tac th) SIGMA_ALGEBRA_UNION >>
        pop_assum mp_tac >> qmatch_abbrev_tac ‘s IN _ ==> t IN _’ >> ‘s = t’ suffices_by simp[] >>
        UNABBREV_ALL_TAC >> rw[EXTENSION] >> qpat_x_assum ‘!x. _’ kall_tac >>
        Cases_on ‘x IN space a’ >> simp[] >> Cases_on ‘g x’ >> simp[])
 >> rw[]
 >- (MP_TAC (Q.SPECL [‘f’, ‘a’] IN_MEASURABLE_BOREL_OO) >> RW_TAC std_ss [] \\
     POP_ASSUM (qspecl_then [‘if c = 0 then NegInf else Normal (inv c)’,‘0’] mp_tac) \\
     qmatch_abbrev_tac ‘s IN _ ==> t IN _’ >> ‘s = t’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
     simp[EXTENSION] >> strip_tac >> Cases_on ‘x IN space a’ >> simp[indicator_fn_def] >>
     Cases_on ‘f x’ >> rw[extreal_inv_def] >> eq_tac >> strip_tac >> simp[] >>
     drule_all_then assume_tac REAL_LTE_TRANS >> fs[])
 >- (drule_all_then assume_tac IN_MEASURABLE_BOREL_SING >>
     pop_assum (fn th => map_every (fn tm => qspec_then tm assume_tac th) [‘NegInf’,‘0’,‘PosInf’]) >>
     drule_then (fn th => NTAC 2 $ dxrule_all_then assume_tac th) SIGMA_ALGEBRA_UNION >>
     pop_assum mp_tac >> qmatch_abbrev_tac ‘s IN _ ==> t IN _’ >> ‘s = t’ suffices_by simp[] >>
     UNABBREV_ALL_TAC >> rw[EXTENSION] >> Cases_on ‘x IN space a’ >> simp[indicator_fn_def] >>
     Cases_on ‘f x’ >> rw[extreal_inv_def])
 >- (MP_TAC (Q.SPECL [‘f’, ‘a’] IN_MEASURABLE_BOREL_OO) >> RW_TAC std_ss [] \\
     POP_ASSUM (qspecl_then [‘Normal (inv c)’,‘PosInf’] mp_tac) \\
     qmatch_abbrev_tac ‘s IN _ ==> t IN _’ >> ‘s = t’ suffices_by simp[] >> UNABBREV_ALL_TAC >>
     rw[EXTENSION] >> Cases_on ‘x IN space a’ >> simp[indicator_fn_def] >>
     Cases_on ‘f x’ >> rw[extreal_inv_def] >> simp[] >> eq_tac >> strip_tac >> rfs[] >>
     REVERSE CONJ_ASM1_TAC >- simp[] >> ‘0 <= c * r’ by simp[] >> rfs[REAL_MUL_SIGN])
QED

Theorem IN_MEASURABLE_BOREL_MUL_INV:
    !a f g h. sigma_algebra a /\ f IN Borel_measurable a /\ g IN Borel_measurable a /\
        (!x. x IN space a /\ g x = 0 ==> f x = 0) /\
        (!x. x IN space a ==> h x = f x * extreal_inv (g x)) ==>
        h IN Borel_measurable a
Proof
    rw[] >> irule IN_MEASURABLE_BOREL_MUL' >> simp[] >>
    qexistsl_tac [‘f’,‘λx. extreal_inv (g x) * indicator_fn {y | g y <> 0} x’] >> simp[] >>
    irule_at Any IN_MEASURABLE_BOREL_INV >>
    qexists_tac ‘g’ >> simp[] >> rw[indicator_fn_def] >> simp[]
QED

Theorem IN_MEASURABLE_BOREL_EXP:
    !a f g. sigma_algebra a /\ f IN Borel_measurable a /\ (!x. x IN space a ==> g x = exp (f x)) ==>
        g IN Borel_measurable a
Proof
    rw[] >> irule IN_MEASURABLE_BOREL_COMP_BOREL >> simp[] >> qexistsl_tac [‘exp’,‘f’] >> simp[] >>
    rw[IN_MEASURABLE_BOREL_ALT2,SIGMA_ALGEBRA_BOREL,FUNSET,SPACE_BOREL] >> Cases_on ‘c < 0’
    >- (‘{x | exp x <= Normal c} = EMPTY’ suffices_by simp[BOREL_MEASURABLE_SETS_EMPTY] >>
        rw[EXTENSION,GSYM extreal_lt_def] >> irule lte_trans >> qexists_tac ‘0’ >> simp[exp_pos]) >>
    ‘{x | exp x <= Normal c} = {x | x <= ln (Normal c)}’ suffices_by simp[BOREL_MEASURABLE_SETS_RC] >>
    fs[GSYM real_lte] >> rw[EXTENSION] >> REVERSE (fs[REAL_LE_LT])
    >- (simp[extreal_ln_def,normal_0] >> Cases_on ‘x’ >>
        simp[extreal_exp_def,GSYM real_lt,EXP_POS_LT]) >>
    drule_then SUBST1_TAC $ GSYM $ iffRL EXP_LN >> simp[Once $ GSYM extreal_exp_def] >>
    simp[iffRL EXP_LN,extreal_ln_def]
QED

Theorem IN_MEASURABLE_BOREL_POW':
    !n a f g. sigma_algebra a /\ f IN Borel_measurable a /\ (!x. x IN space a ==> g x = f x pow n) ==>
        g IN Borel_measurable a
Proof
    Induct_on ‘n’ >> rw[extreal_pow_alt]
    >- (irule IN_MEASURABLE_BOREL_CONST >> simp[] >> qexists_tac ‘1’ >> simp[])
    >- (irule IN_MEASURABLE_BOREL_MUL' >> simp[] >> qexistsl_tac [‘λx. f x pow n’,‘f’] >> simp[] >>
        last_x_assum irule >> simp[] >> qexists_tac ‘f’ >> simp[])
QED

Theorem IN_MEASURABLE_BOREL_POW_EXP:
    !a f g h. sigma_algebra a /\ f IN Borel_measurable a /\
        (!n. {x | g x = n} INTER space a IN subsets a) /\
        (!x. x IN space a ==> h x = (f x) pow (g x)) ==> h IN Borel_measurable a
Proof
    rw[] >> simp[Once IN_MEASURABLE_BOREL_PLUS_MINUS] >>
    ‘!P. {x | P (g x)} INTER space a IN subsets a’ by (rw[] >>
        ‘{x | P (g x)} INTER space a = BIGUNION {{x | g x = n} INTER space a | P n}’ by (
            rw[Once EXTENSION,IN_BIGUNION] >> eq_tac >> strip_tac >> gvs[] >>
            qexists_tac ‘{y | g y = g x} INTER space a’ >> simp[] >> qexists_tac ‘g x’ >> simp[]) >>
        pop_assum SUBST1_TAC >> irule SIGMA_ALGEBRA_COUNTABLE_UNION >>
        REVERSE (rw[SUBSET_DEF]) >- simp[SF SFY_ss] >> simp[COUNTABLE_ALT] >>
        qexists_tac ‘λn. {x | g x = n} INTER space a’ >> rw[] >> qexists_tac ‘n’ >> simp[]) >>
    map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> qexistsl_tac qex >> simp ths) [
        (Pos hd,IN_MEASURABLE_BOREL_ADD',[‘λx. fn_minus f x pow g x * indicator_fn {x | EVEN (g x)} x’,
            ‘λx. fn_plus f x pow g x * indicator_fn {x | $< 0 (g x)} x’],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_MUL',[‘indicator_fn {x | EVEN (g x)}’,‘λx. fn_minus f x pow g x’],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_INDICATOR,[‘{x | EVEN (g x)} INTER space a’],[]),
        (Pos (el 3),IN_MEASURABLE_BOREL_MUL',[‘indicator_fn {x | $< 0 (g x)}’,‘λx. fn_plus f x pow g x’],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_INDICATOR,[‘{x | $< 0 (g x)} INTER space a’],[]),
        (Pos last,IN_MEASURABLE_BOREL_MUL',[‘indicator_fn {x | ODD (g x)}’,‘λx. fn_minus f x pow g x’],[]),
        (Pos (el 2),IN_MEASURABLE_BOREL_INDICATOR,[‘{x | ODD (g x)} INTER space a’],[])] >>
    pop_assum kall_tac >>
    ‘!pf. pf IN Borel_measurable a /\ (!x. 0 <= pf x) ==> (λx. pf x pow g x) IN Borel_measurable a’ by (
        rw[] >> irule IN_MEASURABLE_BOREL_SUMINF >> simp[] >>
        qexistsl_tac [‘λn x. pf x pow n * indicator_fn {x | g x = n} x’] >> simp[pow_pos_le,INDICATOR_FN_POS,le_mul] >>
        simp[RIGHT_AND_FORALL_THM] >> strip_tac >>
        map_every (fn (pos,tm,qex,ths) => irule_at pos tm >> simp[] >> qexistsl_tac qex >> simp ths) [
            (Any,IN_MEASURABLE_BOREL_MUL',[‘indicator_fn {x | g x = n}’,‘λx. pf x pow n’],[]),
            (Pos hd,IN_MEASURABLE_BOREL_POW',[‘n’,‘pf’],[]),
            (Pos hd,IN_MEASURABLE_BOREL_INDICATOR,[‘{x | g x = n} INTER space a’],[indicator_fn_def])] >>
        rw[] >> qspecl_then [‘g x’,‘pf x pow g x’] mp_tac ext_suminf_sing_general >>
        simp[pow_pos_le] >> DISCH_THEN $ SUBST1_TAC o SYM >> AP_TERM_TAC >> rw[FUN_EQ_THM] >>
        Cases_on ‘g x = n’ >> simp[]) >>
    pop_assum (fn th => NTAC 2 (irule_at Any th >> simp[iffLR IN_MEASURABLE_BOREL_PLUS_MINUS])) >>
    simp[FN_PLUS_POS,FN_MINUS_POS] >> rw[indicator_fn_def] >> simp[fn_minus_def,fn_plus_alt]
    >- (Cases_on ‘f x < 0’ >- fs[pow_neg_odd,pow_ainv_odd] >> fs[ODD_POS,zero_pow] >>
        ‘~(f x pow g x < 0)’ suffices_by simp[] >> fs[extreal_lt_def,pow_pos_le])
    >- (‘~(f x pow g x < 0)’ suffices_by simp[] >> fs[ODD_EVEN] >> simp[extreal_lt_def,pow_even_le])
    >- (Cases_on ‘0 <= f x’ >> fs[GSYM extreal_lt_def] >>
        simp[ineq_imp,pow_pos_le,zero_pow,pow_even_le,pow_ainv_even])
    >- (fs[EVEN_ODD] >> Cases_on ‘0 <= f x’ >> fs[GSYM extreal_lt_def] >> simp[ineq_imp,pow_pos_le,zero_pow] >>
        ‘~(0 <= f x pow g x)’ suffices_by simp[] >> simp[GSYM extreal_lt_def,pow_neg_odd])
    >- (Cases_on ‘0 <= f x’ >> fs[GSYM extreal_lt_def] >> simp[ineq_imp])
    >- (rfs[EVEN_ODD,ODD])
QED

(* NOTE: added ‘sigma_algebra a’ into antecedents due to changes of ‘measurable’

         Here ‘Normal o real’ is actually used as a "filter" to remove all infinities from
         the domain of a function f.
 *)
Theorem IN_MEASURABLE_BOREL_NORMAL_REAL:
    !a f. sigma_algebra a /\ f IN Borel_measurable a ==> Normal o real o f IN Borel_measurable a
Proof
    rw[] >> irule IN_MEASURABLE_BOREL_IMP_BOREL' >> art []
 >> irule_at Any in_borel_measurable_from_Borel >> art []
QED

(*** AE Theorems ***)

Theorem AE_subset:
    !m P Q. (AE x::m. P x) /\ (!x. x IN m_space m /\ P x ==> Q x) ==> (AE x::m. Q x)
Proof
    rw[AE_ALT] >> qexists_tac `N` >> fs[SUBSET_DEF] >> rw[] >>
    NTAC 2 $ first_x_assum $ drule_then assume_tac >> gs[]
QED

Theorem AE_cong:
    !m P Q. (!x. x IN m_space m ==> P x = Q x) ==> ((AE x::m. P x) <=> (AE x::m. Q x))
Proof
    rw[] >> eq_tac >> rw[] >> dxrule_at_then (Pos $ el 1) irule AE_subset >> simp[SF CONJ_ss]
QED

Theorem AE_T:
    !m. measure_space m ==> AE x::m. T
Proof
    rw[AE_ALT] >> qexists_tac ‘ {} ’ >> simp[NULL_SET_EMPTY]
QED

Theorem AE_UNION:
    !m P Q. measure_space m /\ ((AE x::m. P x) \/ (AE x::m. Q x)) ==> (AE x::m. P x \/ Q x)
Proof
    rw[AE_ALT,null_set_def] >> qexists_tac ‘N’ >> fs[SUBSET_DEF]
QED

Theorem AE_BIGUNION:
    !m P s. measure_space m /\ (?n. n IN s /\ AE x::m. P n x) ==> (AE x::m. ?n. n IN s /\ P n x)
Proof
    rw[AE_ALT,null_set_def] >> qexists_tac ‘N’ >> fs[SUBSET_DEF,GSYM IMP_DISJ_THM]
QED

Theorem AE_INTER:
    !m P Q. measure_space m /\ (AE x::m. P x) /\ (AE x::m. Q x) ==> (AE x::m. P x /\ Q x)
Proof
    rw[AE_ALT] >> qexists_tac ‘N UNION N'’ >> rename [‘N UNION M’] >>
    simp[SIMP_RULE (srw_ss ()) [IN_APP] NULL_SET_UNION] >>
    fs[SUBSET_DEF] >> rw[] >> simp[]
QED

Theorem AE_BIGINTER:
    !m P s. measure_space m /\ countable s /\ (!n. n IN s ==> AE x::m. P n x) ==> (AE x::m. !n. n IN s ==> P n x)
Proof
    rw[AE_ALT] >> fs[GSYM RIGHT_EXISTS_IMP_THM,SKOLEM_THM] >> qexists_tac ‘BIGUNION (IMAGE f s)’ >>
    rename [‘IMAGE N s’] >> REVERSE CONJ_TAC
    >- (fs[SUBSET_DEF] >> rw[] >> NTAC 2 (first_x_assum $ drule_then assume_tac >> rfs[]) >>
        map_every (fn qex => qexists_tac qex >> simp[]) [‘N n’,‘n’]) >>
    fs[COUNTABLE_ENUM] >- simp[NULL_SET_EMPTY] >> simp[IMAGE_IMAGE] >>
    fs[null_set_def] >> CONJ_ASM1_TAC >- (irule MEASURE_SPACE_BIGUNION >> simp[]) >>
    simp[GSYM le_antisym] >> irule_at Any $ cj 2 $ iffLR positive_def >> simp[iffLR measure_space_def] >>
    irule leeq_trans >> qexists_tac ‘suminf (measure m o (N o f))’ >>
    irule_at Any $ iffLR countably_subadditive_def >>
    simp[MEASURE_SPACE_COUNTABLY_SUBADDITIVE,FUNSET,combinTheory.o_DEF,ext_suminf_0]
QED

Theorem AE_eq_add:
    !m f fae g gae. measure_space m /\ (AE x::m. f x = fae x) /\ (AE x::m. g x = gae x) ==>
        AE x::m. f x + g x = fae x + gae x
Proof
    rw[] >> fs[AE_ALT] >> qexists_tac ‘N UNION N'’ >>
    (drule_then assume_tac) NULL_SET_UNION >> rfs[IN_APP] >> pop_assum kall_tac >>
    fs[SUBSET_DEF] >> rw[] >> NTAC 2 (last_x_assum (drule_then assume_tac)) >>
    CCONTR_TAC >> fs[]
QED

Theorem AE_eq_sum:
    !m f fae s. FINITE s /\ measure_space m /\ (!n. n IN s ==> AE x::m. (f n x):extreal = fae n x) ==>
        AE x::m. SIGMA (C f x) s = SIGMA (C fae x) s
Proof
    rw[] >> qspecl_then [‘m’,‘λn x. f n x = fae n x’,‘s’] assume_tac AE_BIGINTER
 >> rfs[finite_countable]
 >> qspecl_then [‘m’,‘λx. !n. n IN s ==> f n x = fae n x’,‘λx. SIGMA (C f x) s = SIGMA (C fae x) s’]
        (irule o SIMP_RULE (srw_ss ()) []) AE_subset
 >> rw[] >> irule EXTREAL_SUM_IMAGE_EQ' >> rw[combinTheory.C_DEF]
QED

val _ = export_theory ();

(* References:

  [1] Schilling, R.L.: Measures, Integrals and Martingales (Second Edition).
      Cambridge University Press (2017).
  [2] Mhamdi, T., Hasan, O., Tahar, S.: Formalization of Measure Theory and
      Lebesgue Integration for Probabilistic Analysis in HOL.
      ACM Trans. Embedded Comput. Syst. 12, 1--23 (2013).
  [3] Coble, A.R.: Anonymity, information, and machine-assisted proof, (2010).
  [4] Hurd, J.: Formal verification of probabilistic algorithms. (2001).
  [7] Wikipedia: https://en.wikipedia.org/wiki/Emile_Borel
  [8] Hardy, G.H., Littlewood, J.E.: A Course of Pure Mathematics, Tenth Edition.
      Cambridge University Press, London (1967).
 *)
