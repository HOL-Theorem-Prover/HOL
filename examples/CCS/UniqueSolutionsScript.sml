(* ========================================================================== *)
(* FILE          : UniqueSolutionsScript.sml                                  *)
(* DESCRIPTION   : Milner and Sangiorgi's "Unique Solutions of Equations"     *)
(*                                                                            *)
(* THESIS        : A Formalization of Unique Solutions of Equations in        *)
(*                 Process Algebra                                            *)
(* AUTHOR        : (c) Chun Tian, University of Bologna                       *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory pairTheory sumTheory listTheory;
open prim_recTheory arithmeticTheory combinTheory;

open CCSLib CCSTheory;
open StrongEQTheory StrongEQLib StrongLawsTheory;
open WeakEQTheory WeakEQLib WeakLawsTheory;
open ObsCongrTheory ObsCongrLib ObsCongrLawsTheory;
open CongruenceTheory BisimulationUptoTheory;
open TraceTheory ExpansionTheory ContractionTheory;

val _ = new_theory "UniqueSolutions";

(******************************************************************************)
(*                                                                            *)
(*          1. Milner's unique solutions theorem for STRONG_EQUIV             *)
(*                                                                            *)
(******************************************************************************)

(* Lemma 4.13 in Milner's book [1]:
   If the variable X is weakly guarded in E, and E{P/X} --a-> P', then P' takes the form
   E'{P/X} (for some expression E'), and moreover, for any Q, E{Q/X} --a-> E'{Q/X}.
 *)
val STRONG_UNIQUE_SOLUTIONS_LEMMA = store_thm (
   "STRONG_UNIQUE_SOLUTIONS_LEMMA",
  ``!E. WG E ==>
	!P a P'. TRANS (E P) a P' ==>
		 ?E'. CONTEXT E' /\ (P' = E' P) /\ !Q. TRANS (E Q) a (E' Q)``,
    Induct_on `WG` >> BETA_TAC
 >> COUNT_TAC (rpt STRIP_TAC) (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      POP_ASSUM (STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [TRANS_cases])) \\
      Q.EXISTS_TAC `\t. P'` >> BETA_TAC \\
      ASM_REWRITE_TAC [CONTEXT2] >| (* 10 sub-goals here *)
      [ REWRITE_TAC [PREFIX],
        MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [],
        MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [],
        MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [],
        MATCH_MP_TAC REC >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 6) *)
      IMP_RES_TAC TRANS_PREFIX \\
      ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `e` \\
      ASM_REWRITE_TAC [PREFIX],
      (* goal 3 (of 6) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 3.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ],
      (* goal 4 (of 6) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 4.1 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E'' t) (E' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.1.1 (of 2) *)
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WG_IS_CONTEXT,
          (* goal 4.1.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [] ],
        (* goal 4.2 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.2.1 (of 2) *)
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] \\
          IMP_RES_TAC WG_IS_CONTEXT,
          (* goal 4.2.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ],
        (* goal 4.3 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E''' t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.3.1 (of 2) *)
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [],
          (* goal 4.3.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR3 \\
          Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ] ],
      (* goal 5 (of 6) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        FULL_SIMP_TAC std_ss [] \\
        PROVE_TAC [],
        (* goal 5.2 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        PROVE_TAC [] ],
      (* goal 6 (of 6) *)
      IMP_RES_TAC TRANS_RELAB \\
      RES_TAC >> FULL_SIMP_TAC std_ss [] \\
      Q.EXISTS_TAC `\t. relab (E' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
      CONJ_TAC >- ( MATCH_MP_TAC CONTEXT7 >> ASM_REWRITE_TAC [] ) \\
      GEN_TAC >> MATCH_MP_TAC RELABELING \\
      ASM_REWRITE_TAC [] ]);

(* Proposition 3.14 in Milner's book [1]:
   Let the expression E contains at most the variable X, and let X be weakly guarded in E,
   then:
	If P ~ E{P/X} and Q ~ E{Q/X} then P ~ Q.
 *)
val STRONG_UNIQUE_SOLUTIONS = store_thm (
   "STRONG_UNIQUE_SOLUTIONS",
  ``!E. WG E ==>
	!P Q. STRONG_EQUIV P (E P) /\ STRONG_EQUIV Q (E Q) ==> STRONG_EQUIV P Q``,
    rpt STRIP_TAC
 >> irule (REWRITE_RULE [RSUBSET] STRONG_BISIM_UPTO_THM)
 >> Q.EXISTS_TAC `\x y. (x = y) \/ (?G. CONTEXT G /\ (x = G P) /\ (y = G Q))`
 >> BETA_TAC >> Rev CONJ_TAC
 >- ( DISJ2_TAC >> Q.EXISTS_TAC `\x. x` >> BETA_TAC \\
      KILL_TAC >> RW_TAC std_ss [CONTEXT1] )
 >> REWRITE_TAC [STRONG_BISIM_UPTO]
 >> Q.X_GEN_TAC `P'`
 >> Q.X_GEN_TAC `Q'`
 >> BETA_TAC >> STRIP_TAC (* 2 sub-goals here *)
 >- ( ASM_REWRITE_TAC [] >> rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 1 (of 2) *)
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [O_DEF] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [],
        (* goal 2 (of 2) *)
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
        REWRITE_TAC [O_DEF] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
        BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [] ] )
 >> ASM_REWRITE_TAC []
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`G`, `G`)
 >> COUNT_TAC (Induct_on `CONTEXT` >> BETA_TAC >> rpt STRIP_TAC) (* 14 sub-goals here *)
 >| [ (* goal 1 (of 14) *)
      Q.PAT_X_ASSUM `STRONG_EQUIV P (E P)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      IMP_RES_TAC STRONG_UNIQUE_SOLUTIONS_LEMMA \\ (* lemma used here *)
      FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      Q.PAT_X_ASSUM `STRONG_EQUIV Q (E Q)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      `STRONG_EQUIV (E' Q) E1'` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      Q.EXISTS_TAC `E' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E' P` >> ASM_REWRITE_TAC [] \\
      BETA_TAC >> DISJ2_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 14) *)
      Q.PAT_X_ASSUM `STRONG_EQUIV Q (E Q)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      IMP_RES_TAC STRONG_UNIQUE_SOLUTIONS_LEMMA \\ (* lemma used here *)
      FULL_SIMP_TAC std_ss [] \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      Q.PAT_X_ASSUM `STRONG_EQUIV P (E P)`
	(STRIP_ASSUME_TAC o (ONCE_REWRITE_RULE [PROPERTY_STAR])) \\
      RES_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      `STRONG_EQUIV (E' P) E1` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      `STRONG_EQUIV (E' Q) E2` by PROVE_TAC [STRONG_EQUIV_SYM] \\
      Q.EXISTS_TAC `E' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E' P` >> ASM_REWRITE_TAC [] \\
      BETA_TAC >> DISJ2_TAC \\
      Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [],
      (* goal 3 (of 14) *)
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [],
      (* goal 4 (of 14) *)
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [STRONG_EQUIV_REFL] \\
      BETA_TAC >> DISJ1_TAC >> RW_TAC std_ss [],
      (* goal 5 (of 14) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G Q` >> REWRITE_TAC [PREFIX] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `G Q` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `G P` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      DISJ2_TAC >> Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [],
      (* goal 6 (of 14) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G P` >> REWRITE_TAC [PREFIX] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      Q.EXISTS_TAC `G Q` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      Q.EXISTS_TAC `G P` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      DISJ2_TAC >> Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [],
      (* goal 7 (of 14) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 7.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [],
        (* goal 7.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [] ],
      (* goal 8 (of 14) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 8.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [],
        (* goal 8.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ) \\
        ASM_REWRITE_TAC [] ],
      (* goal 9 (of 14) *)
      IMP_RES_TAC TRANS_PAR >> FULL_SIMP_TAC std_ss [] >| (* 3 sub-goals here *)
      [ (* goal 9.1 (of 3) *)
        Q.PAT_X_ASSUM `E1 = X` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `E2 || G' Q` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 9.1.1 (of 2) *)
          Q.EXISTS_TAC `y || G' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `y || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. (\z. y) t || G' t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.1.2 (of 2) *)
          Q.EXISTS_TAC `G'' Q || G' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G'' P || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ],
        (* goal 9.2 (of 3) *)
        Q.PAT_X_ASSUM `E1 = X` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `G Q || E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 9.2.1 (of 2) *)
          Q.EXISTS_TAC `G Q || y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || y` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. G t || (\z. y) t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.2.2 (of 2) *)
          Q.EXISTS_TAC `G Q || G'' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ],
        (* goal 9.3 (of 3) *)
        Q.PAT_X_ASSUM `E1 = X` K_TAC \\
        Q.PAT_X_ASSUM `u = tau` K_TAC \\
        RES_TAC \\
        Q.EXISTS_TAC `E2'' || E2'` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        Q.PAT_X_ASSUM `X E2 E2'` MP_TAC \\
        Q.PAT_X_ASSUM `X E1' E2''` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 4 sub-goals here *)
        [ (* goal 9.3.1 (of 4) *)
          Q.EXISTS_TAC `y || y''` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y || y''` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 9.3.2 (of 4) *)
          Q.EXISTS_TAC `y || G'' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. (\z. y) t || G'' t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.3.3 (of 4) *)
          Q.EXISTS_TAC `G'' Q || y''` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G'' P || y''` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || y''` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y'')` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. G'' t || (\z. y'') t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 9.3.4 (of 4) *)
          Q.EXISTS_TAC `G'' Q || G''' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G'' P || G''' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || G''' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ] ],
      (* goal 10 (of 14) *)
      IMP_RES_TAC TRANS_PAR >> FULL_SIMP_TAC std_ss [] >| (* 3 sub-goals here *)
      [ (* goal 10.1 (of 3) *)
        Q.PAT_X_ASSUM `E2 = X` K_TAC >> RES_TAC \\
        Q.EXISTS_TAC `E1' || G' P` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 10.1.1 (of 2) *)
          Q.EXISTS_TAC `y || G' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `y || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. (\z. y) t || G' t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.1.2 (of 2) *)
          Q.EXISTS_TAC `G'' Q || G' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G'' P || G' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || G' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ],
        (* goal 10.2 (of 3) *)
        Q.PAT_X_ASSUM `E2 = X` K_TAC >> RES_TAC \\
        Q.EXISTS_TAC `G P || E1'` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 10.2.1 (of 2) *)
          Q.EXISTS_TAC `G Q || y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || y` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. G t || (\z. y) t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.2.2 (of 2) *)
          Q.EXISTS_TAC `G Q || G'' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          Q.EXISTS_TAC `G P || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [STRONG_EQUIV_REFL] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G t || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ],
        (* goal 10.3 (of 3) *)
        Q.PAT_X_ASSUM `E2 = X` K_TAC \\
        Q.PAT_X_ASSUM `u = tau` K_TAC >> RES_TAC \\
        Q.EXISTS_TAC `E1'' || E1'` \\
        CONJ_TAC >- ( MATCH_MP_TAC PAR3 >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        Q.PAT_X_ASSUM `X E1'' E1` MP_TAC \\
        Q.PAT_X_ASSUM `X E1' E2'` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC \\
        RW_TAC std_ss [] >| (* 4 sub-goals here *)
        [ (* goal 10.3.1 (of 4) *)
          Q.EXISTS_TAC `y'' || y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y'' || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 10.3.2 (of 4) *)
          Q.EXISTS_TAC `G'' Q || y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G'' P || y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G'' t || y` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. G'' t || (\z. y) t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.3.3 (of 4) *)
          Q.EXISTS_TAC `y'' || G'' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `y'' || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. y'' || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          `CONTEXT (\z. y'')` by REWRITE_TAC [CONTEXT2] \\
          Know `CONTEXT (\t. (\z. y'') t || G'' t)`
          >- ( MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ) \\
          BETA_TAC >> REWRITE_TAC [],
          (* goal 10.3.4 (of 4) *)
          Q.EXISTS_TAC `G''' Q || G'' Q` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `G''' P || G'' P` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. G''' t || G'' t` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT5 >> ASM_REWRITE_TAC [] ] ],
      (* goal 11 (of 14) *)
      IMP_RES_TAC TRANS_RESTR >> FULL_SIMP_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 11.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> FULL_SIMP_TAC std_ss [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 11.1.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 11.1.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [] ],
        (* goal 11.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E2` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 11.2.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 11.2.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [] ] ],
      (* goal 12 (of 14) *)
      IMP_RES_TAC TRANS_RESTR >> FULL_SIMP_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 12.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> FULL_SIMP_TAC std_ss [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 12.1.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 12.1.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [] ],
        (* goal 12.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `restr L E1` \\
        CONJ_TAC >- ( MATCH_MP_TAC RESTR >> Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ) \\
        POP_ASSUM MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
        [ (* goal 12.2.1 (of 2) *)
          Q.EXISTS_TAC `restr L y` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L y` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ1_TAC >> REWRITE_TAC [],
          (* goal 12.2.2 (of 2) *)
          Q.EXISTS_TAC `restr L (G' Q)` \\
          Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
				ASM_REWRITE_TAC [] ) \\
          Q.EXISTS_TAC `restr L (G' P)` \\
          CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR \\
			ASM_REWRITE_TAC [] ) \\
          DISJ2_TAC \\
          Q.EXISTS_TAC `\t. restr L (G' t)` >> BETA_TAC >> REWRITE_TAC [] \\
          MATCH_MP_TAC CONTEXT6 >> ASM_REWRITE_TAC [] ] ],
      (* goal 13 (of 14) *)
      IMP_RES_TAC TRANS_RELAB \\
      FULL_SIMP_TAC std_ss [] \\
      RES_TAC \\
      Q.EXISTS_TAC `relab E2 rf` \\
      CONJ_TAC >- ( MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [] ) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 13.1 (of 2) *)
        Q.EXISTS_TAC `relab y rf` \\
        Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab y rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ1_TAC >> REWRITE_TAC [],
        (* goal 13.2 (of 2) *)
        Q.EXISTS_TAC `relab (G' Q) rf` \\
        Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab (G' P) rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ2_TAC \\
        Q.EXISTS_TAC `\t. relab (G' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
        MATCH_MP_TAC CONTEXT7 >> ASM_REWRITE_TAC [] ],
      (* goal 14 (of 14) *)
      IMP_RES_TAC TRANS_RELAB \\
      FULL_SIMP_TAC std_ss [] \\
      RES_TAC \\
      Q.EXISTS_TAC `relab E1 rf` \\
      CONJ_TAC >- ( MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [] ) \\
      POP_ASSUM MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> RW_TAC std_ss [] >| (* 2 sub-goals here *)
      [ (* goal 14.1 (of 2) *)
        Q.EXISTS_TAC `relab y rf` \\
        Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab y rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ1_TAC >> REWRITE_TAC [],
        (* goal 14.2 (of 2) *)
        Q.EXISTS_TAC `relab (G' Q) rf` \\
        Rev CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB \\
			      ASM_REWRITE_TAC [] ) \\
        Q.EXISTS_TAC `relab (G' P) rf` \\
        CONJ_TAC >- ( MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> ASM_REWRITE_TAC [] ) \\
        DISJ2_TAC \\
        Q.EXISTS_TAC `\t. relab (G' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
        MATCH_MP_TAC CONTEXT7 >> ASM_REWRITE_TAC [] ] ]);

(******************************************************************************)
(*                                                                            *)
(*          2. Milner's unique solutions theorem for WEAK_EQUIV               *)
(*                                                                            *)
(******************************************************************************)

(* Lemma 7.12 in Milner's book [1]:
   If the variable X is guarded and sequential in G, and G{P/X} --a-> P', then there is
   an expression H such that G --a--> H, P' = H{P/X} and, for any Q, G{Q/X} --a-> H{Q/X}.
   Moreover H is sequential, and if a = tau then H is also guarded.
 *)
val WEAK_UNIQUE_SOLUTIONS_LEMMA = store_thm (
   "WEAK_UNIQUE_SOLUTIONS_LEMMA",
  ``!G. SG G /\ GSEQ G ==>
	!P a P'. TRANS (G P) a P' ==>
		 ?H. GSEQ H /\ ((a = tau) ==> SG H) /\
		     (P' = H P) /\ !Q. TRANS (G Q) a (H Q)``,
    HO_MATCH_MP_TAC SG_GSEQ_strong_induction
 >> BETA_TAC >> rpt STRIP_TAC (* 7 sub-goals here *)
 >| [ (* goal 1 (of 7) *)
      Q.EXISTS_TAC `\t. P'` >> BETA_TAC \\
      ASM_SIMP_TAC std_ss [GSEQ2] \\
      DISCH_TAC \\
      REWRITE_TAC [SG1],
      (* goal 2 (of 7), `a = tau` used here! *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      SIMP_TAC std_ss [Action_distinct_label] \\
      REWRITE_TAC [PREFIX],
      (* goal 3 (of 7) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 3 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` \\
      ASM_SIMP_TAC std_ss [PREFIX],
      (* goal 4 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G'` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 5 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e2` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 6 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e1` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 7 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e1` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e2` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ] ]);

(* The EPS version of WEAK_UNIQUE_SOLUTIONS_LEMMA.
   NOTE: the WEAK_TRANS version cannot be derived, because of the missing of SG in the middle.
 *)
val WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS = store_thm (
   "WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS",
  ``!G. SG G /\ GSEQ G ==>
	!P P'. EPS (G P) P' ==>
	       ?H. SG H /\ GSEQ H /\ (P' = H P) /\ !Q. EPS (G Q) (H Q)``,
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `GP = G P`
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P`, `P`)
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P'`, `P'`)
 >> Q.SPEC_TAC (`GP`, `GP`)
 >> HO_MATCH_MP_TAC EPS_strongind_right
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >- ( Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `GP` >> ASM_REWRITE_TAC [EPS_REFL] )
 >> RES_TAC
 >> Q.UNABBREV_TAC `GP`
 >> Q.PAT_X_ASSUM `!P''. Abbrev (G P = G P'') ==> X` K_TAC
 >> FULL_SIMP_TAC std_ss []
 >> IMP_RES_TAC (Q.SPEC `H` WEAK_UNIQUE_SOLUTIONS_LEMMA) (* lemma used here *)
 >> FULL_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `H''`
 >> ASM_REWRITE_TAC [EQ_SYM]
 >> GEN_TAC
 >> `EPS (G Q) (H Q) /\ EPS (H Q) (H'' Q)` by PROVE_TAC [ONE_TAU]
 >> IMP_RES_TAC EPS_TRANS);

val GSEQ_EPS_lemma = Q.prove (
   `!E P Q R H. SG E /\ GSEQ E /\ WEAK_EQUIV P (E P) /\ WEAK_EQUIV Q (E Q) /\ GSEQ H /\
		(R = \x y. ?H. GSEQ H /\ (WEAK_EQUIV x (H P)) /\ (WEAK_EQUIV y (H Q)))
    ==>	(!P'. EPS (H P) P' ==> ?Q'. EPS (H Q) Q' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q') /\
	(!Q'. EPS (H Q) Q' ==> ?P'. EPS (H P) P' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q')`,
    rpt GEN_TAC >> STRIP_TAC
 >> `WEAK_EQUIV (H P) ((H o E) P) /\ WEAK_EQUIV (H Q) ((H o E) Q)`
				by PROVE_TAC [WEAK_EQUIV_SUBST_GSEQ, o_DEF]
 >> `SG (H o E) /\ GSEQ (H o E)` by PROVE_TAC [SG_GSEQ_combin]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] WEAK_EQUIV_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `Q`)) \\
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] WEAK_EQUIV_EPS') \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV (H' Q) E1` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL],
      (* goal 2 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] WEAK_EQUIV_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `P`)) \\
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] WEAK_EQUIV_EPS') \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV E2 Q'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H' P` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL] ]);

(* Proposition 7.13 in Milner's book [1]:
   Let the expression E contains at most the variable X, and let X be guarded and sequential
   in E, then:
	If P = E{P/X} and Q = E{Q/X} then P = Q. (here "=" means WEAK_EQUIV)
   
   This proof doesn't use "bisimulation up to" at all, instead it constructed a bisimulation
   directly and then verify it against the very definition of WEAK_EQUIV. -- Chun Tian
 *)
val WEAK_UNIQUE_SOLUTIONS = store_thm (
   "WEAK_UNIQUE_SOLUTIONS",
  ``!E. SG E /\ GSEQ E ==>
	!P Q. WEAK_EQUIV P (E P) /\ WEAK_EQUIV Q (E Q) ==> WEAK_EQUIV P Q``,
    rpt STRIP_TAC
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\x y. ?H. GSEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)`
 >> BETA_TAC >> CONJ_TAC
 >- ( Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [] )
 >> REWRITE_TAC [WEAK_BISIM]
 >> Q.X_GEN_TAC `P'`
 >> Q.X_GEN_TAC `Q'`
 >> STRIP_TAC >> POP_ASSUM (MP_TAC o (BETA_RULE))
 >> STRIP_TAC
 >> Q.ABBREV_TAC `R = \x y. ?H. GSEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)`
 >> `WEAK_EQUIV (H P) ((H o E) P) /\ WEAK_EQUIV (H Q) ((H o E) Q)`
				 by PROVE_TAC [WEAK_EQUIV_SUBST_GSEQ, o_DEF]
 >> `SG (H o E) /\ GSEQ (H o E)` by PROVE_TAC [SG_GSEQ_combin]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      `?E2. WEAK_TRANS (H P) (label l) E2 /\ WEAK_EQUIV E1 E2`
				by PROVE_TAC [WEAK_EQUIV_TRANS_label] \\
      `?E3. WEAK_TRANS ((H o E) P) (label l) E3 /\ WEAK_EQUIV E2 E3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label] \\
      Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) P) (label l) E3`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `TRANS (H' P) (label l) E2'` by PROVE_TAC [] \\
      IMP_RES_TAC (Q.SPEC `H'` WEAK_UNIQUE_SOLUTIONS_LEMMA) \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `EPS (H'' P) E3` by PROVE_TAC [] \\
      MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] GSEQ_EPS_lemma) \\
      RW_TAC std_ss [] >> POP_ASSUM K_TAC \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      `WEAK_TRANS ((H o E) Q) (label l) Q''` by PROVE_TAC [WEAK_TRANS] \\
      `?Q3. WEAK_TRANS (H Q) (label l) Q3 /\ WEAK_EQUIV Q3 Q''`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      `?Q4. WEAK_TRANS Q' (label l) Q4 /\ WEAK_EQUIV Q4 Q3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      Q.EXISTS_TAC `Q4` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X E3 Q''` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM `R y' y` MP_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
      `WEAK_EQUIV y Q4` by PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H'''` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
(*
 (case 4)                              (case 1)
   P'  ======== tau =====> P4            P'  ----------------- l --------------> E1
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H P ======== eps =====> P3            H P ================= l ==============> E2
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H(E(P)) ==== eps =====> H' P         H(E(P)) ==eps=> E1'  --l-> E2'   ==eps=> E3   ~ y' ~~ H''' P
                           |                            (H' P)     (H'' P)              |
                           R                                                            R
                           |                                                            |
   H(E(Q)) ==== eps =====> E3 = H' Q    H(E(Q)) ==eps=> H' Q --l-> H'' Q ==eps=> Q'' ~~ y  ~~ H''' Q
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H Q ======== eps =====> E1           H Q ================== l ==============> Q3
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   Q'  -------- eps -----> E2            Q' ================== l ==============> Q4
 *)
      (* goal 2 (of 4) *)
      `?E1. WEAK_TRANS (H Q) (label l) E1 /\ WEAK_EQUIV E2 E1`
				by PROVE_TAC [WEAK_EQUIV_TRANS_label] \\
      `?E3. WEAK_TRANS ((H o E) Q) (label l) E3 /\ WEAK_EQUIV E1 E3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label] \\
      Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) Q) (label l) E3`
	(STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `TRANS (H' Q) (label l) E2'` by PROVE_TAC [] \\
      IMP_RES_TAC (Q.SPEC `H'` WEAK_UNIQUE_SOLUTIONS_LEMMA) \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `EPS (H'' Q) E3` by PROVE_TAC [] \\
      MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] GSEQ_EPS_lemma) \\
      RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!P'. EPS (H'' P) P' ==> X` K_TAC \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      `WEAK_TRANS ((H o E) P) (label l) P''` by PROVE_TAC [WEAK_TRANS] \\
      `?P3. WEAK_TRANS (H P) (label l) P3 /\ WEAK_EQUIV P3 P''`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      `?P4. WEAK_TRANS P' (label l) P4 /\ WEAK_EQUIV P4 P3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      Q.EXISTS_TAC `P4` >> ASM_REWRITE_TAC [] \\
      Q.PAT_X_ASSUM `X P'' E3` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM `R y' y` MP_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
      Q.EXISTS_TAC `H'''` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
(*
 (case 3)                              (case 2)
   P'  -------- tau -----> E1            P'  ================== l ==============> P4
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H P ======== eps =====> E2            H P ================== l ==============> P3
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H(E(P)) ==== eps =====> E3 = H' P    H(E(P)) ==eps=> H' P --l-> H'' P ==eps=> P'' ~~ y' ~~ H''' P
                           |                                                            |
                           R                                                            R
                           |                           (H' Q)     (H'' Q)               |
   H(E(Q)) ==== eps =====> H' Q         H(E(Q)) ==eps=> E1'  --l-> E2'   ==eps=> E3   ~ y  ~~ H''' Q
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H Q ======== eps =====> Q3            H Q ================== l ==============> E1
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   Q'  ======== eps =====> Q4            Q'  ------------------ l --------------> E2
 *)
      (* goal 3 (of 4) *)
      `?E2. EPS (H P) E2 /\ WEAK_EQUIV E1 E2` by PROVE_TAC [WEAK_EQUIV_TRANS_tau] \\
      `?E3. EPS ((H o E) P) E3 /\ WEAK_EQUIV E2 E3` by PROVE_TAC [WEAK_EQUIV_EPS] \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `?Q3. EPS (H Q) Q3 /\ WEAK_EQUIV Q3 (H' Q)` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      `?Q4. EPS Q' Q4 /\ WEAK_EQUIV Q4 Q3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      Q.EXISTS_TAC `Q4` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `R` >> BETA_TAC \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
      (* goal 4 (of 4) *)
      `?E1. EPS (H Q) E1 /\ WEAK_EQUIV E2 E1` by PROVE_TAC [WEAK_EQUIV_TRANS_tau] \\
      `?E3. EPS ((H o E) Q) E3 /\ WEAK_EQUIV E1 E3` by PROVE_TAC [WEAK_EQUIV_EPS] \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `?P3. EPS (H P) P3 /\ WEAK_EQUIV P3 (H' P)` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      `?P4. EPS P' P4 /\ WEAK_EQUIV P4 P3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      Q.EXISTS_TAC `P4` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `R` >> BETA_TAC \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [] \\
      PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] ]);

(******************************************************************************)
(*                                                                            *)
(*           3. Milner's unique solutions theorem for OBS_CONGR               *)
(*                                                                            *)
(******************************************************************************)

val OBS_UNIQUE_SOLUTIONS_LEMMA = store_thm (
   "OBS_UNIQUE_SOLUTIONS_LEMMA",
  ``!G. SG G /\ SEQ G ==>
	!P a P'. TRANS (G P) a P' ==>
		 ?H. SEQ H /\ ((a = tau) ==> SG H) /\
		     (P' = H P) /\ !Q. TRANS (G Q) a (H Q)``,
    HO_MATCH_MP_TAC SG_SEQ_strong_induction
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.EXISTS_TAC `\t. P'` >> BETA_TAC \\
      ASM_SIMP_TAC std_ss [SEQ2] \\
      DISCH_TAC \\
      REWRITE_TAC [SG1],
      (* goal 2 (of 4), `a = tau` used here! *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      SIMP_TAC std_ss [Action_distinct_label] \\
      REWRITE_TAC [PREFIX],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      FULL_SIMP_TAC std_ss [] \\
      NTAC 3 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `G` \\
      ASM_SIMP_TAC std_ss [PREFIX],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `H` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> ASM_REWRITE_TAC [],
        (* goal 4.2 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `H` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> ASM_REWRITE_TAC [] ] ]);

(* The EPS version of OBS_UNIQUE_SOLUTIONS_LEMMA.
   NOTE: the WEAK_TRANS version cannot be derived, because of the missing of SG in the middle.
 *)
val OBS_UNIQUE_SOLUTIONS_LEMMA_EPS = store_thm (
   "OBS_UNIQUE_SOLUTIONS_LEMMA_EPS",
  ``!G. SG G /\ SEQ G ==>
	!P P'. EPS (G P) P' ==>
	       ?H. SG H /\ SEQ H /\ (P' = H P) /\ !Q. EPS (G Q) (H Q)``,
    rpt STRIP_TAC
 >> Q.ABBREV_TAC `GP = G P`
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P`, `P`)
 >> POP_ASSUM MP_TAC
 >> Q.SPEC_TAC (`P'`, `P'`)
 >> Q.SPEC_TAC (`GP`, `GP`)
 >> HO_MATCH_MP_TAC EPS_strongind_right
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >- ( Q.EXISTS_TAC `G` >> ASM_REWRITE_TAC [] \\
      Q.UNABBREV_TAC `GP` >> ASM_REWRITE_TAC [EPS_REFL] )
 >> RES_TAC
 >> Q.UNABBREV_TAC `GP`
 >> Q.PAT_X_ASSUM `!P''. Abbrev (G P = G P'') ==> X` K_TAC
 >> FULL_SIMP_TAC std_ss []
 >> IMP_RES_TAC (Q.SPEC `H` OBS_UNIQUE_SOLUTIONS_LEMMA) (* lemma used here *)
 >> FULL_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `H''`
 >> ASM_REWRITE_TAC [EQ_SYM]
 >> GEN_TAC
 >> `EPS (G Q) (H Q) /\ EPS (H Q) (H'' Q)` by PROVE_TAC [ONE_TAU]
 >> IMP_RES_TAC EPS_TRANS);

(* These lemmas may apply at the final stage, it doesn't require (SG H), just (SEQ H) *)
val SEQ_EPS_lemma = Q.prove (
   `!E P Q R H. SG E /\ SEQ E /\ OBS_CONGR P (E P) /\ OBS_CONGR Q (E Q) /\ SEQ H /\
		(R = \x y. ?H. SEQ H /\ (WEAK_EQUIV x (H P)) /\ (WEAK_EQUIV y (H Q)))
    ==>	(!P'. EPS (H P) P' ==> ?Q'. EPS (H Q) Q' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q') /\
	(!Q'. EPS (H Q) Q' ==> ?P'. EPS (H P) P' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q')`,
    rpt GEN_TAC >> STRIP_TAC
 >> `OBS_CONGR (H P) ((H o E) P) /\ OBS_CONGR (H Q) ((H o E) Q)`
				by PROVE_TAC [OBS_CONGR_SUBST_SEQ, o_DEF]
 >> `SG (H o E) /\ SEQ (H o E)` by PROVE_TAC [SG_SEQ_combin]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `Q`)) \\
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS') \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV (H' Q) E1` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL],
      (* goal 2 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `P`)) \\
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS') \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV E2 Q'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H' P` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL] ]);

(* Proposition 7.13 in Milner's book [1]:
   Let the expression E contains at most the variable X, and let X be guarded and sequential
   in E, then:
	If P = E{P/X} and Q = E{Q/X} then P = Q. (here "=" means OBS_CONGR)
   
   This proof doesn't use "bisimulation up to" at all, instead it constructed a bisimulation
   directly and then verify it against OBS_CONGR_BY_WEAK_BISIM. -- Chun Tian
 *)
val OBS_UNIQUE_SOLUTIONS = store_thm (
   "OBS_UNIQUE_SOLUTIONS",
  ``!E. SG E /\ SEQ E ==>
	!P Q. OBS_CONGR P (E P) /\ OBS_CONGR Q (E Q) ==> OBS_CONGR P Q``,
    REPEAT STRIP_TAC
 >> irule OBS_CONGR_BY_WEAK_BISIM
 >> Q.EXISTS_TAC `\x y. ?H. SEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)`
 >> Rev CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [WEAK_BISIM] \\
      Q.X_GEN_TAC `P'` \\
      Q.X_GEN_TAC `Q'` \\
      STRIP_TAC >> POP_ASSUM (MP_TAC o (BETA_RULE)) \\
      STRIP_TAC \\
      Q.ABBREV_TAC `R = \x y. ?H. SEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)` \\
      `OBS_CONGR (H P) ((H o E) P) /\ OBS_CONGR (H Q) ((H o E) Q)`
				 by PROVE_TAC [OBS_CONGR_SUBST_SEQ, o_DEF] \\
      `SG (H o E) /\ SEQ (H o E)` by PROVE_TAC [SG_SEQ_combin] \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 1 (of 4) *)
        `?E2. WEAK_TRANS (H P) (label l) E2 /\ WEAK_EQUIV E1 E2`
				by PROVE_TAC [WEAK_EQUIV_TRANS_label] \\
        `?E3. WEAK_TRANS ((H o E) P) (label l) E3 /\ WEAK_EQUIV E2 E3`
				by PROVE_TAC [OBS_CONGR_WEAK_TRANS] \\
        Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) P) (label l) E3`
	  (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `TRANS (H' P) (label l) E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H'` OBS_UNIQUE_SOLUTIONS_LEMMA) \\
        NTAC 7 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `EPS (H'' P) E3` by PROVE_TAC [] \\
        MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] SEQ_EPS_lemma) \\
        RW_TAC std_ss [] >> POP_ASSUM K_TAC \\
        RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
        `WEAK_TRANS ((H o E) Q) (label l) Q''` by PROVE_TAC [WEAK_TRANS] \\
        `?Q3. WEAK_TRANS (H Q) (label l) Q3 /\ WEAK_EQUIV Q3 Q''`
				by PROVE_TAC [OBS_CONGR_WEAK_TRANS'] \\
        `?Q4. WEAK_TRANS Q' (label l) Q4 /\ WEAK_EQUIV Q4 Q3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
        Q.EXISTS_TAC `Q4` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X E3 Q''` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
        `WEAK_EQUIV y Q4` by PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] \\
        Q.EXISTS_TAC `H'''` >> ASM_REWRITE_TAC [] \\
        PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
(*
 (goal 1.4)                            (goal 1.1)
   P'  ======== tau =====> P4            P'  ----------------- l --------------> E1
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H P ======== eps =====> P3            H P ================= l ==============> E2
   |                       |             |                                       |
   ~~                      ~~            ~~c                                     ~~
   |                       |             |                                       |
   H(E(P)) ==== eps =====> H' P         H(E(P)) ==eps=> E1'  --l-> E2'   ==eps=> E3  ~~ y' ~~ H''' P
                           |                            (H' P)     (H'' P)              |
                           R                                                            R
                           |                                                            |
   H(E(Q)) ==== eps =====> E3 = H' Q    H(E(Q)) ==eps=> H' Q --l-> H'' Q ==eps=> Q'' ~~ y  ~~ H''' Q
   |                       |             |                                       |
   ~~                      ~~            ~~c                                     ~~
   |                       |             |                                       |
   H Q ======== eps =====> E1           H Q ================== l ==============> Q3
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   Q'  -------- eps -----> E2            Q' ================== l ==============> Q4
 *)
        (* goal 2 (of 4) *)
        `?E1. WEAK_TRANS (H Q) (label l) E1 /\ WEAK_EQUIV E2 E1`
				by PROVE_TAC [WEAK_EQUIV_TRANS_label] \\
        `?E3. WEAK_TRANS ((H o E) Q) (label l) E3 /\ WEAK_EQUIV E1 E3`
				by PROVE_TAC [OBS_CONGR_WEAK_TRANS] \\
        Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) Q) (label l) E3`
	  (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `TRANS (H' Q) (label l) E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H'` OBS_UNIQUE_SOLUTIONS_LEMMA) \\
        NTAC 7 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `EPS (H'' Q) E3` by PROVE_TAC [] \\
        MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] SEQ_EPS_lemma) \\
        RW_TAC std_ss [] \\
        Q.PAT_X_ASSUM `!P'. EPS (H'' P) P' ==> X` K_TAC \\
        RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
        `WEAK_TRANS ((H o E) P) (label l) P''` by PROVE_TAC [WEAK_TRANS] \\
        `?P3. WEAK_TRANS (H P) (label l) P3 /\ WEAK_EQUIV P3 P''`
				by PROVE_TAC [OBS_CONGR_WEAK_TRANS'] \\
        `?P4. WEAK_TRANS P' (label l) P4 /\ WEAK_EQUIV P4 P3`
				by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
        Q.EXISTS_TAC `P4` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X P'' E3` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
        Q.EXISTS_TAC `H'''` >> ASM_REWRITE_TAC [] \\
        PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
(*
 (goal 1.3)                            (goal 1.2)
   P'  -------- tau -----> E1            P'  ================= l ==============> P4
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H P ======== eps =====> E2            H P ================= l ==============> P3
   |                       |             |                                       |
   ~~c                     ~~            ~~c                                     ~~
   |                       |             |                                       |
   H(E(P)) ==== eps =====> E3 = H' P    H(E(P)) ==eps=> H' P --l-> H'' P ==eps=> P'' ~~ y' ~~ H''' P
                           |                                                            |
                           R                                                            R
                           |                           (H' Q)     (H'' Q)               |
   H(E(Q)) ==== eps =====> H' Q         H(E(Q)) ==eps=> E1'  --l-> E2'   ==eps=> E3  ~~ y  ~~ H''' Q
   |                       |             |                                       |
   ~~c                     ~~            ~~c                                     ~~
   |                       |             |                                       |
   H Q ======== eps =====> Q3            H Q ================= l ==============> E1
   |                       |             |                                       |
   ~~c                     ~~            ~~                                      ~~
   |                       |             |                                       |
   Q'  ======== eps =====> Q4            Q'  ----------------- l --------------> E2
 *)
        (* goal 3 (of 4) *)
        `?E2. EPS (H P) E2 /\ WEAK_EQUIV E1 E2` by PROVE_TAC [WEAK_EQUIV_TRANS_tau] \\
        `?E3. EPS ((H o E) P) E3 /\ WEAK_EQUIV E2 E3` by PROVE_TAC [OBS_CONGR_EPS] \\
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `?Q3. EPS (H Q) Q3 /\ WEAK_EQUIV Q3 (H' Q)` by PROVE_TAC [OBS_CONGR_EPS'] \\
        `?Q4. EPS Q' Q4 /\ WEAK_EQUIV Q4 Q3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
        Q.EXISTS_TAC `Q4` >> ASM_REWRITE_TAC [] \\
        Q.UNABBREV_TAC `R` >> BETA_TAC \\
        Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [] \\
        PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
        (* goal 4 (of 4) *)
        `?E1. EPS (H Q) E1 /\ WEAK_EQUIV E2 E1` by PROVE_TAC [WEAK_EQUIV_TRANS_tau] \\
        `?E3. EPS ((H o E) Q) E3 /\ WEAK_EQUIV E1 E3` by PROVE_TAC [OBS_CONGR_EPS] \\
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `?P3. EPS (H P) P3 /\ WEAK_EQUIV P3 (H' P)` by PROVE_TAC [OBS_CONGR_EPS'] \\
        `?P4. EPS P' P4 /\ WEAK_EQUIV P4 P3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
        Q.EXISTS_TAC `P4` >> ASM_REWRITE_TAC [] \\
        Q.UNABBREV_TAC `R` >> BETA_TAC \\
        Q.EXISTS_TAC `H'` >> ASM_REWRITE_TAC [] \\
        PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] ],
      (* goal 2 (of 2) *)
      Q.ABBREV_TAC `R = \x y. ?H. SEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)` \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        `?E2. WEAK_TRANS (E P) u E2 /\ WEAK_EQUIV E1 E2`
				by PROVE_TAC [OBS_CONGR_HALF_LEFT] \\
        Q.PAT_X_ASSUM `WEAK_TRANS (E P) u E2`
	  (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
        IMP_RES_TAC (Q.SPEC `E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `TRANS (H P) u E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H` OBS_UNIQUE_SOLUTIONS_LEMMA) \\
        NTAC 5 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `EPS (H' P) E2` by PROVE_TAC [] \\
        MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H'`] SEQ_EPS_lemma) \\
        RW_TAC std_ss [] >> POP_ASSUM K_TAC \\
        RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
        `WEAK_TRANS (E Q) u Q'` by PROVE_TAC [WEAK_TRANS] \\
        `?Q''. WEAK_TRANS Q u Q'' /\ WEAK_EQUIV Q'' Q'`
				by PROVE_TAC [OBS_CONGR_WEAK_TRANS'] \\
        Q.EXISTS_TAC `Q''` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X E2 Q'` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
        Q.EXISTS_TAC `H''` >> ASM_REWRITE_TAC [] \\
        PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM],
(*
  (goal 2.1)
      P ------------------- u --------------> E1
      |                                       |
     ~~c                                     ~~
      |                                       |
     E(P) ====eps==> E1' ---u-> E2'  ==eps==> E2 ~~ y' ~~ H'' P
                    (H P)      (H' P)               |
                                                    R
                                                    |
     E(Q) ====eps==> H Q ---u-> H' Q ==eps==> Q' ~~ y  ~~ H'' Q
      |                                       |
     ~~c                                     ~~
      |                                       |
      Q =================== u ==============> Q''
 *)
        (* goal 2.2 (of 2) *)
        `?E1. WEAK_TRANS (E Q) u E1 /\ WEAK_EQUIV E2 E1`
				by PROVE_TAC [OBS_CONGR_HALF_LEFT] \\
        Q.PAT_X_ASSUM `WEAK_TRANS (E Q) u E1`
	  (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
        IMP_RES_TAC (Q.SPEC `E` OBS_UNIQUE_SOLUTIONS_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `TRANS (H Q) u E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H` OBS_UNIQUE_SOLUTIONS_LEMMA) \\
        NTAC 5 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `EPS (H' Q) E1` by PROVE_TAC [] \\
        MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H'`] SEQ_EPS_lemma) \\
        RW_TAC std_ss [] \\
        Q.PAT_X_ASSUM `!P'. EPS (H' P) P' ==> X` K_TAC \\
        RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
        `WEAK_TRANS (E P) u P'` by PROVE_TAC [WEAK_TRANS] \\
        `?P''. WEAK_TRANS P u P'' /\ WEAK_EQUIV P'' P'`
				by PROVE_TAC [OBS_CONGR_WEAK_TRANS'] \\
        Q.EXISTS_TAC `P''` >> ASM_REWRITE_TAC [] \\
        Q.PAT_X_ASSUM `X P' E1` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
        Q.EXISTS_TAC `H''` >> ASM_REWRITE_TAC [] \\
        PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] ] ]); 
(*
  (goal 2.2)
      P ------------------- u --------------> P''
      |                                       |
     ~~c                                     ~~
      |                                       |
     E(P) ====eps==> H P ---u-> H' P ==eps==> P' ~~ y' ~~ H'' P
                                                    |
                                                    R
                    (H Q)      (H' Q)               |
     E(Q) ====eps==> E1' ---u-> E2' ===eps==> E1 ~~ y  ~~ H'' Q
      |                                       |
     ~~c                                     ~~
      |                                       |
      Q ------------------- u --------------> E2
 *)

(******************************************************************************)
(*                                                                            *)
(*            4. Unique solutions of contractions for WEAK_EQUIV              *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: the lemma works for any precongruence relation *)
val unfolding_lemma1 = store_thm (
   "unfolding_lemma1",
  ``!E C P. GCONTEXT E /\ GCONTEXT C /\ P contracts (E P) ==>
	!n. (C P) contracts (C o (FUNPOW E n)) P``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> irule contracts_precongruence_applied >- ASM_REWRITE_TAC []
 >> Q.SPEC_TAC (`n`, `n`)
 >> Induct >- REWRITE_TAC [FUNPOW, contracts_REFL]
 >> REWRITE_TAC [FUNPOW_SUC]
 >> Q.ABBREV_TAC `Q = FUNPOW E n P`
 >> `(E P) contracts (E Q)` by PROVE_TAC [contracts_precongruence_applied]
 >> IMP_RES_TAC contracts_TRANS);

(* This can be merged to HOL's arithmeticTheory *)
val FUNPOW_SUC_LEFT = store_thm (
   "FUNPOW_SUC_LEFT", ``!f n. FUNPOW f (SUC n) = (FUNPOW f n) o f``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [FUN_EQ_THM, o_DEF] >> BETA_TAC
 >> GEN_TAC
 >> `FUNPOW f (n + 1) x = FUNPOW f n (FUNPOW f 1 x)` by PROVE_TAC [FUNPOW_ADD]
 >> FULL_SIMP_TAC arith_ss [FUNPOW_1, ADD1]);

(* |- !f n x. FUNPOW f (SUC n) x = FUNPOW f n (f x) *)
val FUNPOW_SUC_LEFT' = save_thm (
   "FUNPOW_SUC_LEFT'", BETA_RULE (REWRITE_RULE [FUN_EQ_THM, o_DEF] FUNPOW_SUC_LEFT));

val unfolding_lemma2 = store_thm (
   "unfolding_lemma2",
  ``!E. WGS E ==> !P u P'. TRANS (E P) u P' ==>
	?C'. GCONTEXT C' /\ (P' = C' P) /\ !Q. TRANS (E Q) u (C' Q)``,
    HO_MATCH_MP_TAC WGS_strongind
 >> BETA_TAC >> REWRITE_TAC [ETA_AX]
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      Q.EXISTS_TAC `\t. P'` >> ASM_REWRITE_TAC [GCONTEXT2],
      (* goal 2 (of 6) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `e` >> ASM_REWRITE_TAC [] \\
      GEN_TAC >> REWRITE_TAC [PREFIX],
      (* goal 3 (of 6) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        IMP_RES_TAC WGS_IS_GCONTEXT \\
        Q.EXISTS_TAC `E` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        IMP_RES_TAC WGS_IS_GCONTEXT \\
        Q.EXISTS_TAC `E'` >> ASM_REWRITE_TAC [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> REWRITE_TAC [PREFIX] ],
      (* goal 4 (of 6) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 4.1 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (C' t) (E' t)` >> BETA_TAC \\
	CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT5 >> ASM_REWRITE_TAC [] \\
		      MATCH_MP_TAC WGS_IS_GCONTEXT >> ASM_REWRITE_TAC [] ) \\
	FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR1 >> ASM_REWRITE_TAC [],
	(* goal 4.2 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (E t) (C' t)` >> BETA_TAC \\
	CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT5 >> ASM_REWRITE_TAC [] \\
		      MATCH_MP_TAC WGS_IS_GCONTEXT >> ASM_REWRITE_TAC [] ) \\
	FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR2 >> ASM_REWRITE_TAC [],
	(* goal 4.3 (of 3) *)
	RES_TAC \\
        Q.EXISTS_TAC `\t. par (C'' t) (C' t)` >> BETA_TAC \\
	CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT5 >> ASM_REWRITE_TAC [] ) \\
	FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR3 \\
	Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ],
      (* goal 5 (of 6) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
	FULL_SIMP_TAC std_ss [] >> RES_TAC \\
	Q.EXISTS_TAC `\t. restr L (C' t)` >> BETA_TAC \\
	CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT6 >> ASM_REWRITE_TAC [] ) \\
	ASM_REWRITE_TAC [] \\
	GEN_TAC >> MATCH_MP_TAC RESTR >> ASM_REWRITE_TAC [],
	(* goal 5.2 (of 2) *)
	FULL_SIMP_TAC std_ss [] >> RES_TAC \\
	Q.EXISTS_TAC `\t. restr L (C' t)` >> BETA_TAC \\
	CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT6 >> ASM_REWRITE_TAC [] ) \\
	ASM_REWRITE_TAC [] \\
	GEN_TAC >> MATCH_MP_TAC RESTR >> ASM_REWRITE_TAC [] \\
	Q.EXISTS_TAC `l` >> ASM_REWRITE_TAC [] ],
      (* goal 6 (of 6) *)
      IMP_RES_TAC TRANS_RELAB >> RES_TAC \\
      Q.EXISTS_TAC `\t. relab (C' t) rf` >> BETA_TAC \\
      CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT7 >> ASM_REWRITE_TAC [] ) \\
      ASM_REWRITE_TAC [] \\
      GEN_TAC >> MATCH_MP_TAC RELABELING >> ASM_REWRITE_TAC [] ]);

val unfolding_lemma3 = store_thm (
   "unfolding_lemma3",
  ``!C E. GCONTEXT C /\ WGS E ==>
	!P x P'. TRANS (C (E P)) x P' ==>
		 ?C'. GCONTEXT C' /\ (P' = C' P) /\ !Q. TRANS (C (E Q)) x (C' Q)``,
    rpt STRIP_TAC
 >> IMP_RES_TAC GCONTEXT_WGS_combin
 >> Know `C (E P) = (C o E) P` >- SIMP_TAC std_ss [o_DEF]
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM `TRANS (C (E P)) x P'` MP_TAC
 >> ASM_REWRITE_TAC [] >> DISCH_TAC
 >> IMP_RES_TAC unfolding_lemma2
 >> POP_ASSUM K_TAC
 >> Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC []
 >> GEN_TAC >> POP_ASSUM MP_TAC
 >> KILL_TAC
 >> REWRITE_TAC [o_DEF] >> BETA_TAC
 >> RW_TAC std_ss []);

(* NOTE: the lemma works for not only WGS but any weakly guarded expressions *)
val unfolding_lemma4 = store_thm (
   "unfolding_lemma4",
  ``!C E n xs P' P. GCONTEXT C /\ WGS E /\
	TRACE ((C o FUNPOW E n) P) xs P' /\ (LENGTH xs <= n) ==>
	?C'. GCONTEXT C' /\ (P' = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs (C' Q)``,
    NTAC 2 GEN_TAC
 >> Induct_on `n`
 >- ( REWRITE_TAC [o_DEF, FUNPOW] >> BETA_TAC >> rpt STRIP_TAC \\
      Q.EXISTS_TAC `C` >> ASM_REWRITE_TAC [] \\
      POP_ASSUM MP_TAC \\
      SIMP_TAC arith_ss [] \\
      REWRITE_TAC [GSYM NULL_LENGTH, NULL_EQ] \\
      DISCH_TAC \\
      FULL_SIMP_TAC std_ss [TRACE_NIL] )
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `TRACE X xs P'` MP_TAC
 >> Know `(C o (FUNPOW E (SUC n))) P = (C o (FUNPOW E n)) (E P)`
 >- ( REWRITE_TAC [o_DEF, FUNPOW_SUC_LEFT'] >> BETA_TAC >> RW_TAC std_ss [] )
 >> Rewr >> DISCH_TAC
 >> IMP_RES_TAC TRACE_cases2
 >> Cases_on `xs`
 >- ( REV_FULL_SIMP_TAC std_ss [NULL] \\
      `LENGTH (epsilon :'b Action list) <= n` by FULL_SIMP_TAC arith_ss [LENGTH] \\
      Q.PAT_X_ASSUM `!xs P' P. X ==> X'`
	(MP_TAC o (Q.SPECL [`[] :'b Action list`, `P'`, `(E :('a, 'b) context) P`])) \\
      RW_TAC std_ss [] >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C' o E` \\
      CONJ_TAC >- ( IMP_RES_TAC WGS_IS_GCONTEXT >> MATCH_MP_TAC GCONTEXT_combin \\
		    ASM_REWRITE_TAC [] ) \\
      CONJ_TAC >- ( KILL_TAC >> REWRITE_TAC [o_DEF] >> RW_TAC std_ss [] ) \\
      GEN_TAC >> REWRITE_TAC [FUNPOW_SUC_LEFT', o_DEF] >> BETA_TAC \\
      ASM_REWRITE_TAC [] )
 >> FULL_SIMP_TAC list_ss []
 >> `LENGTH (FRONT (h::t)) <= n` by PROVE_TAC [LENGTH_FRONT_CONS]
 >> Q.ABBREV_TAC `xs = FRONT (h::t)`
 >> Q.ABBREV_TAC `x = LAST (h::t)`
 >> Q.PAT_X_ASSUM `!xs P'' P'''. X ==> X'`
	(MP_TAC o (Q.SPECL [`xs`, `u`, `(E :('a, 'b) context) P`]))
 >> RW_TAC std_ss []
 >> IMP_RES_TAC (Q.SPECL [`C'`, `E`] unfolding_lemma3)
 >> NTAC 5 (POP_ASSUM K_TAC)
 >> Q.EXISTS_TAC `C''` >> ASM_REWRITE_TAC []
 >> GEN_TAC
 >> ONCE_REWRITE_TAC [TRACE_cases2]
 >> REWRITE_TAC [NULL]
 >> Q.EXISTS_TAC `C' (E Q)`
 >> Q.UNABBREV_TAC `x` >> ASM_REWRITE_TAC []
 >> REWRITE_TAC [FUNPOW_SUC_LEFT']
 >> Q.UNABBREV_TAC `xs` >> ASM_REWRITE_TAC []);

(* Lemma 3.9 of [2] *)
val UNIQUE_SOLUTIONS_OF_CONTRACTIONS_LEMMA = store_thm (
   "UNIQUE_SOLUTIONS_OF_CONTRACTIONS_LEMMA",
  ``!(P :('a, 'b) CCS) (Q :('a, 'b) CCS).
	(?E. WGS E /\ P contracts (E P) /\ Q contracts (E Q)) ==>
	!(C :('a, 'b) context). GCONTEXT C ==>
	    (!l R. WEAK_TRANS (C P) (label l) R ==>
		?C'. GCONTEXT C' /\ R contracts (C' P) /\
		     (WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C Q) (C' Q)) /\
	    (!R. WEAK_TRANS (C P) tau R ==>
		?C'. GCONTEXT C' /\ R contracts (C' P) /\
		     (WEAK_EQUIV O EPS) (C Q) (C' Q))``,
    NTAC 5 STRIP_TAC
 (* Part 1: construct C'' which is a GCONTEXT *)
 >> IMP_RES_TAC WGS_IS_GCONTEXT
 >> Q.ABBREV_TAC `C'' = \n. C o (FUNPOW E n)`
 >> Know `!n. GCONTEXT (C'' n)`
 >- ( Q.UNABBREV_TAC `C''` >> BETA_TAC \\
      Induct_on `n` >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        ASM_REWRITE_TAC [o_DEF, FUNPOW, ETA_AX],
        (* goal 1.2 (of 2) *)
        REWRITE_TAC [FUNPOW_SUC_LEFT, o_ASSOC] \\
        MATCH_MP_TAC GCONTEXT_combin \\
        ASM_REWRITE_TAC [] ] )
 >> DISCH_TAC
 (* Part 2: property of C'' on P and Q *)
 >> `!n. (C P) contracts (C'' n P)`
	by (Q.UNABBREV_TAC `C''` >> BETA_TAC >> PROVE_TAC [unfolding_lemma1])
 >> `!n. (C Q) contracts (C'' n Q)`
	by (Q.UNABBREV_TAC `C''` >> BETA_TAC >> PROVE_TAC [unfolding_lemma1])
 (* Part 3 *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [Action_distinct_label] \\
      `(C P) contracts (C'' (LENGTH xs) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP contracts_AND_TRACE_label)) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH xs` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs'' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs'' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> ASM_REWRITE_TAC [] ) >> STRIP_TAC \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) contracts ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      Know `WEAK_TRANS (C (FUNPOW E n Q)) (label l) (C' Q)`
      >- ( REWRITE_TAC [WEAK_TRANS_AND_TRACE, Action_distinct_label] \\
	   Q.EXISTS_TAC `xs''` >> ASM_REWRITE_TAC [] \\
	   MATCH_MP_TAC UNIQUE_LABEL_NOT_NULL \\
	   Q.EXISTS_TAC `label l` >> ASM_REWRITE_TAC [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC contracts_WEAK_TRANS_label' \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [] \\
      `(C P) contracts (C'' (LENGTH xs) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP contracts_AND_TRACE_tau)) \\ (* diff here *)
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH xs` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs'' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs'' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> ASM_REWRITE_TAC [] ) >> STRIP_TAC \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) contracts ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      Know `EPS (C (FUNPOW E n Q)) (C' Q)` (* diff here *)
      >- ( REWRITE_TAC [EPS_AND_TRACE] \\
	   Q.EXISTS_TAC `xs''` >> ASM_REWRITE_TAC [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC contracts_EPS' \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ]);

(* Theorem 3.10 of [2], the proof relies on above lemma, and "contracts_IMP_WEAK_EQUIV",
   the definition of contraction is not used.
 *)
val UNIQUE_SOLUTIONS_OF_CONTRACTIONS = store_thm (
   "UNIQUE_SOLUTIONS_OF_CONTRACTIONS",
  ``!E. WGS E ==>
	!P Q. P contracts (E P) /\ Q contracts (E Q) ==> WEAK_EQUIV P Q``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\R S. ?C. GCONTEXT C /\ WEAK_EQUIV R (C P) /\ WEAK_EQUIV S (C Q)`
 >> BETA_TAC >> CONJ_TAC
 >- ( Q.EXISTS_TAC `E` \\
      CONJ_TAC >- IMP_RES_TAC WGS_IS_GCONTEXT \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      ASM_REWRITE_TAC [] )
 >> REWRITE_TAC [WEAK_BISIM]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
	(ASSUME_TAC o (Q.SPECL [`l`, `E1`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E' (label l) E1 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTIONS_OF_CONTRACTIONS_LEMMA) \\
      `!l R. WEAK_TRANS (C P) (label l) R ==>
           ?C'. GCONTEXT C' /\ R contracts (C' P) /\
		(WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C Q) (C' Q)`
	by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ P contracts (E P) /\ Q contracts (E Q)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
	(ASSUME_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS (C P) (label l) R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `WEAK_TRANS (C Q) (label l) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
	(ASSUME_TAC o (Q.SPECL [`l`, `E2`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E'' (label l) E2 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTIONS_OF_CONTRACTIONS_LEMMA) \\
      `!l R. WEAK_TRANS (C Q) (label l) R ==>
           ?C'. GCONTEXT C' /\ R contracts (C' Q) /\
		(WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C P) (C' P)`
	by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ Q contracts (E Q) /\ P contracts (E P)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
	(ASSUME_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS (C Q) (label l) R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `WEAK_TRANS (C P) (label l) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 3 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
			    (ASSUME ``WEAK_EQUIV E' ((C :('a, 'b) context) P)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E''` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> ASM_REWRITE_TAC [] ) \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTIONS_OF_CONTRACTIONS_LEMMA) \\
      `!R. WEAK_TRANS (C P) tau R ==>
           ?C'. GCONTEXT C' /\ R contracts (C' P) /\
		(WEAK_EQUIV O EPS) (C Q) (C' Q)` by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ P contracts (E P) /\ Q contracts (E Q)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
	(ASSUME_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      Q.PAT_X_ASSUM `!R. WEAK_TRANS (C P) tau R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `EPS (C Q) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 4 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
			    (ASSUME ``WEAK_EQUIV E'' ((C :('a, 'b) context) Q)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> ASM_REWRITE_TAC [] ) \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTIONS_OF_CONTRACTIONS_LEMMA) \\
      `!R. WEAK_TRANS (C Q) tau R ==>
           ?C'. GCONTEXT C' /\ R contracts (C' Q) /\
		(WEAK_EQUIV O EPS) (C P) (C' P)` by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ Q contracts (E Q) /\ P contracts (E P)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
	(ASSUME_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      Q.PAT_X_ASSUM `!R. WEAK_TRANS (C Q) tau R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `EPS (C P) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS] ]);

(******************************************************************************)
(*                                                                            *)
(*            5. Unique solutions of expansions for WEAK_EQUIV                *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: the lemma works for any precongruence relation *)
val unfolding_lemma1' = store_thm (
   "unfolding_lemma1'",
  ``!E C P. GCONTEXT E /\ GCONTEXT C /\ P expands (E P) ==>
	!n. (C P) expands (C o (FUNPOW E n)) P``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> irule expands_precongruence_applied >- ASM_REWRITE_TAC []
 >> Q.SPEC_TAC (`n`, `n`)
 >> Induct >- REWRITE_TAC [FUNPOW, expands_REFL]
 >> REWRITE_TAC [FUNPOW_SUC]
 >> Q.ABBREV_TAC `Q = FUNPOW E n P`
 >> `(E P) expands (E Q)` by PROVE_TAC [expands_precongruence_applied]
 >> IMP_RES_TAC expands_TRANS);

val UNIQUE_SOLUTIONS_OF_EXPANSIONS_LEMMA = store_thm (
   "UNIQUE_SOLUTIONS_OF_EXPANSIONS_LEMMA",
  ``!(P :('a, 'b) CCS) (Q :('a, 'b) CCS).
	(?E. WGS E /\ P expands (E P) /\ Q expands (E Q)) ==>
	!(C :('a, 'b) context). GCONTEXT C ==>
	    (!l R. WEAK_TRANS (C P) (label l) R ==>
		?C'. GCONTEXT C' /\ R expands (C' P) /\
		     (WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C Q) (C' Q)) /\
	    (!R. WEAK_TRANS (C P) tau R ==>
		?C'. GCONTEXT C' /\ R expands (C' P) /\
		     (WEAK_EQUIV O EPS) (C Q) (C' Q))``,
    NTAC 5 STRIP_TAC
 (* Part 1: construct C'' which is a GCONTEXT *)
 >> IMP_RES_TAC WGS_IS_GCONTEXT
 >> Q.ABBREV_TAC `C'' = \n. C o (FUNPOW E n)`
 >> Know `!n. GCONTEXT (C'' n)`
 >- ( Q.UNABBREV_TAC `C''` >> BETA_TAC \\
      Induct_on `n` >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        ASM_REWRITE_TAC [o_DEF, FUNPOW, ETA_AX],
        (* goal 1.2 (of 2) *)
        REWRITE_TAC [FUNPOW_SUC_LEFT, o_ASSOC] \\
        MATCH_MP_TAC GCONTEXT_combin \\
        ASM_REWRITE_TAC [] ] )
 >> DISCH_TAC
 (* Part 2: property of C'' on P and Q *)
 >> `!n. (C P) expands (C'' n P)`
	by (Q.UNABBREV_TAC `C''` >> BETA_TAC >> PROVE_TAC [unfolding_lemma1'])
 >> `!n. (C Q) expands (C'' n Q)`
	by (Q.UNABBREV_TAC `C''` >> BETA_TAC >> PROVE_TAC [unfolding_lemma1'])
 (* Part 3 *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [Action_distinct_label] \\
      `(C P) expands (C'' (LENGTH xs) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP expands_AND_TRACE_label)) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH xs` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs'' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs'' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> ASM_REWRITE_TAC [] ) >> STRIP_TAC \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) expands ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      Know `WEAK_TRANS (C (FUNPOW E n Q)) (label l) (C' Q)`
      >- ( REWRITE_TAC [WEAK_TRANS_AND_TRACE, Action_distinct_label] \\
	   Q.EXISTS_TAC `xs''` >> ASM_REWRITE_TAC [] \\
	   MATCH_MP_TAC UNIQUE_LABEL_NOT_NULL \\
	   Q.EXISTS_TAC `label l` >> ASM_REWRITE_TAC [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC expands_WEAK_TRANS' \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC expands_IMP_WEAK_EQUIV >> ASM_REWRITE_TAC [], (* extra steps *)
      (* goal 2 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [] \\
      `(C P) expands (C'' (LENGTH xs) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP expands_AND_TRACE_tau)) \\ (* diff here *)
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH xs` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs'' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs'' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> ASM_REWRITE_TAC [] ) >> STRIP_TAC \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) expands ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      Know `EPS (C (FUNPOW E n Q)) (C' Q)` (* diff here *)
      >- ( REWRITE_TAC [EPS_AND_TRACE] \\
	   Q.EXISTS_TAC `xs''` >> ASM_REWRITE_TAC [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC expands_EPS' \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC expands_IMP_WEAK_EQUIV >> ASM_REWRITE_TAC [] ]); (* extra steps *)

val UNIQUE_SOLUTIONS_OF_EXPANSIONS = store_thm (
   "UNIQUE_SOLUTIONS_OF_EXPANSIONS",
  ``!E. WGS E ==>
	!P Q. P expands (E P) /\ Q expands (E Q) ==> WEAK_EQUIV P Q``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\R S. ?C. GCONTEXT C /\ WEAK_EQUIV R (C P) /\ WEAK_EQUIV S (C Q)`
 >> BETA_TAC >> CONJ_TAC
 >- ( Q.EXISTS_TAC `E` \\
      CONJ_TAC >- IMP_RES_TAC WGS_IS_GCONTEXT \\
      IMP_RES_TAC expands_IMP_WEAK_EQUIV \\
      ASM_REWRITE_TAC [] )
 >> REWRITE_TAC [WEAK_BISIM]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
	(ASSUME_TAC o (Q.SPECL [`l`, `E1`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E' (label l) E1 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTIONS_OF_EXPANSIONS_LEMMA) \\
      `!l R. WEAK_TRANS (C P) (label l) R ==>
           ?C'. GCONTEXT C' /\ R expands (C' P) /\
		(WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C Q) (C' Q)`
	by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ P expands (E P) /\ Q expands (E Q)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
	(ASSUME_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS (C P) (label l) R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `WEAK_TRANS (C Q) (label l) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
	(ASSUME_TAC o (Q.SPECL [`l`, `E2`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E'' (label l) E2 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTIONS_OF_EXPANSIONS_LEMMA) \\
      `!l R. WEAK_TRANS (C Q) (label l) R ==>
           ?C'. GCONTEXT C' /\ R expands (C' Q) /\
		(WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C P) (C' P)`
	by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ Q expands (E Q) /\ P expands (E P)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
	(ASSUME_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS (C Q) (label l) R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `WEAK_TRANS (C P) (label l) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 3 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
			    (ASSUME ``WEAK_EQUIV E' ((C :('a, 'b) context) P)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E''` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> ASM_REWRITE_TAC [] ) \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTIONS_OF_EXPANSIONS_LEMMA) \\
      `!R. WEAK_TRANS (C P) tau R ==>
           ?C'. GCONTEXT C' /\ R expands (C' P) /\
		(WEAK_EQUIV O EPS) (C Q) (C' Q)` by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ P expands (E P) /\ Q expands (E Q)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
	(ASSUME_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      Q.PAT_X_ASSUM `!R. WEAK_TRANS (C P) tau R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `EPS (C Q) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1'` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 4 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
			    (ASSUME ``WEAK_EQUIV E'' ((C :('a, 'b) context) Q)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> ASM_REWRITE_TAC [] ) \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTIONS_OF_EXPANSIONS_LEMMA) \\
      `!R. WEAK_TRANS (C Q) tau R ==>
           ?C'. GCONTEXT C' /\ R expands (C' Q) /\
		(WEAK_EQUIV O EPS) (C P) (C' P)` by METIS_TAC [] \\
      Q.PAT_X_ASSUM `(?E. WGS E /\ Q expands (E Q) /\ P expands (E P)) ==> X` K_TAC \\
      RES_TAC \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
	(ASSUME_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      Q.PAT_X_ASSUM `!R. WEAK_TRANS (C Q) tau R ==> X` K_TAC \\
      RES_TAC \\
      Q.PAT_X_ASSUM `EPS (C P) y ==> X` K_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `C'` >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> ASM_REWRITE_TAC [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS] ]);

(* Bibliography:
 *
 * [1] Milner, R.: Communication and concurrency. (1989).
 * [2] Sangiorgi, D.: Equations, contractions, and unique solutions. ACM SIGPLAN Notices. (2015).
 *)

val _ = export_theory ();
val _ = print_theory_to_file "-" "UniqueSolutionsTheory.lst";
val _ = html_theory "UniqueSolutions";

(* last updated: Aug 3, 2017 *)
