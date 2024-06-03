(* ========================================================================== *)
(* FILE          : UniqueSolutionsScript.sml                                  *)
(* DESCRIPTION   : Milner and Sangiorgi's "Unique Solutions of Equations"     *)
(*                                                                            *)
(* COPYRIGHTS    : 2016-2017 University of Bologna, Italy (Chun Tian)         *)
(*                 2018-2019 Fondazione Bruno Kessler, Italy (Chun Tian)      *)
(*                 2023-2024 The Australian National University (Chun Tian)   *)
(* ========================================================================== *)

open HolKernel Parse boolLib bossLib;

open combinTheory pred_setTheory relationTheory pairTheory sumTheory listTheory
     prim_recTheory arithmeticTheory;

open CCSLib CCSTheory TraceTheory StrongEQTheory WeakEQTheory ObsCongrTheory
     BisimulationUptoTheory CongruenceTheory ExpansionTheory ContractionTheory;

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
Theorem STRONG_UNIQUE_SOLUTION_LEMMA :
    !E. WG E ==>
        !P a P'. TRANS (E P) a P' ==>
                 ?E'. CONTEXT E' /\ (P' = E' P) /\ !Q. TRANS (E Q) a (E' Q)
Proof
    Induct_on `WG` >> BETA_TAC
 >> COUNT_TAC (rpt STRIP_TAC) (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      Q.EXISTS_TAC `\t. P'` >> rw [] \\
      rw [CONTEXT2],
      (* goal 2 (of 6) *)
      IMP_RES_TAC TRANS_PREFIX >> art [] \\
      Q.EXISTS_TAC `e` >> art [PREFIX],
      (* goal 3 (of 6) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> art [],
        (* goal 3.2 (of 2) *)
        RES_TAC \\
        Q.EXISTS_TAC `E''` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> art [] ],
      (* goal 4 (of 6) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 4.1 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E'' t) (E' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.1.1 (of 2) *)
          MATCH_MP_TAC CONTEXT5 >> art [] \\
          IMP_RES_TAC WG_IMP_CONTEXT,
          (* goal 4.1.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR1 >> art [] ],
        (* goal 4.2 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.2.1 (of 2) *)
          MATCH_MP_TAC CONTEXT5 >> art [] \\
          IMP_RES_TAC WG_IMP_CONTEXT,
          (* goal 4.2.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR2 >> art [] ],
        (* goal 4.3 (of 3) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. par (E''' t) (E'' t)` \\
        BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 4.3.1 (of 2) *)
          MATCH_MP_TAC CONTEXT5 >> art [],
          (* goal 4.3.2 (of 2) *)
          GEN_TAC >> MATCH_MP_TAC PAR3 \\
          Q.EXISTS_TAC `l` >> art [] ] ],
      (* goal 5 (of 6) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT6 >> art [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        FULL_SIMP_TAC std_ss [] \\
        PROVE_TAC [],
        (* goal 5.2 (of 2) *)
        RES_TAC >> FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT6 >> art [] ) \\
        GEN_TAC >> MATCH_MP_TAC RESTR \\
        Q.EXISTS_TAC `l` >> FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        PROVE_TAC [] ],
      (* goal 6 (of 6) *)
      IMP_RES_TAC TRANS_RELAB \\
      RES_TAC >> FULL_SIMP_TAC std_ss [] \\
      Q.EXISTS_TAC `\t. relab (E' t) rf` >> BETA_TAC >> REWRITE_TAC [] \\
      CONJ_TAC >- ( MATCH_MP_TAC CONTEXT7 >> art [] ) \\
      GEN_TAC >> MATCH_MP_TAC RELABELING >> art [] ]
QED

(* NOTE: This is a generalization of STRONG_UNIQUE_SOLUTION with the same proof. *)
Theorem STRONG_UNIQUE_SOLUTION_EXT :
    !C1 C2 P Q. WG C1 /\ WG C2 /\ (!t. STRONG_EQUIV (C1 t) (C2 t)) /\
                STRONG_EQUIV P (C1 P) /\ STRONG_EQUIV Q (C2 Q) ==> STRONG_EQUIV P Q
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC STRONG_EQUIV_BY_BISIM_UPTO
 >> qabbrev_tac ‘R = \x y. x = y \/ ?E. CONTEXT E /\ x = E P /\ y = E Q’
 >> Q.EXISTS_TAC ‘R’
 >> reverse CONJ_TAC
 >- (rw [Abbr ‘R’] \\
     DISJ2_TAC >> qexistsl_tac [‘\t. t’] >> rw [CONTEXT1])
 >> simp [STRONG_BISIM_UPTO]
 >> qx_genl_tac [`P'`, `Q'`]
 >> ‘R P' Q' <=> P' = Q' \/ ?E. CONTEXT E /\ P' = E P /\ Q' = E Q’ by rw [Abbr ‘R’]
 >> POP_ORW >> STRIP_TAC (* 2 subgoals *)
 >- (rw [O_DEF, Abbr ‘R’] >| (* 2 sub-goals here *)
     [ (* goal 1 (of 2) *)
       Q.EXISTS_TAC `E1` >> art [] \\
       Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `E2` >> art [] \\
       Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
       Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] ])
 (* preparing for induction *)
 >> NTAC 2 POP_ORW
 >> POP_ASSUM MP_TAC (* CONTEXT E *)
 >> Q.ID_SPEC_TAC ‘E’
 >> Induct_on `CONTEXT` >> rw []
 (* 14 subgoals left *)
 >- ((*
        P  ~  C1[P] ~ C2[P]  : C2[Q] ~  Q
        |     |        |          |     |
        u     u        u          u     u
        |     |        |          |     |
        E1 ~ ?E2   ~  ?G[P]  :  G[Q] ~ ?E3
      *)
    ‘?E2. C1 P --u-> E2 /\ STRONG_EQUIV E1 E2’ by METIS_TAC [PROPERTY_STAR_LEFT] \\
    ‘?E3. C2 P --u-> E3 /\ STRONG_EQUIV E2 E3’ by METIS_TAC [PROPERTY_STAR_LEFT] \\
     MP_TAC (Q.SPEC ‘C2’ STRONG_UNIQUE_SOLUTION_LEMMA) >> simp [] \\
     DISCH_THEN (MP_TAC o (Q.SPECL [‘P’, ‘u’, ‘E3’])) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘G’ STRIP_ASSUME_TAC) \\
     Q.PAT_X_ASSUM ‘E3 = G P’ (rfs o wrap) \\
    ‘?E3. Q --u-> E3 /\ STRONG_EQUIV E3 (G Q)’ by METIS_TAC [PROPERTY_STAR_RIGHT] \\
     Q.EXISTS_TAC ‘E3’ >> rw [Abbr ‘R’, O_DEF] \\
     Q.EXISTS_TAC ‘G Q’ >> reverse CONJ_TAC >- rw [STRONG_EQUIV_SYM] \\
     Q.EXISTS_TAC ‘G P’ \\
     CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_TRANS >> Q.EXISTS_TAC ‘E2’ >> art []) \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘G’ >> art [])
 (* 13 subgoals left *)
 >- ((*
        Q  ~ C2[Q] ~ C1[Q]  :  C1[P] ~  P
        |    |        |          |      |
        E2 ~ E1   ~  G[Q]   :  G[P]  ~  E3
      *)
    ‘?E1. C2 Q --u-> E1 /\ STRONG_EQUIV E2 E1’ by METIS_TAC [PROPERTY_STAR_LEFT] \\
    ‘?E3. C1 Q --u-> E3 /\ STRONG_EQUIV E3 E1’ by METIS_TAC [PROPERTY_STAR_RIGHT] \\
     MP_TAC (Q.SPEC ‘C1’ STRONG_UNIQUE_SOLUTION_LEMMA) >> simp [] \\
     DISCH_THEN (MP_TAC o (Q.SPECL [‘Q’, ‘u’, ‘E3’])) >> simp [] \\
     DISCH_THEN (Q.X_CHOOSE_THEN ‘G’ STRIP_ASSUME_TAC) \\
     Q.PAT_X_ASSUM ‘E3 = G Q’ (rfs o wrap) \\
    ‘?E3. P --u-> E3 /\ STRONG_EQUIV E3 (G P)’ by METIS_TAC [PROPERTY_STAR_RIGHT] \\
     Q.EXISTS_TAC ‘E3’ >> rw [Abbr ‘R’, O_DEF] \\
     Q.EXISTS_TAC ‘G Q’ \\
     reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_TRANS \\
                          Q.EXISTS_TAC ‘E1’ >> rw [STRONG_EQUIV_SYM]) \\
     Q.EXISTS_TAC ‘G P’ >> art [] \\
     DISJ2_TAC >> Q.EXISTS_TAC ‘G’ >> art [])
 (* 12 subgoals left *)
 >- (Q.EXISTS_TAC `E1` >> rw [Abbr ‘R’, O_DEF] \\
     Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `E1` >> art [STRONG_EQUIV_REFL])
 (* 11 subgoals left *)
 >- (Q.EXISTS_TAC `E2` >> rw [Abbr ‘R’, O_DEF] \\
     Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `E2` >> art [STRONG_EQUIV_REFL])
 (* 10 subgoals left *)
 >- (fs [TRANS_PREFIX_EQ] \\
     Q.PAT_X_ASSUM ‘!u. _’ K_TAC >> rw [Abbr ‘R’, O_DEF] \\
     Q.EXISTS_TAC `E Q` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `E P` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
     DISJ2_TAC >> Q.EXISTS_TAC `E` >> art [])
 (* 9 subgoals left *)
 >- (fs [TRANS_PREFIX_EQ] \\
     Q.PAT_X_ASSUM ‘!u. _’ K_TAC >> rw [Abbr ‘R’, O_DEF] \\
     Q.EXISTS_TAC `E Q` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
     Q.EXISTS_TAC `E P` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
     DISJ2_TAC >> Q.EXISTS_TAC `E` >> art [])
 (* 8 subgoals left *)
 >- (fs [TRANS_SUM_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       RES_TAC >> Q.EXISTS_TAC `E2` >> art [],
       (* goal 2 (of 2) *)
       RES_TAC >> Q.EXISTS_TAC `E2` >> art [] ])
 (* 8 subgoals left *)
 >- (fs [TRANS_SUM_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       RES_TAC >> Q.EXISTS_TAC `E1` >> art [],
       (* goal 2 (of 2) *)
       RES_TAC >> Q.EXISTS_TAC `E1` >> art [] ])
 (* 6 subgoals left *)
 >- (fs [TRANS_PAR_EQ] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       RES_TAC >> Q.EXISTS_TAC `E2 || E' Q` \\
       CONJ_TAC >- (DISJ1_TAC >> Q.EXISTS_TAC `E2` >> art []) \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals here *)
       [ (* goal 1.1 (of 2) *)
         rename1 `STRONG_EQUIV E1' y` \\
         Q.EXISTS_TAC `y || E' Q` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `y || E' P` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC \\
         Q.EXISTS_TAC `\t. y || E' t` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. (\z. y) t || E' t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `E'' Q || E' Q` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `E'' P || E' P` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E'' t || E' t` >> rw [] \\
         MATCH_MP_TAC CONTEXT5 >> art [] ],
       (* goal 2 (of 3) *)
       RES_TAC >> Q.EXISTS_TAC `E Q || E2` \\
       CONJ_TAC >- (NDISJ_TAC 1 >> Q.EXISTS_TAC `E2` >> art []) \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals here *)
       [ (* goal 2.1 (of 2) *)
         rename1 `STRONG_EQUIV E1' y` \\
         Q.EXISTS_TAC `E Q || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR \\
                              art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `E P || y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E t || y` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. E t || (\z. y) t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `E Q || E'' Q` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `E P || E'' P` \\
         CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E t || E'' t` >> rw [] \\
         MATCH_MP_TAC CONTEXT5 >> art [] ],
       (* goal 3 (of 3) *)
       RES_TAC >> Q.EXISTS_TAC `E2'' || E2'` \\
       CONJ_TAC >- (NDISJ_TAC 2 >> take [`E2''`, `E2'`, `l`] >> art []) \\
       Q.PAT_X_ASSUM `X E2 E2'` MP_TAC \\
       Q.PAT_X_ASSUM `X E1' E2''` MP_TAC \\
       rw [Abbr ‘R’, O_DEF] >| (* 4 subgoals here *)
       [ (* goal 3.1 (of 4) *)
         rename1 `STRONG_EQUIV E1' x` \\
         rename1 `STRONG_EQUIV E2 y` \\
         Q.EXISTS_TAC `x || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `x || y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ1_TAC >> REWRITE_TAC [],
         (* goal 3.2 (of 4) *)
         rename1 `STRONG_EQUIV E1' y` \\
         Q.EXISTS_TAC `y || E'' Q` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `y || E'' P` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. y || E'' t` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. (\z. y) t || E'' t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 3.3 (of 4) *)
         rename1 `STRONG_EQUIV E2 y` \\
         Q.EXISTS_TAC `E'' Q || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `E'' P || y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ2_TAC \\
         Q.EXISTS_TAC `\t. E'' t || y` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. E'' t || (\z. y) t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 3.4 (of 4) *)
         Q.EXISTS_TAC `E'' Q || E''' Q` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `E'' P || E''' P` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E'' t || E''' t` >> rw [] \\
         MATCH_MP_TAC CONTEXT5 >> art [] ] ])
 (* 5 subgoals left *)
 >- (fs [TRANS_PAR_EQ] >| (* 3 subgoals, again *)
     [ (* goal 1 (of 3) *)
       RES_TAC >> Q.EXISTS_TAC `E1' || E' P` \\
       CONJ_TAC >- (DISJ1_TAC >> Q.EXISTS_TAC `E1'` >> art []) \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         rename1 `STRONG_EQUIV E1' y` \\
         Q.EXISTS_TAC `y || E' Q` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `y || E' P` \\
         CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. y || E' t` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. (\z. y) t || E' t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 4.2 (of 2) *)
         Q.EXISTS_TAC `E'' Q || E' Q` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `E'' P || E' P` \\
         CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E'' t || E' t` >> rw [] \\
         MATCH_MP_TAC CONTEXT5 >> art [] ],
       (* goal 2 (of 3) *)
       RES_TAC >> Q.EXISTS_TAC `E P || E1'` \\
       CONJ_TAC >- (NDISJ_TAC 1 >> Q.EXISTS_TAC `E1'` >> art []) \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 sub-goals here *)
       [ (* goal 2.1 (of 2) *)
         rename1 `STRONG_EQUIV E1' y` \\
         Q.EXISTS_TAC `E Q || y` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `E P || y` \\
         CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E t || y` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. E t || (\z. y) t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `E Q || E'' Q` \\
         reverse CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         Q.EXISTS_TAC `E P || E'' P` \\
         CONJ_TAC
         >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art [STRONG_EQUIV_REFL]) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E t || E'' t` >> rw [] \\
         MATCH_MP_TAC CONTEXT5 >> art [] ],
       (* goal 3 (of 3) *)
       RES_TAC >> Q.EXISTS_TAC `E1'' || E1'` \\
       CONJ_TAC >- (NDISJ_TAC 2 >> take [`E1''`, `E1'`, `l`] >> art []) \\
       Q.PAT_X_ASSUM `_ E1'' E1` MP_TAC \\
       Q.PAT_X_ASSUM `_ E1' E2'` MP_TAC \\
       rw [Abbr ‘R’, O_DEF] >| (* 4 sub-goals here *)
       [ (* goal 3.1 (of 4) *)
         rename1 `STRONG_EQUIV E1' x` \\
         rename1 `STRONG_EQUIV y E1` \\
         Q.EXISTS_TAC `y || x` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `y || x` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ1_TAC >> rw [],
         (* goal 3.2 (of 4) *)
         rename1 `STRONG_EQUIV E1' y` \\
         Q.EXISTS_TAC `E'' Q || y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `E'' P || y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E'' t || y` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. E'' t || (\z. y) t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 3.3 (of 4) *)
         rename1 `STRONG_EQUIV y E1` \\
         Q.EXISTS_TAC `y || E'' Q` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `y || E'' P` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. y || E'' t` >> rw [] \\
        `CONTEXT (\z. y)` by REWRITE_TAC [CONTEXT2] \\
         Know `CONTEXT (\t. (\z. y) t || E'' t)`
         >- (MATCH_MP_TAC CONTEXT5 >> art []) >> rw [],
         (* goal 3.4 (of 4) *)
         Q.EXISTS_TAC `E''' Q || E'' Q` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         Q.EXISTS_TAC `E''' P || E'' P` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_PRESD_BY_PAR >> art []) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. E''' t || E'' t` >> rw [] \\
         MATCH_MP_TAC CONTEXT5 >> art [] ] ])
 (* 4 subgoals left *)
 >- (fs [TRANS_RESTR_EQ] >| (* 2 subgoals *)
    [ (* goal 1 (of 2) *)
      POP_ASSUM (fs o wrap) \\
      RES_TAC >> Q.EXISTS_TAC `restr L E2` \\
      CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
      POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals *)
      [ (* goal 1.1 (of 2) *)
        rename1 `STRONG_EQUIV y E2` \\
        Q.EXISTS_TAC `restr L y` \\
        reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        Q.EXISTS_TAC `restr L y` \\
        CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        DISJ1_TAC >> REWRITE_TAC [],
        (* goal 1.2 (of 2) *)
        Q.EXISTS_TAC `restr L (E' Q)` \\
        reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        Q.EXISTS_TAC `restr L (E' P)` \\
        CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        DISJ2_TAC >> Q.EXISTS_TAC `\t. restr L (E' t)` >> rw [] \\
        MATCH_MP_TAC CONTEXT6 >> art [] ],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM ‘u = label l’ (fs o wrap) \\
      RES_TAC >> Q.EXISTS_TAC `restr L E2` \\
      CONJ_TAC >- (Q.EXISTS_TAC `E2` >> art []) \\
      POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        rename1 `STRONG_EQUIV y E2` \\
        Q.EXISTS_TAC `restr L y` \\
        reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        Q.EXISTS_TAC `restr L y` \\
        CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        DISJ1_TAC >> REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        Q.EXISTS_TAC `restr L (E' Q)` \\
        reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        Q.EXISTS_TAC `restr L (E' P)` \\
        CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
        DISJ2_TAC \\
        Q.EXISTS_TAC `\t. restr L (E' t)` >> BETA_TAC >> REWRITE_TAC [] \\
        MATCH_MP_TAC CONTEXT6 >> art [] ] ])
 (* 3 subgoals left *)
 >- (fs [TRANS_RESTR_EQ] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       POP_ASSUM (fs o wrap) \\
       RES_TAC >> Q.EXISTS_TAC `restr L E1` \\
       CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals *)
       [ (* goal 1.1 (of 2) *)
         rename1 `STRONG_EQUIV E1 y` \\
         Q.EXISTS_TAC `restr L y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         Q.EXISTS_TAC `restr L y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         DISJ1_TAC >> REWRITE_TAC [],
         (* goal 1.2 (of 2) *)
         Q.EXISTS_TAC `restr L (E' Q)` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         Q.EXISTS_TAC `restr L (E' P)` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. restr L (E' t)` >> rw [] \\
         MATCH_MP_TAC CONTEXT6 >> art [] ],
       (* goal 2 (of 2) *)
       Q.PAT_X_ASSUM ‘u = label l’ (fs o wrap) \\
       RES_TAC >> Q.EXISTS_TAC `restr L E1` \\
       CONJ_TAC >- (Q.EXISTS_TAC `E1` >> art []) \\
       POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals *)
       [ (* goal 2.1 (of 2) *)
         rename1 `STRONG_EQUIV E1 y` \\
         Q.EXISTS_TAC `restr L y` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         Q.EXISTS_TAC `restr L y` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         DISJ1_TAC >> REWRITE_TAC [],
         (* goal 2.2 (of 2) *)
         Q.EXISTS_TAC `restr L (E' Q)` \\
         reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         Q.EXISTS_TAC `restr L (E' P)` \\
         CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RESTR >> art []) \\
         DISJ2_TAC >> Q.EXISTS_TAC `\t. restr L (E' t)` >> rw [] \\
         MATCH_MP_TAC CONTEXT6 >> art [] ] ])
 (* 2 subgoals left *)
 >- (fs [TRANS_RELAB_EQ] \\
     Q.PAT_X_ASSUM ‘u = relabel rf u'’ K_TAC \\
     RES_TAC >> Q.EXISTS_TAC `relab E2 rf` \\
     rename1 `TRANS (E Q) u E2` \\
     CONJ_TAC >- (take [`u`, `E2`] >> art []) \\
     POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 `STRONG_EQUIV y E2` \\
       Q.EXISTS_TAC `relab y rf` \\
       reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art [] ) \\
       Q.EXISTS_TAC `relab y rf` \\
       CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
       DISJ1_TAC >> REWRITE_TAC [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `relab (E' Q) rf` \\
       reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
       Q.EXISTS_TAC `relab (E' P) rf` \\
       CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
       DISJ2_TAC >> Q.EXISTS_TAC `\t. relab (E' t) rf` >> rw [] \\
       MATCH_MP_TAC CONTEXT7 >> art [] ])
 (* final goal *)
 >> (fs [TRANS_RELAB_EQ] \\
     Q.PAT_X_ASSUM ‘u = relabel rf u'’ K_TAC \\
     RES_TAC >> Q.EXISTS_TAC `relab E1 rf` \\
     rename1 `TRANS (E P) u E1` \\
     CONJ_TAC >- (take [`u`, `E1`] >> art []) \\
     POP_ASSUM MP_TAC >> rw [Abbr ‘R’, O_DEF] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       rename1 `STRONG_EQUIV E1 y` \\
       Q.EXISTS_TAC `relab y rf` \\
       reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
       Q.EXISTS_TAC `relab y rf` \\
       CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
       DISJ1_TAC >> REWRITE_TAC [],
       (* goal 2 (of 2) *)
       Q.EXISTS_TAC `relab (E' Q) rf` \\
       reverse CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
       Q.EXISTS_TAC `relab (E' P) rf` \\
       CONJ_TAC >- (MATCH_MP_TAC STRONG_EQUIV_SUBST_RELAB >> art []) \\
       DISJ2_TAC >> Q.EXISTS_TAC `\t. relab (E' t) rf` >> rw [] \\
       MATCH_MP_TAC CONTEXT7 >> art [] ])
QED

(* Proposition 4.14 in Milner's book [1] (uni-variate version):
   Let the expression E contains at most the variable X, and let X be
   weakly guarded in E, then:
        If P ~ E{P/X} and Q ~ E{Q/X} then P ~ Q.
 *)
Theorem STRONG_UNIQUE_SOLUTION :
    !E P Q. WG E /\ STRONG_EQUIV P (E P) /\ STRONG_EQUIV Q (E Q) ==> STRONG_EQUIV P Q
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC STRONG_UNIQUE_SOLUTION_EXT
 >> qexistsl_tac [‘E’, ‘E’] >> rw []
QED

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
val WEAK_UNIQUE_SOLUTION_LEMMA = store_thm (
   "WEAK_UNIQUE_SOLUTION_LEMMA",
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
      Q.EXISTS_TAC `G` >> art [] \\
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
        Q.EXISTS_TAC `G` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G'` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 5 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e2` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 6 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e1` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [] \\
        Q.EXISTS_TAC `G` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ],
      (* goal 7 (of 7) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e1` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 \\
        REWRITE_TAC [PREFIX],
        (* goal 4.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        FULL_SIMP_TAC std_ss [Action_distinct_label] \\
        Q.EXISTS_TAC `e2` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 \\
        REWRITE_TAC [PREFIX] ] ]);

(* The EPS version of WEAK_UNIQUE_SOLUTION_LEMMA.
   NOTE: the WEAK_TRANS version cannot be derived, because of the missing of SG in the middle.
 *)
val WEAK_UNIQUE_SOLUTION_LEMMA_EPS = store_thm (
   "WEAK_UNIQUE_SOLUTION_LEMMA_EPS",
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
 >- ( Q.EXISTS_TAC `G` >> art [] \\
      Q.UNABBREV_TAC `GP` >> art [EPS_REFL] )
 >> RES_TAC
 >> Q.UNABBREV_TAC `GP`
 >> Q.PAT_X_ASSUM `!P''. Abbrev (G P = G P'') ==> X` K_TAC
 >> FULL_SIMP_TAC std_ss []
 >> IMP_RES_TAC (Q.SPEC `H` WEAK_UNIQUE_SOLUTION_LEMMA) (* lemma used here *)
 >> FULL_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `H''`
 >> art [EQ_SYM]
 >> GEN_TAC
 >> `EPS (G Q) (H Q) /\ EPS (H Q) (H'' Q)` by PROVE_TAC [ONE_TAU]
 >> IMP_RES_TAC EPS_TRANS);

val GSEQ_EPS_lemma = Q.prove (
   `!E P Q R H. SG E /\ GSEQ E /\ WEAK_EQUIV P (E P) /\ WEAK_EQUIV Q (E Q) /\ GSEQ H /\
                (R = \x y. ?H. GSEQ H /\ (x = H P) /\ (y = H Q))
    ==> (!P'. EPS (H P) P' ==> ?Q'. EPS (H Q) Q' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q') /\
        (!Q'. EPS (H Q) Q' ==> ?P'. EPS (H P) P' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q')`,
 (* proof *)
    rpt GEN_TAC >> STRIP_TAC
 >> `WEAK_EQUIV (H P) ((H o E) P) /\ WEAK_EQUIV (H Q) ((H o E) Q)`
                                by PROVE_TAC [WEAK_EQUIV_SUBST_GSEQ, o_DEF]
 >> `SG (H o E) /\ GSEQ (H o E)` by PROVE_TAC [SG_GSEQ_combin]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] WEAK_EQUIV_EPS) \\
      MP_TAC (Q.SPEC `(H :'a context) o E` WEAK_UNIQUE_SOLUTION_LEMMA_EPS) \\
      RW_TAC bool_ss [] >> POP_ASSUM (MP_TAC o (Q.SPECL [`P`, `E2`])) \\
      RW_TAC bool_ss [] \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `Q`)) \\
      MP_TAC (Q.SPECL [`(H :'a context) Q`,
                       `((H :'a context) o (E :'a context)) Q`]
                      WEAK_EQUIV_EPS') >> RW_TAC bool_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `(H' :'a context) Q`)) \\
      RW_TAC bool_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
     `WEAK_EQUIV (H' Q) E1` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> art [] \\
      Q.EXISTS_TAC `H' P` >> art [] \\
      Q.EXISTS_TAC `H'` >> art [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] WEAK_EQUIV_EPS) \\
      MP_TAC (Q.SPEC `(H :'a context) o E` WEAK_UNIQUE_SOLUTION_LEMMA_EPS) \\
      RW_TAC bool_ss [] >> POP_ASSUM (MP_TAC o (Q.SPECL [`Q`, `E2`])) \\
      RW_TAC bool_ss [] \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `P`)) \\
      MP_TAC (Q.SPECL [`(H :'a context) P`,
                       `((H :'a context) o (E :'a context)) P`]
                      WEAK_EQUIV_EPS') >> RW_TAC bool_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `(H' :'a context) P`)) \\
      RW_TAC bool_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
     `WEAK_EQUIV (H' Q) Q'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> art [] \\
      Q.EXISTS_TAC `H' P` >> art [] \\
      Q.EXISTS_TAC `H'` >> art [] ]);

(* Proposition 7.13 in Milner's book [1]:
   Let the expression E contains at most the variable X, and let X be guarded and sequential
   in E, then:
        If P = E{P/X} and Q = E{Q/X} then P = Q. (here "=" means WEAK_EQUIV)
 *)
Theorem WEAK_UNIQUE_SOLUTION :
    !E P Q. SG E /\ GSEQ E /\ WEAK_EQUIV P (E P) /\ WEAK_EQUIV Q (E Q)
        ==> WEAK_EQUIV P Q
Proof
    rpt STRIP_TAC
 >> irule (REWRITE_RULE [RSUBSET] WEAK_BISIM_UPTO_ALT_THM)
 >> Q.EXISTS_TAC `\x y. ?H. GSEQ H /\ (x = H P) /\ (y = H Q)`
 >> BETA_TAC
 >> reverse CONJ_TAC
 >- (Q.EXISTS_TAC `\t. t` >> BETA_TAC >> REWRITE_TAC [GSEQ1])
 >> REWRITE_TAC [WEAK_BISIM_UPTO_ALT]
 >> fix [`P'`, `Q'`]
 >> BETA_TAC >> STRIP_TAC >> art []
 >> NTAC 2 (POP_ASSUM K_TAC)
 >> Q.ABBREV_TAC `R = \x y. ?H. GSEQ H /\ (x = H P) /\ (y = H Q)`
 >> `WEAK_EQUIV (H P) ((H o E) P) /\ WEAK_EQUIV (H Q) ((H o E) Q)`
                                 by PROVE_TAC [WEAK_EQUIV_SUBST_GSEQ, o_DEF]
 >> `SG (H o E) /\ GSEQ (H o E)` by PROVE_TAC [SG_GSEQ_combin]
 >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      `?E3. WEAK_TRANS ((H o E) P) (label l) E3 /\ WEAK_EQUIV E1 E3`
                                by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label] \\
      Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) P) (label l) E3`
        (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTION_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `TRANS (H' P) (label l) E2` by PROVE_TAC [] \\
      IMP_RES_TAC (Q.SPEC `H'` WEAK_UNIQUE_SOLUTION_LEMMA) \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `EPS (H'' P) E3` by PROVE_TAC [] \\
      MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] GSEQ_EPS_lemma) \\
      RW_TAC std_ss [] >> POP_ASSUM K_TAC \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      `WEAK_TRANS ((H o E) Q) (label l) Q'` by PROVE_TAC [WEAK_TRANS] \\
      `?Q3. WEAK_TRANS (H Q) (label l) Q3 /\ WEAK_EQUIV Q3 Q'`
                                by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      Q.EXISTS_TAC `Q3` >> art [] \\
      Q.PAT_X_ASSUM `X E3 Q'` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM `R y' y` MP_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
      `WEAK_EQUIV y Q3` by PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y` >> art [] \\
      `WEAK_EQUIV E1 y'` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y'` >> art [] \\
      Q.EXISTS_TAC `H'''` >> art [],
(*
 (case 4)                              (case 1)
   H P ======== eps =====> P3            H P ================= l ==============> E1
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H(E(P)) ==== eps =====> H' P         H(E(P)) ==eps=> E1'  --l-> E2    ==eps=> E3  ~~ y'
                           |                            (H' P)     (H'' P)              |
                           R                                                            R
                           |                                                            |
   H(E(Q)) ==== eps =====> E3 = H' Q    H(E(Q)) ==eps=> H' Q --l-> H'' Q ==eps=> Q'  ~~ y
   |                       |             |                                       |
   ~~                      ~~            ~~                                      ~~
   |                       |             |                                       |
   H Q ======== tau =====> E2           H Q ================== l ==============> Q3
 *)
      (* goal 2 (of 4) *)
      `?E3. WEAK_TRANS ((H o E) Q) (label l) E3 /\ WEAK_EQUIV E2 E3`
                                by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label] \\
      Q.PAT_X_ASSUM `WEAK_TRANS ((H o E) Q) (label l) E3`
        (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTION_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `TRANS (H' Q) (label l) E2'` by PROVE_TAC [] \\
      IMP_RES_TAC (Q.SPEC `H'` WEAK_UNIQUE_SOLUTION_LEMMA) \\
      NTAC 7 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `EPS (H'' Q) E3` by PROVE_TAC [] \\
      MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H''`] GSEQ_EPS_lemma) \\
      RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!P'. EPS (H'' P) P' ==> X` K_TAC \\
      RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
      `WEAK_TRANS ((H o E) P) (label l) P'` by PROVE_TAC [WEAK_TRANS] \\
      `?P3. WEAK_TRANS (H P) (label l) P3 /\ WEAK_EQUIV P3 P'`
                                by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_label'] \\
      Q.EXISTS_TAC `P3` >> art [] \\
      Q.PAT_X_ASSUM `X P' E3` MP_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
      Q.PAT_X_ASSUM `R y' y` MP_TAC \\
      Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
      `WEAK_EQUIV y E2` by PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `y` >> art [] \\
      `WEAK_EQUIV P3 y'` by PROVE_TAC [WEAK_EQUIV_TRANS] \\
      Q.EXISTS_TAC `y'` >> art [] \\
      Q.EXISTS_TAC `H'''` >> art [],
(*
 (case 3)                              (case 2)
   H P ======== tau =====> E1            H P ================== l ==============> P3
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H(E(P)) ==== eps =====> E3 = H' P    H(E(P)) ==eps=> H' P --l-> H'' P ==eps==> P' ~~ y'
                           |                                                            |
                           R                                                            R
                           |                           (H' Q)     (H'' Q)               |
   H(E(Q)) ==== eps =====> H' Q         H(E(Q)) ==eps=> E1'  --l-> E2'   ==eps==> E3 ~~ y
   |                       |             |                                        |
   ~~                      ~~            ~~                                       ~~
   |                       |             |                                        |
   H Q ======== eps =====> Q3            H Q ================== l ==============> E2
 *)
      (* goal 3 (of 4) *)
      `?E3. EPS ((H o E) P) E3 /\ WEAK_EQUIV E1 E3` by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_tau] \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTION_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `?Q3. EPS (H Q) Q3 /\ WEAK_EQUIV Q3 (H' Q)` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      Q.EXISTS_TAC `Q3` >> art [] \\
      Q.UNABBREV_TAC `R` >> REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV (H' Q) Q3` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> art [] \\
      Q.EXISTS_TAC `E3` >> art [] \\
      Q.EXISTS_TAC `H'` >> art [],
      (* goal 4 (of 4) *)
      `?E3. EPS ((H o E) Q) E3 /\ WEAK_EQUIV E2 E3` by PROVE_TAC [WEAK_EQUIV_WEAK_TRANS_tau] \\
      IMP_RES_TAC (Q.SPEC `H o E` WEAK_UNIQUE_SOLUTION_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
      `?P3. EPS (H P) P3 /\ WEAK_EQUIV P3 (H' P)` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
      Q.EXISTS_TAC `P3` >> art [] \\
      Q.UNABBREV_TAC `R` >> REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV E3 E2` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `E3` >> art [] \\
      Q.EXISTS_TAC `H' P` >> art [] \\
      Q.EXISTS_TAC `H'` >> art [] ]
QED

(******************************************************************************)
(*                                                                            *)
(*           3. Milner's unique solutions theorem for OBS_CONGR               *)
(*                                                                            *)
(******************************************************************************)

val OBS_UNIQUE_SOLUTION_LEMMA = store_thm (
   "OBS_UNIQUE_SOLUTION_LEMMA",
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
      Q.EXISTS_TAC `G` >> art [] \\
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
        RES_TAC >> Q.EXISTS_TAC `H` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> art [],
        (* goal 4.2 (of 2) *)
        RES_TAC >> Q.EXISTS_TAC `H` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> art [] ] ]);

(* The EPS version of OBS_UNIQUE_SOLUTION_LEMMA.
   NOTE: the WEAK_TRANS version cannot be derived, because of the missing of SG in the middle.
 *)
val OBS_UNIQUE_SOLUTION_LEMMA_EPS = store_thm (
   "OBS_UNIQUE_SOLUTION_LEMMA_EPS",
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
 >- ( Q.EXISTS_TAC `G` >> art [] \\
      Q.UNABBREV_TAC `GP` >> art [EPS_REFL] )
 >> RES_TAC
 >> Q.UNABBREV_TAC `GP`
 >> Q.PAT_X_ASSUM `!P''. Abbrev (G P = G P'') ==> X` K_TAC
 >> FULL_SIMP_TAC std_ss []
 >> IMP_RES_TAC (Q.SPEC `H` OBS_UNIQUE_SOLUTION_LEMMA) (* lemma used here *)
 >> FULL_SIMP_TAC std_ss []
 >> Q.EXISTS_TAC `H''`
 >> art [EQ_SYM]
 >> GEN_TAC
 >> `EPS (G Q) (H Q) /\ EPS (H Q) (H'' Q)` by PROVE_TAC [ONE_TAU]
 >> IMP_RES_TAC EPS_TRANS);

(* This lemma may apply at the final stage, it doesn't require (SG H), just (SEQ H) *)
val SEQ_EPS_lemma = Q.prove (
   `!E P Q R H. SG E /\ SEQ E /\ OBS_CONGR P (E P) /\ OBS_CONGR Q (E Q) /\ SEQ H /\
                (R = \x y. ?H. SEQ H /\ (WEAK_EQUIV x (H P)) /\ (WEAK_EQUIV y (H Q)))
    ==> (!P'. EPS (H P) P' ==> ?Q'. EPS (H Q) Q' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q') /\
        (!Q'. EPS (H Q) Q' ==> ?P'. EPS (H P) P' /\ (WEAK_EQUIV O R O WEAK_EQUIV) P' Q')`,
    rpt GEN_TAC >> STRIP_TAC
 >> `OBS_CONGR (H P) ((H o E) P) /\ OBS_CONGR (H Q) ((H o E) Q)`
                                by PROVE_TAC [OBS_CONGR_SUBST_SEQ, o_DEF]
 >> `SG (H o E) /\ SEQ (H o E)` by PROVE_TAC [SG_SEQ_combin]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `Q`)) \\
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS') \\
      NTAC 2 (POP_ASSUM K_TAC) \\
      Q.EXISTS_TAC `E1` >> art [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV (H' Q) E1` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      Q.EXISTS_TAC `H' Q` >> art [] \\
      Q.EXISTS_TAC `E2` >> art [] \\
      Q.EXISTS_TAC `H'` >> art [WEAK_EQUIV_REFL],
      (* goal 2 (of 2) *)
      IMP_RES_TAC (Q.SPECL [`H Q`, `(H o E) Q`] OBS_CONGR_EPS) \\
      IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      POP_ASSUM (ASSUME_TAC o BETA_RULE o (Q.SPEC `P`)) \\
      IMP_RES_TAC (Q.SPECL [`H P`, `(H o E) P`] OBS_CONGR_EPS') \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      `WEAK_EQUIV E2 Q'` by PROVE_TAC [WEAK_EQUIV_SYM] \\
      PROVE_TAC [WEAK_EQUIV_REFL] ]);

(* Proposition 7.13 in Milner's book [1]:
   Let the expression E contains at most the variable X, and let X be
   guarded and sequential in E, then:

     If P = E{P/X} and Q = E{Q/X} then P = Q. (here "=" means OBS_CONGR)

   This proof doesn't use "bisimulation up to" at all, instead it
   constructed a bisimulation directly and then verify it against
   OBS_CONGR_BY_WEAK_BISIM.
 *)
Theorem OBS_UNIQUE_SOLUTION :
    !E P Q. SG E /\ SEQ E /\ OBS_CONGR P (E P) /\ OBS_CONGR Q (E Q)
        ==> OBS_CONGR P Q
Proof
    rpt STRIP_TAC
 >> irule OBS_CONGR_BY_WEAK_BISIM
 >> Q.EXISTS_TAC `\x y. ?H. SEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)`
 >> reverse CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REWRITE_TAC [WEAK_BISIM] \\
      fix [`P'`, `Q'`] \\
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
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `TRANS (H' P) (label l) E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H'` OBS_UNIQUE_SOLUTION_LEMMA) \\
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
        Q.EXISTS_TAC `Q4` >> art [] \\
        Q.PAT_X_ASSUM `X E3 Q''` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
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
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `TRANS (H' Q) (label l) E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H'` OBS_UNIQUE_SOLUTION_LEMMA) \\
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
        Q.EXISTS_TAC `P4` >> art [] \\
        Q.PAT_X_ASSUM `X P'' E3` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >>
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
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `?Q3. EPS (H Q) Q3 /\ WEAK_EQUIV Q3 (H' Q)` by PROVE_TAC [OBS_CONGR_EPS'] \\
        `?Q4. EPS Q' Q4 /\ WEAK_EQUIV Q4 Q3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
        Q.EXISTS_TAC `Q4` >> art [] \\
        Q.UNABBREV_TAC `R` >> BETA_TAC \\
        PROVE_TAC [WEAK_EQUIV_TRANS],
        (* goal 4 (of 4) *)
        `?E1. EPS (H Q) E1 /\ WEAK_EQUIV E2 E1` by PROVE_TAC [WEAK_EQUIV_TRANS_tau] \\
        `?E3. EPS ((H o E) Q) E3 /\ WEAK_EQUIV E1 E3` by PROVE_TAC [OBS_CONGR_EPS] \\
        IMP_RES_TAC (Q.SPEC `H o E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `?P3. EPS (H P) P3 /\ WEAK_EQUIV P3 (H' P)` by PROVE_TAC [OBS_CONGR_EPS'] \\
        `?P4. EPS P' P4 /\ WEAK_EQUIV P4 P3` by PROVE_TAC [WEAK_EQUIV_EPS'] \\
        Q.EXISTS_TAC `P4` >> art [] \\
        Q.UNABBREV_TAC `R` >> BETA_TAC \\
        PROVE_TAC [WEAK_EQUIV_TRANS, WEAK_EQUIV_SYM] ],
      (* goal 2 (of 2) *)
      Q.ABBREV_TAC `R = \x y. ?H. SEQ H /\ WEAK_EQUIV x (H P) /\ WEAK_EQUIV y (H Q)` \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        `?E2. WEAK_TRANS (E P) u E2 /\ WEAK_EQUIV E1 E2`
                                by PROVE_TAC [OBS_CONGR_TRANS_LEFT] \\
        Q.PAT_X_ASSUM `WEAK_TRANS (E P) u E2`
          (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
        IMP_RES_TAC (Q.SPEC `E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `TRANS (H P) u E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H` OBS_UNIQUE_SOLUTION_LEMMA) \\
        NTAC 5 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
        `EPS (H' P) E2` by PROVE_TAC [] \\
        MP_TAC (Q.SPECL [`E`, `P`, `Q`, `R`, `H'`] SEQ_EPS_lemma) \\
        RW_TAC std_ss [] >> POP_ASSUM K_TAC \\
        RES_TAC >> NTAC 2 (POP_ASSUM K_TAC) \\
        `WEAK_TRANS (E Q) u Q'` by PROVE_TAC [WEAK_TRANS] \\
        `?Q''. WEAK_TRANS Q u Q'' /\ WEAK_EQUIV Q'' Q'`
                                by PROVE_TAC [OBS_CONGR_WEAK_TRANS'] \\
        Q.EXISTS_TAC `Q''` >> art [] \\
        Q.PAT_X_ASSUM `X E2 Q'` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
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
                                by PROVE_TAC [OBS_CONGR_TRANS_LEFT] \\
        Q.PAT_X_ASSUM `WEAK_TRANS (E Q) u E1`
          (STRIP_ASSUME_TAC o (REWRITE_RULE [WEAK_TRANS])) \\
        IMP_RES_TAC (Q.SPEC `E` OBS_UNIQUE_SOLUTION_LEMMA_EPS) \\
        NTAC 4 (POP_ASSUM K_TAC) \\
        POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
        `TRANS (H Q) u E2'` by PROVE_TAC [] \\
        IMP_RES_TAC (Q.SPEC `H` OBS_UNIQUE_SOLUTION_LEMMA) \\
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
        Q.EXISTS_TAC `P''` >> art [] \\
        Q.PAT_X_ASSUM `X P' E1` MP_TAC \\
        REWRITE_TAC [O_DEF] >> BETA_TAC >> rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `R y' y` MP_TAC \\
        Q.UNABBREV_TAC `R` >> BETA_TAC >> rpt STRIP_TAC \\
        PROVE_TAC [WEAK_EQUIV_SYM, WEAK_EQUIV_TRANS] ] ]
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
QED

(******************************************************************************)
(*                                                                            *)
(*            4. Unique solutions of contractions                             *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: the lemma works for any precongruence relation *)
val unfolding_lemma1 = store_thm (
   "unfolding_lemma1",
  ``!E C P. GCONTEXT E /\ GCONTEXT C /\ P contracts (E P) ==>
        !n. (C P) contracts (C o (FUNPOW E n)) P``,
    rpt STRIP_TAC
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> irule contracts_SUBST_GCONTEXT >> art []
 >> Q.SPEC_TAC (`n`, `n`)
 >> Induct >- REWRITE_TAC [FUNPOW, contracts_REFL]
 >> REWRITE_TAC [FUNPOW_SUC]
 >> Q.ABBREV_TAC `Q = FUNPOW E n P`
 >> PROVE_TAC [contracts_SUBST_GCONTEXT, contracts_TRANS]);

(* These can be merged to HOL's arithmeticTheory (not used here any more).
   The word "LEFT" or "RIGHT" indicate the position of `FUNPOW` w.r.t `o`.
 *)
Theorem FUNPOW_SUC_RIGHT :
    !f n. FUNPOW f (SUC n) = f o (FUNPOW f n)
Proof
    RW_TAC std_ss [o_DEF, FUNPOW_SUC, FUN_EQ_THM]
QED

Theorem FUNPOW_SUC_LEFT :
    !f n. FUNPOW f (SUC n) = (FUNPOW f n) o f
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [FUN_EQ_THM, o_DEF] >> BETA_TAC
 >> GEN_TAC
 >> `FUNPOW f (n + 1) x = FUNPOW f n (FUNPOW f 1 x)` by PROVE_TAC [FUNPOW_ADD]
 >> FULL_SIMP_TAC arith_ss [FUNPOW_1, ADD1]
QED

(* A single transition from WGS E[P] will not touch the variable P *)
val unfolding_lemma2 = store_thm (
   "unfolding_lemma2",
  ``!E. WGS E ==> !P u P'. TRANS (E P) u P' ==>
        ?C'. GCONTEXT C' /\ (P' = C' P) /\ !Q. TRANS (E Q) u (C' Q)``,
    HO_MATCH_MP_TAC WGS_strongind
 >> BETA_TAC >> REWRITE_TAC [ETA_AX]
 >> rpt STRIP_TAC (* 6 sub-goals here *)
 >| [ (* goal 1 (of 6) *)
      Q.EXISTS_TAC `\t. P'` >> art [GCONTEXT2],
      (* goal 2 (of 6) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `e` >> art [] \\
      GEN_TAC >> REWRITE_TAC [PREFIX],
      (* goal 3 (of 6) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 3.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        Q.EXISTS_TAC `e1` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> REWRITE_TAC [PREFIX],
        (* goal 3.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        Q.EXISTS_TAC `e2` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> REWRITE_TAC [PREFIX] ],
      (* goal 4 (of 6) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 4.1 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (C' t) (E' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT5 >> art [] \\
                      MATCH_MP_TAC WGS_IMP_GCONTEXT >> art [] ) \\
        FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR1 >> art [],
        (* goal 4.2 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (E t) (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT5 >> art [] \\
                      MATCH_MP_TAC WGS_IMP_GCONTEXT >> art [] ) \\
        FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR2 >> art [],
        (* goal 4.3 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (C'' t) (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT5 >> art [] ) \\
        FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ],
      (* goal 5 (of 6) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 5.1 (of 2) *)
        FULL_SIMP_TAC std_ss [] >> RES_TAC \\
        Q.EXISTS_TAC `\t. restr L (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT6 >> art [] ) \\
        art [] \\
        GEN_TAC >> MATCH_MP_TAC RESTR >> art [],
        (* goal 5.2 (of 2) *)
        FULL_SIMP_TAC std_ss [] >> RES_TAC \\
        Q.EXISTS_TAC `\t. restr L (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT6 >> art [] ) \\
        art [] \\
        GEN_TAC >> MATCH_MP_TAC RESTR >> art [] \\
        Q.EXISTS_TAC `l` >> art [] ],
      (* goal 6 (of 6) *)
      IMP_RES_TAC TRANS_RELAB >> RES_TAC \\
      Q.EXISTS_TAC `\t. relab (C' t) rf` >> BETA_TAC \\
      CONJ_TAC >- ( MATCH_MP_TAC GCONTEXT7 >> art [] ) \\
      art [] \\
      GEN_TAC >> MATCH_MP_TAC RELABELING >> art [] ]);

(* In this proof, we combine C and E into a single WGS and call previous lemma *)
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
 >> art [] >> DISCH_TAC
 >> IMP_RES_TAC unfolding_lemma2
 >> POP_ASSUM K_TAC
 >> Q.EXISTS_TAC `C'` >> art []
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
 >- (RW_TAC std_ss [o_DEF, FUNPOW_0] \\
     Q.EXISTS_TAC `C` >> fs [TRACE_NIL])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `TRACE X xs P'` MP_TAC
 >> Know `!P. (C o (FUNPOW E (SUC n))) P = (C o (FUNPOW E n)) (E P)`
 >- RW_TAC std_ss [o_DEF, FUNPOW] >> Rewr
 >> DISCH_TAC
 >> IMP_RES_TAC TRACE_cases2
 >> Cases_on `xs`
 >- (REV_FULL_SIMP_TAC std_ss [NULL] \\
    `LENGTH (epsilon :'a Action list) <= n` by FULL_SIMP_TAC arith_ss [LENGTH] \\
     Q.PAT_X_ASSUM `!xs P' P. X ==> X'`
       (MP_TAC o (Q.SPECL [`[] :'a Action list`, `P'`, `(E :'a context) P`])) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC `C' o E` >> art [] \\
     CONJ_TAC >- (IMP_RES_TAC WGS_IMP_GCONTEXT \\
                  MATCH_MP_TAC GCONTEXT_combin >> art []) \\
     CONJ_TAC >- (KILL_TAC >> REWRITE_TAC [o_DEF] >> RW_TAC std_ss []) \\
     GEN_TAC >> ASM_SIMP_TAC std_ss [o_DEF])
 >> FULL_SIMP_TAC list_ss []
 >> `LENGTH (FRONT (h::t)) <= n` by PROVE_TAC [LENGTH_FRONT_CONS]
 >> Q.ABBREV_TAC `xs = FRONT (h::t)`
 >> Q.ABBREV_TAC `x = LAST (h::t)`
 >> Q.PAT_X_ASSUM `!xs P'' P'''. X ==> X'`
      (MP_TAC o (Q.SPECL [`xs`, `u`, `(E :'a context) P`]))
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`C'`, `E`] unfolding_lemma3)
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`P`, `x`, `P'`]))
 >> RW_TAC bool_ss []
 >> Q.EXISTS_TAC `C''` >> art []
 >> GEN_TAC
 >> ONCE_REWRITE_TAC [TRACE_cases2]
 >> REWRITE_TAC [NULL]
 >> Q.EXISTS_TAC `C' (E Q)`
 >> Q.UNABBREV_TAC `x` >> art []
 >> Q.UNABBREV_TAC `xs` >> art []);

(* Lemma 3.9 of [2] *)
val UNIQUE_SOLUTION_OF_CONTRACTIONS_LEMMA = store_thm (
   "UNIQUE_SOLUTION_OF_CONTRACTIONS_LEMMA",
  ``!(P :'a CCS) (Q :'a CCS).
        (?E. WGS E /\ P contracts (E P) /\ Q contracts (E Q)) ==>
        !(C :'a context). GCONTEXT C ==>
            (!l R. WEAK_TRANS (C P) (label l) R ==>
                ?C'. GCONTEXT C' /\ R contracts (C' P) /\
                     (WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C Q) (C' Q)) /\
            (!R. WEAK_TRANS (C P) tau R ==>
                ?C'. GCONTEXT C' /\ R contracts (C' P) /\
                     (WEAK_EQUIV O EPS) (C Q) (C' Q))``,
    NTAC 5 STRIP_TAC
 (* Part 1: construct C'' which is a GCONTEXT *)
 >> IMP_RES_TAC WGS_IMP_GCONTEXT
 >> Q.ABBREV_TAC `C'' = \n. C o (FUNPOW E n)`
 >> Know `!n. GCONTEXT (C'' n)`
 >- (Q.UNABBREV_TAC `C''` >> BETA_TAC \\
     Induct_on `n` >- art [o_DEF, FUNPOW, ETA_THM] \\
     REWRITE_TAC [FUNPOW_SUC_LEFT, o_ASSOC] \\
     MATCH_MP_TAC GCONTEXT_combin >> art []) >> DISCH_TAC
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
      `(C P) contracts (C'' (LENGTH us) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP contracts_AND_TRACE_label)) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> art [] ) \\
      STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) contracts ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `WEAK_TRANS (C (FUNPOW E n Q)) (label l) (C' Q)`
      >- ( REWRITE_TAC [WEAK_TRANS_AND_TRACE, Action_distinct_label] \\
           Q.EXISTS_TAC `xs'` >> art [] \\
           MATCH_MP_TAC UNIQUE_LABEL_NOT_NULL \\
           Q.EXISTS_TAC `label l` >> art [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC contracts_WEAK_TRANS_label' \\
      Q.EXISTS_TAC `E1` >> art [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [] \\
      `(C P) contracts (C'' (LENGTH us) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP contracts_AND_TRACE_tau)) \\ (* diff here *)
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> art [] ) \\
      STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) contracts ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `EPS (C (FUNPOW E n Q)) (C' Q)` (* diff here *)
      >- ( REWRITE_TAC [EPS_AND_TRACE] \\
           Q.EXISTS_TAC `xs'` >> art [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC contracts_EPS' \\
      Q.EXISTS_TAC `E1` >> art [] ]);

(* Theorem 3.10 of [2], the proof relies on above lemma, and "contracts_IMP_WEAK_EQUIV",
   the definition of contraction is not used.
 *)
Theorem UNIQUE_SOLUTION_OF_CONTRACTIONS :
    !E P Q. WGS E /\ P contracts (E P) /\ Q contracts (E Q) ==> WEAK_EQUIV P Q
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\R S. ?C. GCONTEXT C /\ WEAK_EQUIV R (C P) /\ WEAK_EQUIV S (C Q)`
 >> BETA_TAC >> CONJ_TAC
 >- (Q.EXISTS_TAC `E` \\
     CONJ_TAC >- IMP_RES_TAC WGS_IMP_GCONTEXT \\
     IMP_RES_TAC contracts_IMP_WEAK_EQUIV >> art [])
 >> REWRITE_TAC [WEAK_BISIM]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
        (ASSUME_TAC o (Q.SPECL [`l`, `E1`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E' (label l) E1 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTION_OF_CONTRACTIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
        (ASSUME_TAC o (Q.SPECL [`l`, `E2`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E'' (label l) E2 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTION_OF_CONTRACTIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 3 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
                            (ASSUME ``WEAK_EQUIV E' ((C :'a context) P)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E''` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> art [] ) \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTION_OF_CONTRACTIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 4 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
                            (ASSUME ``WEAK_EQUIV E'' ((C :'a context) Q)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> art [] ) \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTION_OF_CONTRACTIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [contracts_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS] ]
QED

(******************************************************************************)
(*                                                                            *)
(*            5. Unique solutions of expansions                               *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: the lemma works for any precongruence relation *)
val unfolding_lemma1' = store_thm (
   "unfolding_lemma1'",
  ``!E C P. GCONTEXT E /\ GCONTEXT C /\ P expands (E P) ==>
        !n. (C P) expands (C o (FUNPOW E n)) P``,
    rpt STRIP_TAC
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> irule expands_SUBST_GCONTEXT >> art []
 >> Q.SPEC_TAC (`n`, `n`)
 >> Induct >- REWRITE_TAC [FUNPOW, expands_REFL]
 >> REWRITE_TAC [FUNPOW_SUC]
 >> Q.ABBREV_TAC `Q = FUNPOW E n P`
 >> `(E P) expands (E Q)` by PROVE_TAC [expands_SUBST_GCONTEXT]
 >> IMP_RES_TAC expands_TRANS);

(* The proof has only minor differences with UNIQUE_SOLUTION_OF_CONTRACTIONS_LEMMA *)
val UNIQUE_SOLUTION_OF_EXPANSIONS_LEMMA = store_thm (
   "UNIQUE_SOLUTION_OF_EXPANSIONS_LEMMA",
  ``!(P :'a CCS) (Q :'a CCS).
        (?E. WGS E /\ P expands (E P) /\ Q expands (E Q)) ==>
        !(C :'a context). GCONTEXT C ==>
            (!l R. WEAK_TRANS (C P) (label l) R ==>
                ?C'. GCONTEXT C' /\ R expands (C' P) /\
                     (WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C Q) (C' Q)) /\
            (!R. WEAK_TRANS (C P) tau R ==>
                ?C'. GCONTEXT C' /\ R expands (C' P) /\
                     (WEAK_EQUIV O EPS) (C Q) (C' Q))``,
    NTAC 5 STRIP_TAC
 (* Part 1: construct C'' which is a GCONTEXT *)
 >> IMP_RES_TAC WGS_IMP_GCONTEXT
 >> Q.ABBREV_TAC `C'' = \n. C o (FUNPOW E n)`
 >> Know `!n. GCONTEXT (C'' n)`
 >- (Q.UNABBREV_TAC `C''` >> BETA_TAC \\
     Induct_on `n` >- art [o_DEF, FUNPOW, ETA_THM] \\
     REWRITE_TAC [FUNPOW_SUC_LEFT, o_ASSOC] \\
     MATCH_MP_TAC GCONTEXT_combin >> art []) >> DISCH_TAC
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
      `(C P) expands (C'' (LENGTH us) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP expands_AND_TRACE_label)) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> art [] ) \\
      STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) expands ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `WEAK_TRANS (C (FUNPOW E n Q)) (label l) (C' Q)`
      >- ( REWRITE_TAC [WEAK_TRANS_AND_TRACE, Action_distinct_label] \\
           Q.EXISTS_TAC `xs'` >> art [] \\
           MATCH_MP_TAC UNIQUE_LABEL_NOT_NULL \\
           Q.EXISTS_TAC `label l` >> art [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC expands_WEAK_TRANS' \\
      Q.EXISTS_TAC `E1` >> art [] \\
      MATCH_MP_TAC expands_IMP_WEAK_EQUIV >> art [], (* extra steps *)
      (* goal 2 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [] \\
      `(C P) expands (C'' (LENGTH us) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP expands_AND_TRACE_tau)) \\ (* diff here *)
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. GCONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs' (C' Q)`
      >- ( MATCH_MP_TAC unfolding_lemma4 >> art [] ) \\
      STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `(C Q) expands ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `EPS (C (FUNPOW E n Q)) (C' Q)` (* diff here *)
      >- ( REWRITE_TAC [EPS_AND_TRACE] \\
           Q.EXISTS_TAC `xs'` >> art [] ) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC expands_EPS' \\
      Q.EXISTS_TAC `E1` >> art [] \\
      MATCH_MP_TAC expands_IMP_WEAK_EQUIV >> art [] ]); (* extra steps *)

(* The proof is essentially the same with UNIQUE_SOLUTION_OF_CONTRACTIONS *)
Theorem UNIQUE_SOLUTION_OF_EXPANSIONS :
    !E P Q. WGS E /\ P expands (E P) /\ Q expands (E Q) ==> WEAK_EQUIV P Q
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\R S. ?C. GCONTEXT C /\ WEAK_EQUIV R (C P) /\ WEAK_EQUIV S (C Q)`
 >> BETA_TAC >> CONJ_TAC
 >- (Q.EXISTS_TAC `E` \\
     CONJ_TAC >- IMP_RES_TAC WGS_IMP_GCONTEXT \\
     IMP_RES_TAC expands_IMP_WEAK_EQUIV >> art [])
 >> REWRITE_TAC [WEAK_BISIM]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
        (ASSUME_TAC o (Q.SPECL [`l`, `E1`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E' (label l) E1 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTION_OF_EXPANSIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
        (ASSUME_TAC o (Q.SPECL [`l`, `E2`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RES_TAC \\
      Q.PAT_X_ASSUM `TRANS E'' (label l) E2 ==> X` K_TAC \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTION_OF_EXPANSIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 3 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
                            (ASSUME ``WEAK_EQUIV E' ((C :'a context) P)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E''` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> art [] ) \\
      ASSUME_TAC (Q.SPECL [`P`, `Q`] UNIQUE_SOLUTION_OF_EXPANSIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1' (C' Q)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2 (C' P)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 4 (of 4) *)
      IMP_RES_TAC (MATCH_MP WEAK_EQUIV_TRANS_tau
                            (ASSUME ``WEAK_EQUIV E'' ((C :'a context) Q)``)) \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- ( Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
           Q.EXISTS_TAC `C` >> art [] ) \\
      ASSUME_TAC (Q.SPECL [`Q`, `P`] UNIQUE_SOLUTION_OF_EXPANSIONS_LEMMA) \\
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
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      `WEAK_EQUIV E1 (C' P)` by PROVE_TAC [WEAK_EQUIV_TRANS] >> art [] \\
      `WEAK_EQUIV E2' (C' Q)` by PROVE_TAC [expands_IMP_WEAK_EQUIV] \\
      PROVE_TAC [WEAK_EQUIV_TRANS] ]
QED

(* Another way to prove above theorem using UNIQUE_SOLUTION_OF_CONTRACTIONS, this method
   works for any relation coarser than `contracts`, partial-ordering and precogruence of
  `expands` are not needed. *)
val UNIQUE_SOLUTION_OF_EXPANSIONS' = store_thm (
   "UNIQUE_SOLUTION_OF_EXPANSIONS'",
  ``!E. WGS E ==>
        !P Q. P expands (E P) /\ Q expands (E Q) ==> WEAK_EQUIV P Q``,
    rpt STRIP_TAC
 >> IMP_RES_TAC expands_IMP_contracts
 >> irule UNIQUE_SOLUTION_OF_CONTRACTIONS
 >> Q.EXISTS_TAC `E` >> art []);

(******************************************************************************)
(*                                                                            *)
(*             6. Unique solutions of observational contractions              *)
(*                                                                            *)
(******************************************************************************)

(* NOTE: the lemma works for any precongruence relation *)
Theorem OBS_unfolding_lemma1 :
    !E C P. CONTEXT E /\ CONTEXT C /\ OBS_contracts P (E P) ==>
        !n. OBS_contracts (C P) ((C o (FUNPOW E n)) P)
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [o_DEF]
 >> BETA_TAC
 >> irule OBS_contracts_SUBST_CONTEXT >> art []
 >> Q.SPEC_TAC (`n`, `n`)
 >> Induct >- REWRITE_TAC [FUNPOW, OBS_contracts_REFL]
 >> REWRITE_TAC [FUNPOW_SUC]
 >> Q.ABBREV_TAC `Q = FUNPOW E n P`
 >> `OBS_contracts (E P) (E Q)` by PROVE_TAC [OBS_contracts_SUBST_CONTEXT]
 >> IMP_RES_TAC OBS_contracts_TRANS
QED

(* A single transition from WG E[P] will not touch the variable P *)
Theorem OBS_unfolding_lemma2 :
    !E. WG E ==>
       !P u P'. TRANS (E P) u P' ==>
               ?C'. CONTEXT C' /\ (P' = C' P) /\ !Q. TRANS (E Q) u (C' Q)
Proof
    HO_MATCH_MP_TAC WG_strongind
 >> BETA_TAC >> REWRITE_TAC [ETA_AX]
 >> reverse (rpt STRIP_TAC
             >- (Q.EXISTS_TAC `\t. P'` >> art [CONTEXT2])
             >- (IMP_RES_TAC TRANS_PREFIX \\
                 Q.EXISTS_TAC `e` >> art [] \\
                 GEN_TAC >> REWRITE_TAC [PREFIX])) (* 4 goals left *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_RELAB >> RES_TAC \\
      Q.EXISTS_TAC `\t. relab (C' t) rf` >> BETA_TAC \\
      CONJ_TAC >- ( MATCH_MP_TAC CONTEXT7 >> art [] ) \\
      art [] \\
      GEN_TAC >> MATCH_MP_TAC RELABELING >> art [],
      (* goal 2 (of 4) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        FULL_SIMP_TAC std_ss [] >> RES_TAC \\
        Q.EXISTS_TAC `\t. restr L (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT6 >> art [] ) \\
        art [] \\
        GEN_TAC >> MATCH_MP_TAC RESTR >> art [],
        (* goal 2.2 (of 2) *)
        FULL_SIMP_TAC std_ss [] >> RES_TAC \\
        Q.EXISTS_TAC `\t. restr L (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT6 >> art [] ) \\
        art [] \\
        GEN_TAC >> MATCH_MP_TAC RESTR >> art [] \\
        Q.EXISTS_TAC `l` >> art [] ],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 3.1 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (C' t) (E' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT5 >> art [] \\
                      MATCH_MP_TAC WG_IMP_CONTEXT >> art [] ) \\
        FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR1 >> art [],
        (* goal 3.2 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (E t) (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT5 >> art [] \\
                      MATCH_MP_TAC WG_IMP_CONTEXT >> art [] ) \\
        FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR2 >> art [],
        (* goal 3.3 (of 3) *)
        RES_TAC \\
        Q.EXISTS_TAC `\t. par (C'' t) (C' t)` >> BETA_TAC \\
        CONJ_TAC >- ( MATCH_MP_TAC CONTEXT5 >> art [] ) \\
        FULL_SIMP_TAC std_ss [] \\
        GEN_TAC >> MATCH_MP_TAC PAR3 \\
        Q.EXISTS_TAC `l` >> art [] ],
      (* goal 4 (of 4) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        Q.PAT_X_ASSUM `!P u P'. TRANS (E P) u P' ==> X` MP_TAC \\
        Q.PAT_X_ASSUM `TRANS (sum (E P) (E' P)) u P'` MP_TAC \\
        POP_ASSUM MP_TAC \\
        Q.PAT_X_ASSUM `WG E` MP_TAC \\
        Q.SPEC_TAC (`E`, `E`) \\
        HO_MATCH_MP_TAC WG_strongind \\
        BETA_TAC >> REWRITE_TAC [ETA_AX] >> rpt STRIP_TAC (* 6 sub-goals here *)
        >- ( RES_TAC >> POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `P`)) \\
             Q.EXISTS_TAC `C'` >> art [] \\
             GEN_TAC >> MATCH_MP_TAC SUM1 >> art [] ) \\
        RES_TAC >> Q.EXISTS_TAC `C'` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM1 >> art [],
        (* goal 4.2 (of 2) *)
        Q.PAT_X_ASSUM `!P u P'. TRANS (E' P) u P' ==> X` MP_TAC \\
        Q.PAT_X_ASSUM `TRANS (sum (E P) (E' P)) u P'` MP_TAC \\
        POP_ASSUM MP_TAC \\
        Q.PAT_X_ASSUM `WG E'` MP_TAC \\
        Q.SPEC_TAC (`E'`, `E'`) \\
        HO_MATCH_MP_TAC WG_strongind \\
        BETA_TAC >> REWRITE_TAC [ETA_AX] >> rpt STRIP_TAC (* 6 sub-goals here *)
        >- ( RES_TAC >> POP_ASSUM (STRIP_ASSUME_TAC o (Q.SPEC `P`)) \\
             Q.EXISTS_TAC `C'` >> art [] \\
             GEN_TAC >> MATCH_MP_TAC SUM2 >> art [] ) \\
        RES_TAC >> Q.EXISTS_TAC `C'` >> art [] \\
        GEN_TAC >> MATCH_MP_TAC SUM2 >> art [] ] ]
QED

(* In this proof, we combine C and E into a single WG and call previous lemma *)
Theorem OBS_unfolding_lemma3 :
    !C E. CONTEXT C /\ WG E ==>
          !P x P'. TRANS (C (E P)) x P' ==>
                   ?C'. CONTEXT C' /\ (P' = C' P) /\ !Q. TRANS (C (E Q)) x (C' Q)
Proof
    rpt STRIP_TAC
 >> IMP_RES_TAC CONTEXT_WG_combin
 >> Know `C (E P) = (C o E) P` >- SIMP_TAC std_ss [o_DEF]
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM `TRANS (C (E P)) x P'` MP_TAC
 >> art [] >> DISCH_TAC
 >> IMP_RES_TAC OBS_unfolding_lemma2
 >> POP_ASSUM K_TAC
 >> Q.EXISTS_TAC `C'` >> art []
 >> GEN_TAC >> POP_ASSUM MP_TAC
 >> KILL_TAC
 >> REWRITE_TAC [o_DEF] >> BETA_TAC
 >> RW_TAC std_ss []
QED

Theorem OBS_unfolding_lemma4 :
    !C E n xs P' P. CONTEXT C /\ WG E /\
        TRACE ((C o FUNPOW E n) P) xs P' /\ (LENGTH xs <= n) ==>
        ?C'. CONTEXT C' /\ (P' = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs (C' Q)
Proof
    NTAC 2 GEN_TAC
 >> Induct_on `n`
 >- (RW_TAC std_ss [o_DEF, FUNPOW_0] \\
     Q.EXISTS_TAC `C` >> fs [TRACE_NIL])
 >> rpt STRIP_TAC
 >> Q.PAT_X_ASSUM `TRACE X xs P'` MP_TAC
 >> Know `!P. (C o (FUNPOW E (SUC n))) P = (C o (FUNPOW E n)) (E P)`
 >- RW_TAC std_ss [o_DEF, FUNPOW] >> Rewr
 >> DISCH_TAC
 >> IMP_RES_TAC TRACE_cases2
 >> Cases_on `xs`
 >- (REV_FULL_SIMP_TAC std_ss [NULL] \\
    `LENGTH (epsilon :'a Action list) <= n` by FULL_SIMP_TAC arith_ss [LENGTH] \\
     Q.PAT_X_ASSUM `!xs P' P. X ==> X'`
        (MP_TAC o (Q.SPECL [`[] :'a Action list`, `P'`, `(E :'a context) P`])) \\
     RW_TAC std_ss [] \\
     Q.EXISTS_TAC `C' o E` >> art [] \\
     CONJ_TAC >- (IMP_RES_TAC WG_IMP_CONTEXT \\
                  MATCH_MP_TAC CONTEXT_combin >> art []) \\
     CONJ_TAC >- (KILL_TAC >> REWRITE_TAC [o_DEF] >> RW_TAC std_ss []) \\
     GEN_TAC >> ASM_SIMP_TAC std_ss [o_DEF])
 >> FULL_SIMP_TAC list_ss []
 >> `LENGTH (FRONT (h::t)) <= n` by PROVE_TAC [LENGTH_FRONT_CONS]
 >> Q.ABBREV_TAC `xs = FRONT (h::t)`
 >> Q.ABBREV_TAC `x = LAST (h::t)`
 >> Q.PAT_X_ASSUM `!xs P'' P'''. X ==> X'`
        (MP_TAC o (Q.SPECL [`xs`, `u`, `(E :'a context) P`]))
 >> RW_TAC std_ss []
 >> MP_TAC (Q.SPECL [`C'`, `E`] OBS_unfolding_lemma3)
 >> RW_TAC bool_ss []
 >> POP_ASSUM (MP_TAC o (Q.SPECL [`P`, `x`, `P'`]))
 >> RW_TAC bool_ss []
 >> Q.EXISTS_TAC `C''` >> art []
 >> GEN_TAC >> ONCE_REWRITE_TAC [TRACE_cases2]
 >> REWRITE_TAC [NULL]
 >> Q.EXISTS_TAC `C' (E Q)`
 >> Q.UNABBREV_TAC `x` >> art []
 >> Q.UNABBREV_TAC `xs` >> art []
QED

(* Lemma 3.9 of [2] *)
val UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS_LEMMA = store_thm (
   "UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS_LEMMA",
  ``!(P :'a CCS) (Q :'a CCS) E.
        WG E /\ OBS_contracts P (E P) /\ OBS_contracts Q (E Q) ==>
        !(C :'a context). CONTEXT C ==>
            (!l R. WEAK_TRANS (C P) (label l) R ==>
                ?C'. CONTEXT C' /\ R contracts (C' P) /\
                     (WEAK_EQUIV O (\x y. WEAK_TRANS x (label l) y)) (C Q) (C' Q)) /\
            (!R. WEAK_TRANS (C P) tau R ==>
                ?C'. CONTEXT C' /\ R contracts (C' P) /\
                     (WEAK_EQUIV O EPS) (C Q) (C' Q))``,
    NTAC 6 STRIP_TAC
 (* Part 1: construct C'' which is a CONTEXT *)
 >> IMP_RES_TAC WG_IMP_CONTEXT
 >> Q.ABBREV_TAC `C'' = \n. C o (FUNPOW E n)`
 >> Know `!n. CONTEXT (C'' n)`
 >- (Q.UNABBREV_TAC `C''` >> BETA_TAC \\
     Induct_on `n` >- art [o_DEF, FUNPOW, ETA_THM] \\
     REWRITE_TAC [FUNPOW_SUC_LEFT, o_ASSOC] \\
     MATCH_MP_TAC CONTEXT_combin >> art []) >> DISCH_TAC
 (* Part 2: property of C'' on P and Q *)
 >> `!n. OBS_contracts (C P) (C'' n P)`
        by (Q.UNABBREV_TAC `C''` >> BETA_TAC >> PROVE_TAC [OBS_unfolding_lemma1])
 >> `!n. OBS_contracts (C Q) (C'' n Q)`
        by (Q.UNABBREV_TAC `C''` >> BETA_TAC >> PROVE_TAC [OBS_unfolding_lemma1])
 (* Part 3 *)
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [Action_distinct_label] \\
      `OBS_contracts (C P) (C'' (LENGTH us) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP OBS_contracts_AND_TRACE_label)) \\
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. CONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs' (C' Q)`
      >- (MATCH_MP_TAC OBS_unfolding_lemma4 >> art []) \\
      STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `OBS_contracts (C Q) ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `WEAK_TRANS (C (FUNPOW E n Q)) (label l) (C' Q)`
      >- (REWRITE_TAC [WEAK_TRANS_AND_TRACE, Action_distinct_label] \\
          Q.EXISTS_TAC `xs'` >> art [] \\
          MATCH_MP_TAC UNIQUE_LABEL_NOT_NULL \\
          Q.EXISTS_TAC `label l` >> art []) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC OBS_contracts_WEAK_TRANS_label' \\
      Q.EXISTS_TAC `E1` >> art [],
      (* goal 2 (of 2) *)
      IMP_RES_TAC WEAK_TRANS_AND_TRACE \\
      FULL_SIMP_TAC std_ss [] \\
      `OBS_contracts (C P) (C'' (LENGTH us) P)` by PROVE_TAC [] \\
      POP_ASSUM (IMP_RES_TAC o (MATCH_MP OBS_contracts_AND_TRACE_tau)) \\ (* diff here *)
      NTAC 4 (POP_ASSUM K_TAC) \\
      Q.ABBREV_TAC `n = LENGTH us` \\
      Q.UNABBREV_TAC `C''` \\
      Q.PAT_X_ASSUM `TRACE X xs' E2` (ASSUME_TAC o BETA_RULE) \\
      Know `?C'. CONTEXT C' /\ (E2 = C' P) /\ !Q. TRACE ((C o FUNPOW E n) Q) xs' (C' Q)`
      >- (MATCH_MP_TAC OBS_unfolding_lemma4 >> art []) \\
      STRIP_TAC >> POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
      `OBS_contracts (C Q) ((C o FUNPOW E n) Q)` by PROVE_TAC [] \\
      FULL_SIMP_TAC std_ss [] \\ (* to replace E2 *)
      Q.EXISTS_TAC `C'` >> art [] \\
      Know `EPS (C (FUNPOW E n Q)) (C' Q)` (* diff here *)
      >- (REWRITE_TAC [EPS_AND_TRACE] \\
          Q.EXISTS_TAC `xs'` >> art []) >> DISCH_TAC \\
      REWRITE_TAC [O_DEF] >> BETA_TAC \\
      IMP_RES_TAC OBS_contracts_EPS' \\
      Q.EXISTS_TAC `E1` >> art [] ]);

(* Shared lemma for UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS and
   UNIQUE_SOLUTION_OF_ROOTED_CONTRACTIONS *)
val shared_lemma = Q.prove (
   `WG E /\ OBS_contracts P (E P) /\ OBS_contracts Q (E Q) ==>
    WEAK_BISIM (\R S. ?C. CONTEXT C /\
                          WEAK_EQUIV R (C P) /\ WEAK_EQUIV S (C Q))`,
    STRIP_TAC
 >> REWRITE_TAC [WEAK_BISIM]
 >> BETA_TAC >> rpt STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
        (MP_TAC o (Q.SPECL [`l`, `E1`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RW_TAC std_ss [] \\
      MP_TAC (Q.SPECL [`P`, `Q`, `E`] UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS_LEMMA) \\
      RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      POP_ASSUM K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`l`, `E2`])) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
        (MP_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      reverse CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 2 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
        (MP_TAC o (Q.SPECL [`l`, `E2`]) o (MATCH_MP WEAK_EQUIV_TRANS_label)) \\
      RW_TAC std_ss [] \\
      MP_TAC (Q.SPECL [`Q`, `P`, `E`] UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS_LEMMA) \\
      RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      POP_ASSUM K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPECL [`l`, `E2'`])) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
        (MP_TAC o (Q.SPECL [`l`, `y`]) o (MATCH_MP WEAK_EQUIV_WEAK_TRANS_label')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 3 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
        (MP_TAC o (Q.SPEC `E1`) o (MATCH_MP WEAK_EQUIV_TRANS_tau)) \\
      RW_TAC std_ss [] \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- (Q.EXISTS_TAC `E''` >> REWRITE_TAC [EPS_REFL] \\
          Q.EXISTS_TAC `C` >> art []) \\
      Q.PAT_X_ASSUM `EPS _ E2` K_TAC \\
      MP_TAC (Q.SPECL [`P`, `Q`, `E`] UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS_LEMMA) \\
      RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS (C P) (label l) R ==> X` K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `E2`)) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
        (MP_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1'` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      reverse CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS],
      (* goal 4 (of 4) *)
      Q.PAT_X_ASSUM `WEAK_EQUIV E'' (C Q)`
        (MP_TAC o (Q.SPEC `E2`) o (MATCH_MP WEAK_EQUIV_TRANS_tau)) \\
      RW_TAC std_ss [] \\
      IMP_RES_TAC EPS_IMP_WEAK_TRANS (* 2 sub-goals here *)
      >- (Q.EXISTS_TAC `E'` >> REWRITE_TAC [EPS_REFL] \\
          Q.EXISTS_TAC `C` >> art []) \\
      Q.PAT_X_ASSUM `EPS _ E2'` K_TAC \\
      MP_TAC (Q.SPECL [`Q`, `P`, `E`] UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS_LEMMA) \\
      RW_TAC std_ss [] \\
      POP_ASSUM (MP_TAC o (Q.SPEC `C`)) >> RW_TAC std_ss [] \\
      Q.PAT_X_ASSUM `!l R. WEAK_TRANS (C Q) (label l) R ==> X` K_TAC \\
      POP_ASSUM (MP_TAC o (Q.SPEC `E2'`)) >> RW_TAC std_ss [] \\
      POP_ASSUM MP_TAC >> REWRITE_TAC [O_DEF] >> BETA_TAC >> STRIP_TAC \\
      Q.PAT_X_ASSUM `WEAK_EQUIV E' (C P)`
        (MP_TAC o (Q.SPEC `y`) o (MATCH_MP WEAK_EQUIV_EPS')) \\
      RW_TAC std_ss [] \\
      Q.EXISTS_TAC `E1` >> art [] \\
      Q.EXISTS_TAC `C'` >> art [] \\
      CONJ_TAC >- PROVE_TAC [WEAK_EQUIV_TRANS] \\
      IMP_RES_TAC contracts_IMP_WEAK_EQUIV \\
      PROVE_TAC [WEAK_EQUIV_TRANS] ]);

Theorem UNIQUE_SOLUTION_OF_OBS_CONTRACTIONS :
    !E P Q. WG E /\ OBS_contracts P (E P) /\ OBS_contracts Q (E Q) ==> WEAK_EQUIV P Q
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [WEAK_EQUIV]
 >> Q.EXISTS_TAC `\R S. ?C. CONTEXT C /\ WEAK_EQUIV R (C P) /\ WEAK_EQUIV S (C Q)`
 >> BETA_TAC >> CONJ_TAC
 >- (Q.EXISTS_TAC `E` \\
     CONJ_TAC >- IMP_RES_TAC WG_IMP_CONTEXT \\
     IMP_RES_TAC OBS_contracts_IMP_WEAK_EQUIV >> art [])
 >> MATCH_MP_TAC shared_lemma >> art []
QED

(******************************************************************************)
(*                                                                            *)
(*      7. Unique solutions of rooted contractions (EXPRESS/SOS 2018)         *)
(*                                                                            *)
(******************************************************************************)

(* This is a stronger version of previous theorem: conclusion is `OBS_CONGR P Q`
   OBS_CONGR_BY_WEAK_BISIM and STRONG_UNIQUE_SOLUTION_LEMMA must be used here.
 *)
Theorem UNIQUE_SOLUTION_OF_ROOTED_CONTRACTIONS :
    !E P Q. WG E /\ OBS_contracts P (E P) /\ OBS_contracts Q (E Q) ==> OBS_CONGR P Q
Proof
    rpt STRIP_TAC
 >> irule OBS_CONGR_BY_WEAK_BISIM
 >> Q.EXISTS_TAC `\R S. ?C. CONTEXT C /\ WEAK_EQUIV R (C P) /\ WEAK_EQUIV S (C Q)`
 >> BETA_TAC >> CONJ_TAC
 >- (rpt STRIP_TAC >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
       IMP_RES_TAC STRONG_UNIQUE_SOLUTION_LEMMA \\
       POP_ASSUM (ASSUME_TAC o (Q.SPEC `Q`)) \\
       IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
       Q.EXISTS_TAC `E1'` >> art [] \\
       Q.EXISTS_TAC `E'` >> art [] \\
       fs [contracts_IMP_WEAK_EQUIV],
       (* goal 2 (of 2) *)
       IMP_RES_TAC OBS_contracts_TRANS_LEFT \\
       IMP_RES_TAC STRONG_UNIQUE_SOLUTION_LEMMA \\
       POP_ASSUM (ASSUME_TAC o (Q.SPEC `P`)) \\
       IMP_RES_TAC OBS_contracts_TRANS_RIGHT \\
       Q.EXISTS_TAC `E1'` >> art [] \\
       Q.EXISTS_TAC `E'` >> art [] \\
       fs [contracts_IMP_WEAK_EQUIV] ])
 >> MATCH_MP_TAC shared_lemma >> art []
QED

(* Bibliography:
 *
 * [1] Milner, R.: Communication and concurrency. (1989).
 * [2] Sangiorgi, D.: Equations, contractions, and unique solutions. ACM SIGPLAN Notices. (2015).
 *)

val _ = export_theory ();
val _ = print_theory_to_file "-" "UniqueSolutionsTheory.lst";
val _ = html_theory "UniqueSolutions";
