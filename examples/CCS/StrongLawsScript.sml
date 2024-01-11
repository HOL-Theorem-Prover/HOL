(* ========================================================================== *)
(* FILE          : StrongLawsScript.sml                                       *)
(* DESCRIPTION   : Laws of strong equivalence (STRONG_EQUIV)                  *)
(*                                                                            *)
(* COPYRIGHTS    : 1991-1995 University of Cambridge, UK (Monica Nesi)        *)
(*                 2016-2017 University of Bologna, Italy (Chun Tian)         *)
(*                 2018-2019 Fondazione Bruno Kessler, Italy (Chun Tian)      *)
(*                 2023-2024 The Australian National University (Chun Tian)   *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory prim_recTheory arithmeticTheory relationTheory;

open CCSLib CCSTheory StrongEQTheory StrongEQLib;

val _ = new_theory "StrongLaws";

(******************************************************************************)
(*                                                                            *)
(*  Basic laws of strong equivalence for the sum operator (sum_strong_laws)   *)
(*                                                                            *)
(******************************************************************************)

(* Prove STRONG_SUM_IDENT_R: |- !E. STRONG_EQUIV (sum E nil) E *)
val STRONG_SUM_IDENT_R = store_thm (
   "STRONG_SUM_IDENT_R",``!E. STRONG_EQUIV (sum E nil) E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/ (?E'. (x = sum E' nil) /\ (y = E'))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      DISJ2_TAC \\
      EXISTS_TAC ``E :'a CCS`` \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        art [REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                 (ASSUME ``TRANS E u E1``)],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = sum E'' nil``]
                            (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_SUM_NIL \\
        Q.EXISTS_TAC `E1`  >> art [],
        (* goal 2.4 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' :'a CCS = E''``]
                            (ASSUME ``TRANS E' u E2``)) \\
        Q.EXISTS_TAC `E2` >> art [] \\
        MATCH_MP_TAC SUM1 \\
        PURE_ONCE_ASM_REWRITE_TAC [] ] ]);

(* Prove STRONG_SUM_IDEMP: |- !E. STRONG_EQUIV (sum E E) E *)
val STRONG_SUM_IDEMP = store_thm (
   "STRONG_SUM_IDEMP", ``!E. STRONG_EQUIV (sum E E) E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/ (?E'. (x = sum E' E') /\ (y = E'))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      DISJ2_TAC \\
      EXISTS_TAC ``E :'a CCS`` \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        art [REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                      (ASSUME ``TRANS E u E1``)],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = sum E'' E''``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_P_SUM_P \\
        Q.EXISTS_TAC `E1`  >> art [],
        (* goal 2.4 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [] \\
        MATCH_MP_TAC SUM1 \\
        PURE_ONCE_REWRITE_TAC [REWRITE_RULE [ASSUME ``E' :'a CCS = E''``]
                                            (ASSUME ``TRANS E' u E2``)] ] ]);

(* Prove STRONG_SUM_COMM: |- !E E'. STRONG_EQUIV(sum E E') (sum E' E) *)
val STRONG_SUM_COMM = store_thm (
   "STRONG_SUM_COMM", ``!E E'. STRONG_EQUIV (sum E E') (sum E' E)``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/ (?E1 E2. (x = sum E1 E2) /\ (y = sum E2 E1))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      DISJ2_TAC \\
      EXISTS_TAC ``E :'a CCS`` \\
      EXISTS_TAC ``E' :'a CCS`` \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        art [REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                      (ASSUME ``TRANS E u E1``)],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        EXISTS_TAC ``E1' :'a CCS`` \\
        art [REWRITE_RULE [ASSUME ``E = sum E1 E2``]
                                      (ASSUME ``TRANS E u E1'``),
                         TRANS_COMM_EQ],
        (* goal 2.4 (of 4) *)
        EXISTS_TAC ``E2' :'a CCS`` \\
        art [REWRITE_RULE [ASSUME ``E' = sum E2 E1``]
                                      (ASSUME ``TRANS E' u E2'``),
                         TRANS_COMM_EQ] ] ]);

(* Prove STRONG_SUM_IDENT_L: |- !E. STRONG_EQUIV (sum nil E) E *)
val STRONG_SUM_IDENT_L = save_thm (
   "STRONG_SUM_IDENT_L",
    GEN ``E :'a CCS``
       (S_TRANS (SPECL [``nil``, ``E :'a CCS``] STRONG_SUM_COMM)
                (SPEC ``E :'a CCS`` STRONG_SUM_IDENT_R)));

val STRONG_SUM_ASSOC_R = store_thm (
   "STRONG_SUM_ASSOC_R",
      ``!E E' E''.
         STRONG_EQUIV (sum (sum E E') E'') (sum E (sum E' E''))``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
      ``\x y. (x = y) \/ (?E1 E2 E3. (x = sum (sum E1 E2) E3) /\
                                     (y = sum E1 (sum E2 E3)))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      DISJ2_TAC \\
      take [`E`, `E'`, `E''`] \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals *)
      [ (* goal 2.1 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        art [REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                      (ASSUME ``TRANS E u E1``)],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        EXISTS_TAC ``E1' :'a CCS``  >> art [] \\
        art [REWRITE_RULE [ASSUME ``E = sum (sum E1 E2) E3``]
                                      (ASSUME ``TRANS E u E1'``),
                         SYM (SPEC_ALL TRANS_ASSOC_EQ)],
        (* goal 2.4 (of 4) *)
        EXISTS_TAC ``E2' :'a CCS`` \\
        art [REWRITE_RULE [ASSUME ``E' = sum E1 (sum E2 E3)``]
                                      (ASSUME ``TRANS E' u E2'``),
                         TRANS_ASSOC_EQ] ] ]);

(* STRONG_SUM_ASSOC_L:
   |- !E E' E''. STRONG_EQUIV (sum E (sum E' E'')) (sum (sum E E') E'')
 *)
val STRONG_SUM_ASSOC_L = save_thm (
   "STRONG_SUM_ASSOC_L",
    STRIP_FORALL_RULE S_SYM STRONG_SUM_ASSOC_R);

(* STRONG_SUM_MID_IDEMP:
   |- !E E'. STRONG_EQUIV (sum (sum E E') E) (sum E' E)
 *)
val STRONG_SUM_MID_IDEMP = save_thm (
   "STRONG_SUM_MID_IDEMP",
    GEN ``E :'a CCS``
     (GEN ``E' :'a CCS``
       (S_TRANS
        (SPEC ``E :'a CCS``
         (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
          (Q.SPECL [`E`, `E'`] STRONG_SUM_COMM)))
        (S_TRANS
         (Q.SPECL [`E'`, `E`, `E`] STRONG_SUM_ASSOC_R)
         (SPEC ``E' :'a CCS``
          (MATCH_MP STRONG_EQUIV_SUBST_SUM_L
           (SPEC ``E :'a CCS`` STRONG_SUM_IDEMP)))))));

(* STRONG_LEFT_SUM_MID_IDEMP:
   |- !E E' E''. STRONG_EQUIV (sum (sum (sum E E') E'') E') (sum (sum E E'') E')
 *)
val STRONG_LEFT_SUM_MID_IDEMP = save_thm (
   "STRONG_LEFT_SUM_MID_IDEMP",
  ((GEN ``E :'a CCS``) o
   (GEN ``E' :'a CCS``) o
   (GEN ``E'' :'a CCS``))
      (S_TRANS
        (S_TRANS
         (SPEC ``E' :'a CCS``
          (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
           (SPEC ``E'' :'a CCS``
            (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
             (SPECL [``E :'a CCS``, ``E' :'a CCS``] STRONG_SUM_COMM)))))
         (SPEC ``E' :'a CCS``
          (MATCH_MP STRONG_EQUIV_SUBST_SUM_R
           (SPECL [``E' :'a CCS``, ``E :'a CCS``, ``E'' :'a CCS``]
                  STRONG_SUM_ASSOC_R))))
        (SPECL [``E' :'a CCS``, ``sum E E''``] STRONG_SUM_MID_IDEMP)));

(* Unused recursion variables have the same behavior as `nil` *)
Theorem STRONG_EQUIV_NIL_VAR :
    !X. STRONG_EQUIV nil (var X)
Proof
    GEN_TAC
 >> ONCE_REWRITE_TAC [PROPERTY_STAR]
 >> RW_TAC std_ss [NIL_NO_TRANS, VAR_NO_TRANS]
QED

(******************************************************************************)
(*                                                                            *)
(*  Basic laws of strong equivalence for the par operator (par_strong_laws)   *)
(*                                                                            *)
(******************************************************************************)

(* Prove STRONG_PAR_IDENT_R: |- !E. STRONG_EQUIV (par E nil) E *)
val STRONG_PAR_IDENT_R = store_thm (
   "STRONG_PAR_IDENT_R", ``!E. STRONG_EQUIV (par E nil) E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\x y. (?E'. (x = par E' nil) /\ (y = E'))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      EXISTS_TAC ``E :'a CCS`` \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par E'' nil``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_PAR_P_NIL \\
        EXISTS_TAC ``E''' :'a CCS``  >> art [] \\
        EXISTS_TAC ``E''' :'a CCS``  >> art [],
        (* goal 2.2 (of 2) *)
        EXISTS_TAC ``par E2 nil`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          PURE_ONCE_ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC PAR1 \\
          ASSUME_TAC (REWRITE_RULE [ASSUME ``E' :'a CCS = E''``]
                                   (ASSUME ``TRANS E' u E2``)) \\
          PURE_ONCE_ASM_REWRITE_TAC [],
          (* goal 2.2.2 (of 2) *)
          Q.EXISTS_TAC `E2` \\
          REWRITE_TAC [] ] ] ]);

val STRONG_PAR_COMM = store_thm (
   "STRONG_PAR_COMM", ``!E E'. STRONG_EQUIV (par E E') (par E' E)``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\x y. (?E1 E2. (x = par E1 E2) /\ (y = par E2 E1))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`] >> REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par E1 E2``]
                                 (ASSUME ``TRANS E u E1'``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 2.1.1 (of 3) *)
          EXISTS_TAC ``par E2 E1''`` >> art [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1.1 (of 2) *)
            MATCH_MP_TAC PAR2 \\
            PURE_ONCE_ASM_REWRITE_TAC [],
            (* goal 2.1.1.2 (of 2) *)
            take [`E1''`, `E2`] >> REWRITE_TAC [] ],
          (* goal 2.1.2 (of 3) *)
          EXISTS_TAC ``par E1'' E1`` >> art [] \\
          CONJ_TAC >| (* 2 sub-goals *)
          [ (* goal 2.1.2.1 (of 2) *)
            MATCH_MP_TAC PAR1 \\
            PURE_ONCE_ASM_REWRITE_TAC [],
            (* goal 2.1.2.2 (of 2) *)
            take [`E1`, `E1''`] >> REWRITE_TAC [] ],
          (* goal 2.1.3 (of 3) *)
          EXISTS_TAC ``par E2' E1''`` >> art [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.3.1 (of 2) *)
            MATCH_MP_TAC PAR3 \\
            EXISTS_TAC ``COMPL (l :'a Label)`` >> art [COMPL_COMPL_LAB],
            (* goal 2.1.3.2 (of 2) *)
            take [`E1''`, `E2'`] >> REWRITE_TAC [] ] ],
         (* goal 2.2 (of 2) *)
         ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = par E2 E1``]
                                  (ASSUME ``TRANS E' u E2'``)) \\
         IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
         [ (* goal 2.2.1 (of 3) *)
           EXISTS_TAC ``par E1 E1'`` \\
           art [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.1.1 (of 2) *)
             MATCH_MP_TAC PAR2 \\
             PURE_ONCE_ASM_REWRITE_TAC [],
             (* goal 2.2.1.2 (of 2) *)
             take [`E1`, `E1'`] >> REWRITE_TAC [] ],
           (* goal 2.2.2 (of 3) *)
           EXISTS_TAC ``par E1' E2`` >> art [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.2.1 (of 2) *)
             MATCH_MP_TAC PAR1 \\
             PURE_ONCE_ASM_REWRITE_TAC [],
             (* goal 2.2.2.2 (of 2) *)
             take [`E1'`, `E2`] >> REWRITE_TAC [] ],
           (* goal 2.2.3 (of 3) *)
           EXISTS_TAC ``par E2'' E1'`` >> art [] \\
           CONJ_TAC >| (* 2 sub-goals *)
           [ (* goal 2.2.3.1 (of 2) *)
             MATCH_MP_TAC PAR3 \\
             EXISTS_TAC ``COMPL (l :'a Label)`` \\
             art [COMPL_COMPL_LAB],
             (* goal 2.2.3.2 (of 2) *)
             take [`E2''`, `E1'`] >> REWRITE_TAC [] ] ] ] ]);

(* STRONG_PAR_IDENT_L: |- !E. STRONG_EQUIV (par nil E) E *)
val STRONG_PAR_IDENT_L = save_thm (
   "STRONG_PAR_IDENT_L",
    GEN_ALL
       (S_TRANS (SPECL [``nil``, ``E :'a CCS``] STRONG_PAR_COMM)
                (SPEC ``E :'a CCS`` STRONG_PAR_IDENT_R)));

val STRONG_PAR_ASSOC = store_thm (
   "STRONG_PAR_ASSOC",
      ``!E E' E''. STRONG_EQUIV (par (par E E') E'') (par E (par E' E''))``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
      ``\x y. (?E1 E2 E3.
               (x = par (par E1 E2) E3) /\ (y = par E1 (par E2 E3)))``
 >> CONJ_TAC (* 2 sub-goals *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`, `E''`] \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par (par E1 E2) E3``]
                            (ASSUME ``TRANS E u E1'``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals *)
        [ (* goal 2.1.1 (of 3) *)
          STRIP_ASSUME_TAC
            (MATCH_MP TRANS_PAR
                      (ASSUME ``TRANS (par E1 E2) u E1''``)) >| (* 3 sub-goals here *)
          [ (* goal 2.1.1.1 (of 3) *)
            EXISTS_TAC ``par E1''' (par E2 E3)`` >> art [] \\
            CONJ_TAC >| (* 2 sub-goals here *)
            [ (* goal 2.1.1.1.1 (of 2) *)
              MATCH_MP_TAC PAR1 \\
              PURE_ONCE_ASM_REWRITE_TAC [],
              (* goal 2.1.1.1.2 (of 2) *)
              take [`E1'''`, `E2`, `E3`] \\
              art [] ],
            (* goal 2.1.1.2 (of 3) *)
            EXISTS_TAC ``par E1 (par E1''' E3)`` >> art [] \\
            CONJ_TAC >| (* 2 sub-goals here *)
            [ (* goal 2.1.1.2.1 (of 2) *)
              MATCH_MP_TAC PAR2 \\
              MATCH_MP_TAC PAR1 \\
              PURE_ONCE_ASM_REWRITE_TAC [],
              (* goal 2.1.1.2.2 (of 2) *)
              take [`E1`, `E1'''`, `E3`] \\
              art [] ],
            (* goal 2.1.1.3 (of 3) *)
            EXISTS_TAC ``par E1'''(par E2' E3)`` >> art [] \\
            CONJ_TAC >| (* 2 sub-goals here *)
            [ (* goal 2.1.1.3.1 (of 2) *)
              MATCH_MP_TAC PAR3 \\
              Q.EXISTS_TAC `l` \\
              art [] \\
              MATCH_MP_TAC PAR1 \\
              PURE_ONCE_ASM_REWRITE_TAC [],
              (* goal 2.1.1.3.2 (of 2) *)
              take [`E1'''`, `E2'`, `E3`] \\
              art [] ] ],
          (* goal 2.1.2 (of 3) *)
          EXISTS_TAC ``par E1 (par E2 E1'')`` \\
          CONJ_TAC >| (* 2 sub-goals *)
          [ (* goal 2.1.2.1 (of 2) *)
            PURE_ONCE_ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC PAR2 \\
            MATCH_MP_TAC PAR2 \\
            PURE_ONCE_ASM_REWRITE_TAC [],
            (* goal 2.1.2.2 (of 2) *)
            take [`E1`, `E2`, `E1''`] >> art [] ],
          (* goal 2.1.3 (of 3) *)
          STRIP_ASSUME_TAC (* 3 sub-goals here *)
            (MATCH_MP TRANS_PAR
                      (ASSUME ``TRANS (par E1 E2) (label l) E1''``)) >|
          [ (* goal 2.1.3.1 (of 3) *)
            EXISTS_TAC ``par E1''' (par E2 E2')`` >> art [] \\
            CONJ_TAC >| (* 2 sub-goals here *)
            [ (* goal 2.1.3.1.1 (of 2) *)
              MATCH_MP_TAC PAR3 \\
              Q.EXISTS_TAC `l` \\
              art [] \\
              MATCH_MP_TAC PAR2 \\
              PURE_ONCE_ASM_REWRITE_TAC [],
              (* goal 2.1.3.1.2 (of 2) *)
              take [`E1'''`, `E2`, `E2'`] \\
              art [] ],
            (* goal 2.1.3.2 (of 3) *)
            EXISTS_TAC ``par E1 (par E1''' E2')`` >> art [] \\
            CONJ_TAC >| (* 2 sub-goals *)
            [ (* goal 2.1.3.2.1 (of 2) *)
              MATCH_MP_TAC PAR2 \\
              MATCH_MP_TAC PAR3 \\
              Q.EXISTS_TAC `l` >> art [],
              (* goal 2.1.3.2.2 (of 2) *)
              take [`E1`, `E1'''`, `E2'`] >> art [] ],
            (* goal 2.1.3.3 (of 3) *)
            IMP_RES_TAC Action_distinct_label ] ],
         (* goal 2.2 (of 2) *)
         ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = par E1(par E2 E3)``]
                                  (ASSUME ``TRANS E' u E2'``)) \\
         IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
         [ (* goal 2.2.1 (of 3) *)
           EXISTS_TAC ``par (par E1' E2) E3`` >> art [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.1.1 (of 2) *)
             MATCH_MP_TAC PAR1 \\
             MATCH_MP_TAC PAR1 \\
             PURE_ONCE_ASM_REWRITE_TAC [],
             (* goal 2.2.1.2 (of 2) *)
             take [`E1'`, `E2`, `E3`] \\
             art [] ],
           (* goal 2.2.2 (of 3) *)
           STRIP_ASSUME_TAC (* 3 sub-goals here *)
             (MATCH_MP TRANS_PAR
                       (ASSUME ``TRANS (par E2 E3) u E1'``)) >|
           [ (* goal 2.2.2.1 (of 3) *)
             EXISTS_TAC ``par (par E1 E1'') E3`` \\
             art [] \\
             CONJ_TAC >| (* 2 sub-goals *)
             [ (* goal 2.2.2.1.1 (of 2) *)
               MATCH_MP_TAC PAR1 \\
               MATCH_MP_TAC PAR2 \\
               PURE_ONCE_ASM_REWRITE_TAC [],
               (* goal 2.2.2.1.2 (of 2) *)
               take [`E1`, `E1''`, `E3`] >> art [] ],
             (* goal 2.2.2.2 (of 3) *)
             EXISTS_TAC ``par (par E1 E2) E1''`` \\
             art [] \\
             CONJ_TAC >|
             [ MATCH_MP_TAC PAR2 \\
               PURE_ONCE_ASM_REWRITE_TAC [],
               take [`E1`, `E2`, `E1''`] >> art [] ],
             (* goal 2.2.2.3 (of 3) *)
             EXISTS_TAC ``par (par E1 E1'') E2''`` \\
             art [] \\
             CONJ_TAC >| (* 2 sub-goals here *)
             [ (* goal 2.2.2.3.1 (of 2) *)
               MATCH_MP_TAC PAR3 \\
               Q.EXISTS_TAC `l` \\
               art [] \\
               MATCH_MP_TAC PAR2 >> PURE_ONCE_ASM_REWRITE_TAC [],
               (* goal 2.2.2.3.2 (of 2) *)
               take [`E1`, `E1''`, `E2''`] >> art [] ] ],
           (* goal 2.2.3 (of 3) *)
           STRIP_ASSUME_TAC (* 3 sub-goals here *)
             (MATCH_MP TRANS_PAR
                       (ASSUME ``TRANS (par E2 E3) (label (COMPL l)) E2''``)) >|
           [ (* goal 2.2.3.1 (of 3) *)
             EXISTS_TAC ``par (par E1' E1'') E3`` \\
             art [] \\
             CONJ_TAC >| (* 2 sub-goals *)
             [ (* goal 2.2.3.1.1 *)
               MATCH_MP_TAC PAR1 \\
               MATCH_MP_TAC PAR3 \\
               Q.EXISTS_TAC `l` >> art [],
               (* goal 2.2.3.1.2 *)
               take [`E1'`, `E1''`, `E3`] >> art [] ],
             (* goal 2.2.3.2 (of 3) *)
             EXISTS_TAC ``par (par E1' E2) E1''`` \\
             art [] \\
             CONJ_TAC >| (* 2 sub-goals here *)
             [ (* goal 2.2.3.2.1 (of 2) *)
               MATCH_MP_TAC PAR3 \\
               Q.EXISTS_TAC `l` \\
               art [] \\
               MATCH_MP_TAC PAR1 >> PURE_ONCE_ASM_REWRITE_TAC [],
               (* goal 2.2.3.2.2 (of 2) *)
               take [`E1'`, `E2`, `E1''`] >> art [] ],
             (* goal 2.2.3.3 (of 3) *)
             IMP_RES_TAC Action_distinct_label] ] ] ]);

val STRONG_PAR_PREF_TAU = store_thm (
   "STRONG_PAR_PREF_TAU",
      ``!(u :'a Action) E E'.
         STRONG_EQUIV (par (prefix u E) (prefix tau E'))
                      (sum (prefix u (par E (prefix tau E')))
                           (prefix tau (par (prefix u E) E')))``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/
              (?(u' :'a Action) E1 E2. (x = par (prefix u' E1) (prefix tau E2)) /\
                                       (y = sum (prefix u' (par E1 (prefix tau E2)))
                                                (prefix tau (par (prefix u' E1) E2))))``
 >> CONJ_TAC (* 2 sub-goals *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      DISJ2_TAC \\
      take [`u`, `E`, `E'`] \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                 (ASSUME ``TRANS E u E1``)) \\
        Q.EXISTS_TAC `E1`  >> art [],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        EXISTS_TAC ``E1' :'a CCS``  >> art [] \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par (prefix u' E1) (prefix tau E2)``]
                                 (ASSUME ``TRANS E u E1'``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals *)
        [ (* goal 2.3.1 (of 3) *)
          IMP_RES_TAC TRANS_PREFIX \\
          MATCH_MP_TAC SUM1 >> art [PREFIX],
          (* goal 2.3.2 (of 3) *)
          IMP_RES_TAC TRANS_PREFIX \\
          MATCH_MP_TAC SUM2 >> art [PREFIX],
          (* goal 2.3.3 (of 3) *)
          IMP_RES_TAC TRANS_PREFIX \\
          IMP_RES_TAC Action_distinct_label ],
        (* goal 2.4 (of 4) *)
        EXISTS_TAC ``E2' :'a CCS``  >> art [] \\
        ASSUME_TAC (REWRITE_RULE
                     [ASSUME ``E' = sum (prefix u' (par E1 (prefix tau E2)))
                                        (prefix tau (par (prefix u' E1) E2))``]
                     (ASSUME ``TRANS E' u E2'``)) \\
        IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
        [ (* goal 2.4.1 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX \\
          PURE_ONCE_ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC PAR1 \\
          REWRITE_TAC [PREFIX],
          (* goal 2.4.2 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX \\
          PURE_ONCE_ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC PAR2 \\
          REWRITE_TAC [PREFIX] ] ] ]);

(* Prove STRONG_PAR_TAU_PREF:
   |- !E u E'.
       STRONG_EQUIV
        (par (prefix tau E) (prefix u E'))
        (sum (prefix tau (par E (prefix u E')))
             (prefix u (par (prefix tau E) E')))
 *)
val STRONG_PAR_TAU_PREF = save_thm (
   "STRONG_PAR_TAU_PREF",
  ((GEN ``E :'a CCS``) o
   (GEN ``u :'a Action``) o
   (GEN ``E' :'a CCS``))
      (S_TRANS
        (S_TRANS
          (S_TRANS
            (SPECL [``prefix (tau :'a Action) E``, ``prefix (u :'a Action) E'``] STRONG_PAR_COMM)
            (SPECL [``u :'a Action``, ``E' :'a CCS``, ``E :'a CCS``] STRONG_PAR_PREF_TAU))
          (SPECL [``prefix (u :'a Action) (par E' (prefix tau E))``,
                  ``prefix (tau :'a Action) (par (prefix u E') E)``] STRONG_SUM_COMM))
        (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM
         (CONJ (SPEC ``tau :'a Action``
                (MATCH_MP STRONG_EQUIV_SUBST_PREFIX
                 (SPECL [``prefix (u :'a Action) E'``, ``E :'a CCS``] STRONG_PAR_COMM)))
               (SPEC ``u :'a Action``
                (MATCH_MP STRONG_EQUIV_SUBST_PREFIX
                 (SPECL [``E' :'a CCS``, ``prefix (tau :'a Action) E``] STRONG_PAR_COMM)))))));

(* Prove STRONG_PAR_TAU_TAU:
   |- ∀E E'. τ..E || τ..E' ~ τ..(E || τ..E') + τ..(τ..E || E')
 *)
val STRONG_PAR_TAU_TAU = save_thm (
   "STRONG_PAR_TAU_TAU", SPEC ``tau :'a Action`` STRONG_PAR_PREF_TAU);

(* Prove STRONG_PAR_PREF_NO_SYNCR:
   |- ∀l l'.
     l ≠ COMPL l' ⇒
     ∀E E'.
       label l..E || label l'..E' ~
       label l..(E || label l'..E') + label l'..(label l..E || E')
 *)
val STRONG_PAR_PREF_NO_SYNCR = store_thm (
   "STRONG_PAR_PREF_NO_SYNCR",
      ``!(l :'a Label) l'.
         ~(l = COMPL l') ==>
         (!E E'.
           STRONG_EQUIV
           (par (prefix (label l) E) (prefix (label l') E'))
           (sum (prefix (label l) (par E (prefix (label l') E')))
                (prefix (label l') (par (prefix (label l) E) E'))))``,
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/
           ?(l1 :'a Label) l2 E1 E2. ~(l1 = COMPL l2) /\
               (x = par (prefix (label l1) E1) (prefix (label l2) E2)) /\
               (y = sum (prefix (label l1) (par E1 (prefix (label l2) E2)))
                        (prefix (label l2) (par (prefix (label l1) E1) E2)))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      DISJ2_TAC \\
      take [`l`, `l'`, `E`, `E'`] >> art [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                 (ASSUME ``TRANS E u E1``)) \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        EXISTS_TAC ``E1' :'a CCS`` >> art [] \\
        ASSUME_TAC (REWRITE_RULE
                     [ASSUME ``E = par (prefix (label l1) E1) (prefix (label l2) E2)``]
                            (ASSUME ``TRANS E u E1'``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 2.3.1 (of 3) *)
          MATCH_MP_TAC SUM1 >> IMP_RES_TAC TRANS_PREFIX >> art [PREFIX],
          (* goal 2.3.2 (of 3) *)
          MATCH_MP_TAC SUM2 >> IMP_RES_TAC TRANS_PREFIX >> art [PREFIX],
          (* goal 2.3.3 (of 3) *)
          IMP_RES_TAC TRANS_PAR_NO_SYNCR \\
          ASSUME_TAC (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                      (ASSUME ``TRANS (par (prefix (label l1) E1)
                                           (prefix (label l2) E2)) u E1'``)) \\
          RES_TAC ],
        (* goal 2.4 (of 4) *)
        EXISTS_TAC ``E2' :'a CCS``  >> art [] \\
        ASSUME_TAC (REWRITE_RULE
                        [ASSUME ``E' = sum
                             (prefix (label l1) (par E1 (prefix (label l2) E2)))
                             (prefix (label l2) (par (prefix (label l1) E1) E2))``]
                     (ASSUME ``TRANS E' u E2'``)) \\
        IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals, sharing initial and end tacticals *)
        IMP_RES_TAC TRANS_PREFIX \\
        PURE_ONCE_ASM_REWRITE_TAC [] >|
        [ MATCH_MP_TAC PAR1, MATCH_MP_TAC PAR2 ] \\
        REWRITE_TAC [PREFIX] ] ]);

(* Prove STRONG_PAR_PREF_SYNCR:
   |- ∀l l'.
     (l = COMPL l') ⇒
     ∀E E'.
       label l..E || label l'..E' ~
       label l..(E || label l'..E') + label l'..(label l..E || E') +
       τ..(E || E')
 *)
val STRONG_PAR_PREF_SYNCR = store_thm (
   "STRONG_PAR_PREF_SYNCR",
  ``!(l :'a Label) l'. (l = COMPL l') ==>
         !E E'.
           STRONG_EQUIV
           (par (prefix (label l) E) (prefix (label l') E'))
           (sum
            (sum (prefix (label l) (par E (prefix (label l') E')))
                 (prefix (label l') (par (prefix (label l) E) E')))
            (prefix tau (par E E')))``,
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/
           ?(l1 :'a Label) l2 E1 E2.
               (l1 = COMPL l2) /\
               (x = par (prefix (label l1) E1) (prefix (label l2) E2)) /\
               (y = sum
                    (sum (prefix (label l1) (par E1 (prefix (label l2) E2)))
                         (prefix (label l2) (par (prefix (label l1) E1) E2)))
                    (prefix tau (par E1 E2)))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      DISJ2_TAC \\
      take [`l`, `l'`, `E`, `E'`] >> art [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                 (ASSUME ``TRANS E u E1``)) \\
        Q.EXISTS_TAC `E1`  >> art [],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        EXISTS_TAC ``E1' :'a CCS``  >> art [] \\
        ASSUME_TAC (REWRITE_RULE
                        [ASSUME ``E = par (prefix (label l1) E1) (prefix (label l2) E2)``]
                        (ASSUME ``TRANS E u E1'``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here, sharing end tacticals *)
        [ (* goal 2.3.1 (of 3) *)
          MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM1,
          (* goal 2.3.2 (of 3) *)
          MATCH_MP_TAC SUM1 >> MATCH_MP_TAC SUM2,
          (* goal 2.3.3 (of 3) *)
          MATCH_MP_TAC SUM2 ] \\
        IMP_RES_TAC TRANS_PREFIX \\
        art [PREFIX],
        (* goal 2.4 (of 4) *)
        EXISTS_TAC ``E2' :'a CCS``  >> art [] \\
        ASSUME_TAC (REWRITE_RULE
                     [ASSUME ``E' = sum (sum (prefix (label l1) (par E1 (prefix (label l2) E2)))
                                             (prefix (label l2) (par (prefix (label l1) E1) E2)))
                                        (prefix tau (par E1 E2))``]
                     (ASSUME ``TRANS E' u E2'``)) \\
        IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
        [ (* goal 2.4.1 (of 2) *)
          IMP_RES_TAC TRANS_SUM >| (* 4 sub-goals here *)
          [ (* goal 2.4.1.1 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX >> art [] \\
            MATCH_MP_TAC PAR1 >> REWRITE_TAC [PREFIX],
            (* goal 2.4.1.2 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX \\
            CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                             (ASSUME ``(u :'a Action) = label l1``)),
            (* goal 2.4.1.3 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX >> art [] \\
            MATCH_MP_TAC PAR2 >> REWRITE_TAC [PREFIX],
            (* goal 2.4.1.4 (of 4) *)
            IMP_RES_TAC TRANS_PREFIX \\
            CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                             (ASSUME ``(u :'a Action) = label l2``)) ],
          (* goal 2.4.2 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX >> art [] \\
          MATCH_MP_TAC PAR3 \\
          EXISTS_TAC ``COMPL (l2 :'a Label)`` \\
          REWRITE_TAC [COMPL_COMPL_LAB, PREFIX] ] ] ]);

(******************************************************************************)
(*                                                                            *)
(*      Basic laws of strong equivalence for the restriction operator         *)
(*                                                                            *)
(******************************************************************************)

val STRONG_RESTR_NIL = store_thm (
   "STRONG_RESTR_NIL", ``!L :'a Label set. STRONG_EQUIV (restr L nil) nil``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\(x :'a CCS) (y :'a CCS). (?L'. (x = restr L' nil) /\ (y = nil))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC >> EXISTS_TAC ``L :'a Label set`` >> REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] >> BETA_TAC \\
      rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L' nil``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC RESTR_NIL_NO_TRANS,
        (* goal 2.2 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = nil``]
                                 (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC NIL_NO_TRANS ] ]);

(* Prove STRONG_RESTR_SUM:
   |- ∀E E' L. restr L (E + E') ~ restr L E + restr L E'
 *)
val STRONG_RESTR_SUM = store_thm (
   "STRONG_RESTR_SUM",
      ``!E E' L.
         STRONG_EQUIV (restr L (sum E E')) (sum (restr L E) (restr L E'))``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [PROPERTY_STAR]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E1` \\
      REWRITE_TAC [STRONG_EQUIV_REFL] \\
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          art [] >> MATCH_MP_TAC SUM1 \\
          MATCH_MP_TAC RESTR \\
          REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                       (ASSUME ``TRANS E u E''``)],
          (* goal 1.1.2 (of 2) *)
          art [] >> MATCH_MP_TAC SUM2 \\
          MATCH_MP_TAC RESTR \\
          REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                       (ASSUME ``TRANS E' u E''``)] ],
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          art [] >> MATCH_MP_TAC SUM1 \\
          MATCH_MP_TAC RESTR \\
          Q.EXISTS_TAC `l` >> art [REWRITE_RULE [ASSUME ``(u :'a Action) = label l``]
                           (ASSUME ``TRANS E u E''``)],
          (* goal 1.2.2 (of 2) *)
          art [] >> MATCH_MP_TAC SUM2 \\
          MATCH_MP_TAC RESTR \\
          Q.EXISTS_TAC `l` >> art [REWRITE_RULE [ASSUME ``(u :'a Action) = label l``]
                           (ASSUME ``TRANS E' u E''``)] ] ],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E2` \\
      REWRITE_TAC [STRONG_EQUIV_REFL] \\
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          art [] \\
          MATCH_MP_TAC RESTR >> REWRITE_TAC [] \\
          MATCH_MP_TAC SUM1 \\
          REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                      (ASSUME ``TRANS E u E''``)],
          (* goal 2.1.2 (of 2) *)
          art [] \\
          MATCH_MP_TAC RESTR \\
          Q.EXISTS_TAC `l` >> art [] \\
          MATCH_MP_TAC SUM1 \\
          REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'a Action) = label l``]
                      (ASSUME ``TRANS E u E''``)] ],
        (* goal 2.2 (of 2) *)
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          art [] \\
          MATCH_MP_TAC RESTR >> REWRITE_TAC [] \\
          MATCH_MP_TAC SUM2 \\
          REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                      (ASSUME ``TRANS E' u E''``)],
          (* goal 2.2.2 (of 2) *)
          art[] \\
          MATCH_MP_TAC RESTR \\
          Q.EXISTS_TAC `l` >> art [] \\
          MATCH_MP_TAC SUM2 \\
          REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'a Action) = label l``]
                      (ASSUME ``TRANS E' u E''``)] ] ] ]);

(* Prove STRONG_RESTR_PREFIX_TAU:
   |- ∀E L. restr L (τ..E) ~ τ..restr L E
 *)
val STRONG_RESTR_PREFIX_TAU = store_thm (
   "STRONG_RESTR_PREFIX_TAU",
      ``!E L.
         STRONG_EQUIV (restr L (prefix tau E)) (prefix tau (restr L E))``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/ (?E' L'. (x = restr L' (prefix tau E')) /\
                                   (y = prefix tau (restr L' E')))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC >> DISJ2_TAC \\
      EXISTS_TAC ``E :'a CCS`` \\
      EXISTS_TAC ``L :'a Label set`` >> REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] >> BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                  (ASSUME ``TRANS E u E1``)],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L' (prefix tau E'')``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals *)
        [ (* goal 2.3.1 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX \\
          Q.EXISTS_TAC `E1` >> art [PREFIX],
          (* goal 2.3.2 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX \\
          CHECK_ASSUME_TAC
            (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                          (ASSUME ``(u :'a Action) = label l``)) ],
        (* goal 2.4 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = prefix tau (restr L' E'')``]
                                 (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC TRANS_PREFIX \\
        Q.EXISTS_TAC `E2` >> art [] \\
        MATCH_MP_TAC RESTR >> REWRITE_TAC [PREFIX] ] ]);

(* Prove STRONG_RESTR_PR_LAB_NIL:
   |- ∀l L. l ∈ L ∨ COMPL l ∈ L ⇒ ∀E. restr L (label l..E) ~ nil:
 *)
val STRONG_RESTR_PR_LAB_NIL = store_thm (
   "STRONG_RESTR_PR_LAB_NIL",
      ``!(l :'a Label) L.
         (l IN L) \/ ((COMPL l) IN L) ==>
         (!E. STRONG_EQUIV (restr L (prefix (label l) E)) nil)``,
    rpt GEN_TAC
 >> DISCH_TAC
 >> GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\(x :'a CCS) (y :'a CCS).
                    ?l' L' E'. ((l' IN L') \/ ((COMPL l') IN L')) /\
                                 (x = restr L' (prefix (label l') E')) /\
                                 (y = nil)``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`l`, `L`, `E`] >> art [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L' (prefix (label l') E'')``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC RESTR_LABEL_NO_TRANS,
        (* goal 2.2 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = nil``]
                                 (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC NIL_NO_TRANS,
        (* goal 2.3 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L' (prefix (label l') E'')``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC RESTR_LABEL_NO_TRANS,
        (* goal 2.4 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = nil``]
                                 (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC NIL_NO_TRANS ] ]);

(* Prove STRONG_RESTR_PREFIX_LABEL:
   |- ∀l L.
     l ∉ L ∧ COMPL l ∉ L ⇒ ∀E. restr L (label l..E) ~ label l..restr L E
 *)
val STRONG_RESTR_PREFIX_LABEL = store_thm (
   "STRONG_RESTR_PREFIX_LABEL",
       ``!(l :'a Label) L.
         (~(l IN L) /\ ~((COMPL l) IN L)) ==>
         (!E. STRONG_EQUIV (restr L (prefix (label l) E))
                           (prefix (label l) (restr L E)))``,
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/
              ?l' L' E'. ~(l' IN L') /\ ~((COMPL l') IN L') /\
                          (x = restr L' (prefix (label l') E')) /\
                          (y = prefix (label l') (restr L' E'))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC >> DISJ2_TAC \\
      take [`l`, `L`, `E`] >> art [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                 (ASSUME ``TRANS E u E1``)) \\
        Q.EXISTS_TAC `E1`  >> art [],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [] \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = restr L' (prefix (label l') E'')``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.3.1 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX \\
          CHECK_ASSUME_TAC
            (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                          (ASSUME ``(u :'a Action) = label l'``)),
          (* goal 2.3.2 (of 2) *)
          IMP_RES_TAC TRANS_PREFIX >> art [PREFIX] ],
        (* goal 2.4 (of 4) *)
        Q.EXISTS_TAC `E2` >> REWRITE_TAC [] \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = prefix (label l') (restr L' E'')``]
                                 (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC TRANS_PREFIX  >> art [] \\
        MATCH_MP_TAC RESTR \\
        EXISTS_TAC ``l' :'a Label`` \\
        art [PREFIX] ] ]);

(******************************************************************************)
(*                                                                            *)
(*      Basic axioms of strong equivalence for the relabeling operator        *)
(*                                                                            *)
(******************************************************************************)

(* Prove STRONG_RELAB_NIL:
   |- ∀rf. relab nil rf ~ nil
 *)
val STRONG_RELAB_NIL = store_thm (
   "STRONG_RELAB_NIL", ``!(rf :'a Relabeling). STRONG_EQUIV (relab nil rf) nil``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\(x :'a CCS) (y :'a CCS). (?rf'. (x = relab nil rf') /\ (y = nil))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      EXISTS_TAC ``rf :'a Relabeling`` \\
      REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC >> rpt STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = relab nil rf'``]
                            (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC RELAB_NIL_NO_TRANS,
        (* goal 2.2 *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = nil``]
                            (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC NIL_NO_TRANS ] ]);

(* Prove STRONG_RELAB_SUM:
   |- ∀E E' rf. (E + E')[rf] ~ E[rf] + E'[rf]:
 *)
val STRONG_RELAB_SUM = store_thm (
   "STRONG_RELAB_SUM",
  ``!E E' rf. STRONG_EQUIV (relab (sum E E') rf) (sum (relab E rf) (relab E' rf))``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [PROPERTY_STAR]
 >> rpt STRIP_TAC (* 2 sub-goals *)
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `E1` \\
      REWRITE_TAC [STRONG_EQUIV_REFL] \\
      IMP_RES_TAC TRANS_RELAB \\
      IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals here, sharing initial tacticals *)
      art [] >|
      [ (* goal 1.1 (of 2) *) MATCH_MP_TAC SUM1,
        (* goal 1.2 (of 2) *) MATCH_MP_TAC SUM2 ] \\
      MATCH_MP_TAC RELABELING >> art [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `E2` >> REWRITE_TAC [STRONG_EQUIV_REFL] \\
      IMP_RES_TAC TRANS_SUM \\(* 2 sub-goals here, sharing initial tacticals *)
      IMP_RES_TAC TRANS_RELAB >> art [] \\
      MATCH_MP_TAC RELABELING >|
      [ (* goal 2.1 (of 2) *) MATCH_MP_TAC SUM1,
        (* goal 2.2 (of 2) *) MATCH_MP_TAC SUM2 ] >> art [] ]);

(* Prove STRONG_RELAB_PREFIX:
   |- ∀u E labl. u..E[RELAB labl] ~ relabel (RELAB labl) u..(E[RELAB labl]):
 *)
val STRONG_RELAB_PREFIX = store_thm (
   "STRONG_RELAB_PREFIX",
       ``!(u :'a Action) E labl.
         STRONG_EQUIV (relab (prefix u E) (RELAB labl))
                      (prefix (relabel (RELAB labl) u) (relab E (RELAB labl)))``,
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/ (?u' E'. (x = relab (prefix u' E') (RELAB labl)) /\
                                   (y = prefix (relabel (RELAB labl) u')
                                               (relab E' (RELAB labl))))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC >> DISJ2_TAC \\
      EXISTS_TAC ``u :'a Action`` \\
      EXISTS_TAC ``E :'a CCS`` >> REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] >> BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                 (ASSUME ``TRANS E u E1``)) \\
        Q.EXISTS_TAC `E1` >> art [],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        Q.EXISTS_TAC `E1` >> REWRITE_TAC [] \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = relab (prefix u' E'') (RELAB labl)``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        IMP_RES_TAC TRANS_PREFIX >> art [PREFIX],
        (* goal 2.4 (of 4) *)
        Q.EXISTS_TAC `E2` >> REWRITE_TAC [] \\
        ASSUME_TAC (REWRITE_RULE
                        [ASSUME ``E' = prefix (relabel (RELAB labl) u')
                                              (relab E'' (RELAB labl))``]
                        (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC TRANS_PREFIX >> art [] \\
        MATCH_MP_TAC RELABELING >> REWRITE_TAC [PREFIX] ] ]);

(******************************************************************************)
(*                                                                            *)
(*        Laws for the recursion operator and strong equivalence              *)
(*                                                                            *)
(******************************************************************************)

(* The unfolding law R1 for strong equivalence: (Proposition 4.11 of [1, p.99])

   If A := P, then A ~ P

   where A is ‘rec X E’, P is ‘CCS_Subst E (rec X E) X’ (instead of just E)
 *)
Theorem STRONG_UNFOLDING :
    !X E. STRONG_EQUIV (rec X E) (CCS_Subst E (rec X E) X)
Proof
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y. (x = y) \/
              (?Y E'. (x = rec Y E') /\ (y = CCS_Subst E' (rec Y E') Y))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC >> DISJ2_TAC \\
      qexistsl_tac [‘X’, ‘E’] >> rw [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] >> BETA_TAC \\
      rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 2.1 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                  (ASSUME ``TRANS E u E1``)],
        (* goal 2.2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 2.3 (of 4) *)
        Q.EXISTS_TAC `E1` \\
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = rec Y E''``]
                                 (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_REC >> art [],
        (* goal 2.4 (of 4) *)
        Q.EXISTS_TAC `E2` \\
        ASM_REWRITE_TAC
         [REWRITE_RULE [ASSUME ``E' = CCS_Subst E'' (rec Y E'') Y``]
                       (ASSUME ``TRANS E' u E2``), TRANS_REC_EQ] ] ]
QED

(* Prove the theorem STRONG_PREF_REC_EQUIV:
   |- ∀u s v. u..rec s (v..u..var s) ~ rec s (u..v..var s):
 *)
Theorem STRONG_PREF_REC_EQUIV :
    !(u :'a Action) s v.
        STRONG_EQUIV (prefix u (rec s (prefix v (prefix u (var s)))))
                     (rec s (prefix u (prefix v (var s))))
Proof
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
     ``\x y.
         ?u' v' s'.
          (x = prefix u' (rec s' (prefix v' (prefix u' (var s'))))) /\
          (y = rec s' (prefix u' (prefix v' (var s')))) \/
          (x = rec s' (prefix v' (prefix u' (var s')))) /\
          (y = prefix v' (rec s' (prefix u' (prefix v' (var s')))))``
 >> CONJ_TAC (* 2 sub-goals *)
 >- (BETA_TAC >> take [`u`, `v`, `s`] >> REWRITE_TAC [])
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> BETA_TAC
 >> rpt STRIP_TAC (* 4 sub-goals *)
 >| [ (* goal 1 (of 4) *)
      ASSUME_TAC
          (REWRITE_RULE
               [ASSUME ``E = prefix u' (rec s' (prefix v' (prefix u' (var s'))))``]
               (ASSUME ``TRANS E u E1``)) >> fs [] \\
      IMP_RES_TAC TRANS_PREFIX \\
      EXISTS_TAC ``prefix (v' :'a Action) (rec s' (prefix u' (prefix v' (var s'))))`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        art [] >> MATCH_MP_TAC REC >> rw [CCS_Subst_def, PREFIX],
        (* goal 1.2 (of 2) *)
        take [`u'`, `v'`, `s'`] >> art [] ],
      (* goal 2 (of 4) *)
      ASSUME_TAC (REWRITE_RULE
                     [ASSUME ``E' = rec s' (prefix u' (prefix v' (var s')))``,
                      TRANS_REC_EQ, CCS_Subst_def]
                     (ASSUME ``TRANS E' u E2``)) >> fs [] \\
      IMP_RES_TAC TRANS_PREFIX \\
      EXISTS_TAC ``rec s' (prefix v' (prefix u (var s')))`` \\
      CONJ_TAC >| (* 2 sub-goals here, first one is easy *)
      [ (* goal 2.1 (of 2) *)
        art [PREFIX],
        (* goal 2.2 (of 2) *)
        take [`u`, `v'`, `s'`] \\
        art [REWRITE_RULE [ASSUME ``u' :'a Action = u``]
               (ASSUME ``E2 = prefix v' (rec s' (prefix u' (prefix v' (var s'))))``)] ],
      (* goal 3 (of 4) *)
      ASSUME_TAC (REWRITE_RULE
                   [ASSUME ``E = rec s' (prefix v' (prefix u' (var s')))``,
                    TRANS_REC_EQ, CCS_Subst_def]
                   (ASSUME ``TRANS E u E1``)) >> fs [] \\
      IMP_RES_TAC TRANS_PREFIX \\
      EXISTS_TAC ``rec s' (prefix u' (prefix v' (var s')))`` \\
      CONJ_TAC >| (* 2 sub-goals here, first one is easy *)
      [ (* goal 3.1 (of 2) *)
        art [PREFIX],
        (* goal 3.2 (of 2) *)
        take [`u'`, `v'`, `s'`] >> art [] ],
      (* goal 4 (of 4) *)
      ASSUME_TAC (REWRITE_RULE
                   [ASSUME ``E' = prefix v' (rec s' (prefix u' (prefix v' (var s'))))``]
                   (ASSUME ``TRANS E' u E2``)) >> fs [] \\
      IMP_RES_TAC TRANS_PREFIX \\
      EXISTS_TAC ``prefix (u' :'a Action)
                          (rec s' (prefix v' (prefix u' (var s'))))`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ (* goal 4.1 (of 2) *)
        art [] >> MATCH_MP_TAC REC >> rw [CCS_Subst_def, PREFIX],
        (* goal 4.2 (of 2) *)
        take [`u'`, `v'`, `s'`] >> art [] ] ]
QED

Theorem STRONG_UNFOLDING' = REWRITE_RULE [CCS_Subst] STRONG_UNFOLDING

(* Prove the theorem STRONG_REC_ACT2:
   |- ∀s u. rec s (u..u..var s) ~ rec s (u..var s)
 *)
Theorem STRONG_REC_ACT2 :
    !s u. STRONG_EQUIV (rec s (prefix u (prefix u (var s))))
                       (rec s (prefix u (var s)))
Proof
    rpt GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
      ``\x y.
         (?s' u'.
          (x = rec s' (prefix u' (prefix u' (var s')))) /\
          (y = rec s' (prefix u' (var s'))) \/
          (x = prefix u' (rec s' (prefix u' (prefix u' (var s'))))) /\
          (y = rec s' (prefix u' (var s'))))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      qexistsl_tac [‘s’, ‘u’] >> rw [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals *)
      [ (* goal 2.1 (of 4) *)
        ASSUME_TAC
          (REWRITE_RULE [ASSUME ``E = rec s' (prefix u' (prefix u' (var s')))``,
                         TRANS_REC_EQ, CCS_Subst_def]
                        (ASSUME ``TRANS E u E1``)) >> fs [] \\
        IMP_RES_TAC TRANS_PREFIX >> EXISTS_TAC ``E' :'a CCS`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          art [] >> MATCH_MP_TAC REC >> rw [CCS_Subst_def, PREFIX],
          (* goal 2.1.2 (of 2) *)
          qexistsl_tac [‘s'’, ‘u'’] >> art [] ],
        (* goal 2.2 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = rec s'(prefix u'(var s'))``,
                                  TRANS_REC_EQ, CCS_Subst_def]
                                 (ASSUME ``TRANS E' u E2``)) >> fs [] \\
        IMP_RES_TAC TRANS_PREFIX \\
        EXISTS_TAC ``prefix (u' :'a Action) E`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          art [] >> MATCH_MP_TAC REC >> rw [CCS_Subst_def, PREFIX],
          (* goal 2.2.2 (of 2) *)
          qexistsl_tac [‘s'’, ‘u'’] >> art [] ],
        (* goal 2.3 (of 4) *)
        ASSUME_TAC
          (REWRITE_RULE
               [ASSUME ``E = prefix u' (rec s' (prefix u' (prefix u' (var s'))))``]
               (ASSUME ``TRANS E u E1``)) >> fs [] \\
        IMP_RES_TAC TRANS_PREFIX >> EXISTS_TAC ``E' :'a CCS`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.3.1 (of 2) *)
          art [] >> MATCH_MP_TAC REC >> rw [CCS_Subst_def, PREFIX],
          (* goal 2.3.2 (of 2) *)
          qexistsl_tac [‘s'’, ‘u'’] >> art [] ],
        (* goal 2.4 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E' = rec s' (prefix u' (var s'))``,
                                  TRANS_REC_EQ, CCS_Subst_def]
                                 (ASSUME ``TRANS E' u E2``)) >> fs [] \\
        IMP_RES_TAC TRANS_PREFIX \\
        EXISTS_TAC ``rec s' (prefix u' (prefix u' (var s')))`` \\
        CONJ_TAC >| (* 2 sub-goals here, first one is easy *)
        [ (* goal 2.4.1 (of 2) *)
          art [PREFIX],
          (* goal 2.4.2 (of 2) *)
          qexistsl_tac [‘s'’, ‘u'’] >> art [] ] ] ]
QED

(******************************************************************************)
(*                                                                            *)
(*       The strong laws for the redundant recursion operators                *)
(*                                                                            *)
(******************************************************************************)

Theorem STRONG_EQUIV_REC_ELIM :
    !X E. X # E ==> STRONG_EQUIV (rec X E) E
Proof
    rw [Once PROPERTY_STAR]
 >| [ (* goal 1 (of 2) *)
      fs [TRANS_REC_EQ, CCS_Subst] \\
      Know ‘[rec X E/X] E = E’
      >- (MATCH_MP_TAC lemma14b >> art []) \\
      DISCH_THEN (fs o wrap) \\
      Q.EXISTS_TAC ‘E1’ >> rw [],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC ‘E2’ >> rw [TRANS_REC_EQ, CCS_Subst] \\
      Know ‘[rec X E/X] E = E’
      >- (MATCH_MP_TAC lemma14b >> art []) >> rw [] ]
QED

Theorem STRONG_EQUIV_REC_REC_ELIM :
    !X E. STRONG_EQUIV (rec X (rec X E)) (rec X E)
Proof
    rpt GEN_TAC
 >> MATCH_MP_TAC STRONG_EQUIV_REC_ELIM >> rw []
QED

(******************************************************************************)
(*                                                                            *)
(*       The strong laws for the parallel operator in the general form        *)
(*                                                                            *)
(******************************************************************************)

val Is_Prefix_def = Define `
    Is_Prefix E = (?(u :'a Action) E'. (E = prefix u E')) `;

val PREF_IS_PREFIX = store_thm (
   "PREF_IS_PREFIX", ``!(u :'a Action) E. Is_Prefix (prefix u E)``,
    rpt GEN_TAC
 >> REWRITE_TAC [Is_Prefix_def]
 >> EXISTS_TAC ``u :'a Action``
 >> EXISTS_TAC ``E :'a CCS``
 >> REWRITE_TAC []);

(* --------------------------------------------------------------------------- *)
(* Define the notation used for indexed summations:                            *)
(* given a function f: num->CCS and an index n:num, the primitive recursive    *)
(* function CCS_SIGMA is such that SIGMA f n denotes the summation             *)
(* (f 0) + (f 1) + ... + (f n).                                                *)
(* --------------------------------------------------------------------------- *)

val CCS_SIGMA_def = Define `
   (CCS_SIGMA (f :num -> 'a CCS) 0 = f 0) /\
   (CCS_SIGMA f (SUC n) = sum (CCS_SIGMA f n) (f (SUC n))) `;

val _ = overload_on ("SIGMA", ``CCS_SIGMA``);

(*
 SIGMA_BASE =
   |- ∀f. SIGMA f 0 = f 0
 SIGMA_INDUCT =
   |- ∀f n. SIGMA f (SUC n) = SIGMA f n + f (SUC n)
 *)
val [SIGMA_BASE, SIGMA_INDUCT] =
    map (fn (s, thm) => save_thm (s, thm))
        (combine (["SIGMA_BASE", "SIGMA_INDUCT"], CONJUNCTS CCS_SIGMA_def));

(* --------------------------------------------------------------------------- *)
(* Define the notation used for indexed compositions (par):                    *)
(* given a function f: num->CCS and an index n:num, the primitive recursive    *)
(* function CCS_COMP is such that SIGMA f n denotes the composition            *)
(* (f 0) | (f 1) | ... | (f n).                                                *)
(* --------------------------------------------------------------------------- *)

val CCS_COMP_def = Define `
   (CCS_COMP (f :num -> 'a CCS) 0 = f 0) /\
   (CCS_COMP f (SUC n) = par (CCS_COMP f n) (f (SUC n))) `;

val _ = overload_on ("PI", ``CCS_COMP``);

(*
val COMP_BASE =
   |- ∀f. PI f 0 = f 0
val COMP_INDUCT =
   |- ∀f n. PI f (SUC n) = PI f n || f (SUC n)
 *)
val [COMP_BASE, COMP_INDUCT] =
    map (fn (s, thm) => save_thm (s, thm))
        (combine (["COMP_BASE", "COMP_INDUCT"], CONJUNCTS CCS_COMP_def));

(* --------------------------------------------------------------------------- *)
(* Define the functions to compute the summation of the synchronizing summands *)
(* of two summations of prefixed processes in parallel.                        *)
(* SYNC computes the synchronizations between a summand u.P and the summation  *)
(* f: num -> 'a CCS representing the other process in parallel.          *)
(* --------------------------------------------------------------------------- *)

val SYNC_def = Define `
   (SYNC (u :'a Action) P f 0 =
        (if ((u = tau) \/ (PREF_ACT (f 0) = tau))
          then nil
          else (if (LABEL u = COMPL (LABEL (PREF_ACT (f 0))))
                 then (prefix tau (par P (PREF_PROC (f 0))))
                 else nil))) /\
   (SYNC u P f (SUC n) =
        (if ((u = tau) \/ (PREF_ACT (f (SUC n)) = tau))
          then (SYNC u P f n)
          else (if (LABEL u = COMPL (LABEL (PREF_ACT (f (SUC n)))))
                  then (sum (prefix tau (par P (PREF_PROC (f (SUC n))))) (SYNC u P f n))
                  else (SYNC u P f n))))`;

val [SYNC_BASE, SYNC_INDUCT] =
    map (fn (s,thm) => save_thm (s, thm))
        (combine (["SYNC_BASE", "SYNC_INDUCT"], CONJ_LIST 2 SYNC_def));

(* --------------------------------------------------------------------------- *)
(* ALL_SYNC computes the summation of all possible synchronizations between    *)
(* two process summations f, f': num -> CCS of length n, m respectively.       *)
(* This is done using the function SYNC.                                       *)
(* --------------------------------------------------------------------------- *)

val ALL_SYNC_def = Define `
   (ALL_SYNC f 0 f' m = SYNC (PREF_ACT (f 0)) (PREF_PROC (f 0)) f' m) /\
   (ALL_SYNC f (SUC n) f' m =
         sum (ALL_SYNC f n f' m)
             (SYNC (PREF_ACT (f (SUC n))) (PREF_PROC (f (SUC n))) f' m)) `;

val [ALL_SYNC_BASE, ALL_SYNC_INDUCT] =
    map (fn (s,thm) => save_thm (s, thm))
        (combine (["ALL_SYNC_BASE", "ALL_SYNC_INDUCT"], CONJUNCTS ALL_SYNC_def));

(* LESS_SUC_LESS_EQ':
 |- !m n. m < (SUC n) = m <= n
 *)
val LESS_SUC_LESS_EQ' = Q.prove (
   `!m n. m < SUC n <=> m <= n`,
    REWRITE_TAC [LESS_EQ, LESS_EQ_MONO]);

(* |- ∀n m. m < SUC n ⇒ m ≤ n
 *)
val LESS_SUC_LESS_EQ = EQ_IMP_LR LESS_SUC_LESS_EQ';

(* LESS_EQ_ZERO_EQ:
 |- !n. n <= 0 ==> (n = 0)
 *)
val LESS_EQ_ZERO_EQ = EQ_IMP_LR LESS_EQ_0;

(* LESS_EQ_LESS_EQ_SUC:
 |- !m n. m <= n ==> m <= (SUC n)
 *)
val LESS_EQ_LESS_EQ_SUC = Q.prove (
   `!m n. m <= n ==> m <= (SUC n)`,
    rpt STRIP_TAC
 >> IMP_RES_TAC LESS_EQ_IMP_LESS_SUC
 >> IMP_RES_TAC LESS_IMP_LESS_OR_EQ);

Theorem SIGMA_TRANS_THM_EQ :
    !n f (u :'a Action) E. TRANS (SIGMA f n) u E <=> ?k. k <= n /\ TRANS (f k) u E
Proof
    Induct (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      rpt GEN_TAC \\
      REWRITE_TAC [LESS_EQ_0, SIGMA_BASE] \\
      EQ_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        DISCH_TAC \\
        EXISTS_TAC ``0: num``  >> art [],
        (* goal 1.2 (of 2) *)
        STRIP_TAC \\
        REWRITE_TAC [REWRITE_RULE [ASSUME ``k = (0 :num)``]
                        (ASSUME ``TRANS ((f: num -> 'a CCS) k) u E``)] ],
      (* goal 2 (of 2) *)
      rpt GEN_TAC \\
      REWRITE_TAC [SIGMA_INDUCT, TRANS_SUM_EQ] \\
      EQ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        STRIP_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          STRIP_ASSUME_TAC
                (MATCH_MP (EQ_IMP_LR (ASSUME ``!f u E. TRANS (SIGMA f n) u E =
                                                (?k. k <= n /\ TRANS (f k) u E)``))
                          (ASSUME ``TRANS (SIGMA f n) u E``)) \\
          IMP_RES_TAC LESS_EQ_LESS_EQ_SUC \\
          EXISTS_TAC ``k: num`` >> art [],
          (* goal 2.1.2 (of 2) *)
          EXISTS_TAC ``SUC n`` >> art [LESS_EQ_REFL] ],
        (* goal 2.2 (of 2) *)
        STRIP_TAC \\
        IMP_RES_TAC LESS_OR_EQ >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          DISJ1_TAC \\
          PURE_ONCE_ASM_REWRITE_TAC [] \\
          EXISTS_TAC ``k: num`` \\
          IMP_RES_TAC LESS_SUC_LESS_EQ >> art [],
          (* goal 2.2.2 (of 2) *)
          DISJ2_TAC \\
          REWRITE_TAC [REWRITE_RULE [ASSUME ``k = SUC n``]
                        (ASSUME ``TRANS ((f: num -> 'a CCS) k) u E``)] ] ] ]
QED

(* SIGMA_TRANS_THM =
 |- ∀u n f E. SIGMA f n --u-> E ⇒ ∃k. k ≤ n ∧ f k --u-> E
 *)
val SIGMA_TRANS_THM = save_thm (
   "SIGMA_TRANS_THM", EQ_IMP_LR SIGMA_TRANS_THM_EQ);

Theorem SYNC_TRANS_THM_EQ :
    !m (u :'a Action) P f v Q. TRANS (SYNC u P f m) v Q <=>
          ?j l. j <= m /\
                (u = label l) /\ (PREF_ACT (f j) = label (COMPL l)) /\
                (v = tau) /\ (Q = par P (PREF_PROC (f j)))
Proof
    Induct_on `m` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      rpt GEN_TAC \\
      REWRITE_TAC [LESS_EQ_0, SYNC_BASE] \\
      COND_CASES_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        REWRITE_TAC [NIL_NO_TRANS] \\
        STRIP_TAC \\
        DISJ_CASES_TAC
          (ASSUME ``((u :'a Action) = tau) \/
                    (PREF_ACT ((f: num -> 'a CCS) 0) = tau)``)
        >| (* 2 sub-goals here *)
        [ (* goal 1.1.1 (of 2) *)
          ASSUME_TAC (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                                   (ASSUME ``(u :'a Action) = label l``)) \\
          IMP_RES_TAC Action_distinct,
          (* goal 1.1.2 (of 2) *)
          CHECK_ASSUME_TAC
            (REWRITE_RULE [ASSUME ``j = (0 :num)``,
                           ASSUME ``PREF_ACT ((f: num -> 'a CCS) 0) = tau``,
                           Action_distinct]
                (ASSUME ``PREF_ACT ((f: num -> 'a CCS) j) = label (COMPL l)``)) ],
        (* goal 1.2 (of 2) *)
        STRIP_ASSUME_TAC
         (REWRITE_RULE [DE_MORGAN_THM]
                       (ASSUME ``~(((u :'a Action) = tau) \/
                                 (PREF_ACT ((f: num -> 'a CCS) 0) = tau))``)) \\
        IMP_RES_TAC Action_no_tau_is_Label >> art [LABEL_def] \\
        COND_CASES_TAC >| (* 2 sub-goals here *)
        [ (* goal 1.2.1 (of 2) *)
          EQ_TAC >| (* 2 sub-goals here *)
          [ (* goal 1.2.1.1 (of 2) *)
            DISCH_TAC \\
            IMP_RES_TAC TRANS_PREFIX \\
            EXISTS_TAC ``0: num`` \\
            EXISTS_TAC ``x' :'a Label`` >> art [COMPL_COMPL_LAB],
            (* goal 1.2.1.2 (of 2) *)
            STRIP_TAC >> art [PREFIX] ],
          (* goal 1.2.2 (of 2) *)
          REWRITE_TAC [NIL_NO_TRANS] \\
          STRIP_TAC \\
          ASSUME_TAC
            (REWRITE_RULE [ASSUME ``j = (0 :num)``,
                           ASSUME ``PREF_ACT ((f: num -> 'a CCS) 0) = label x``]
                (ASSUME ``PREF_ACT ((f: num -> 'a CCS) j) = label (COMPL l)``)) \\
          IMP_RES_TAC Action_11 \\
          CHECK_ASSUME_TAC
                (REWRITE_RULE [ ASSUME ``x = COMPL (l :'a Label)``, COMPL_COMPL_LAB,
                                ASSUME ``x' :'a Label = l`` ]
                        (ASSUME ``~(x' = COMPL (x :'a Label))``)) ] ],
      (* goal 2 (of 2), inductive case *)
      rpt GEN_TAC \\
      PURE_ONCE_REWRITE_TAC [SYNC_INDUCT] \\
      COND_CASES_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        EQ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          DISCH_TAC \\
          STRIP_ASSUME_TAC
              (MATCH_MP
                (EQ_IMP_LR (ASSUME ``!(u :'a Action) P f v Q.
                                TRANS (SYNC u P f m) v Q =
                                (?j l.
                                  j <= m /\ (u = label l) /\
                                  (PREF_ACT (f j) = label (COMPL l)) /\
                                  (v = tau) /\ (Q = par P (PREF_PROC (f j))))``))
                (ASSUME ``TRANS (SYNC u P f m) v Q``)) \\
          IMP_RES_TAC LESS_EQ_LESS_EQ_SUC \\
          EXISTS_TAC ``j: num`` \\
          Q.EXISTS_TAC `l` >> art [],
          (* goal 2.1.2 (of 2) *)
          STRIP_TAC \\
          DISJ_CASES_TAC (ASSUME ``((u :'a Action) = tau) \/
                                   (PREF_ACT ((f :num -> 'a CCS) (SUC m)) = tau)``)
          >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            CHECK_ASSUME_TAC (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``, Action_distinct]
                                           (ASSUME ``(u :'a Action) = label l``)),
            (* goal 2.1.2.2 (of 2) *)
            art [] \\
            IMP_RES_TAC LESS_OR_EQ >| (* 2 sub-goals here *)
            [ (* goal 2.1.2.2.1 (of 2) *)
              IMP_RES_TAC LESS_SUC_LESS_EQ \\
              EXISTS_TAC ``j: num`` \\
              Q.EXISTS_TAC `l` \\
              art [],
              (* goal 2.1.2.2.2 (of 2) *)
              CHECK_ASSUME_TAC
                (REWRITE_RULE
                    [ASSUME ``j = SUC m``,
                     ASSUME ``PREF_ACT ((f: num -> 'a CCS) (SUC m)) = tau``,
                     Action_distinct]
                  (ASSUME ``PREF_ACT ((f: num -> 'a CCS) j) = label (COMPL l)``)) ]]],
        (* goal 2.2 (of 2) *)
        STRIP_ASSUME_TAC
            (REWRITE_RULE [DE_MORGAN_THM]
                (ASSUME ``~(((u :'a Action) = tau) \/
                            (PREF_ACT ((f : num -> 'a CCS) (SUC m)) = tau))``)) \\
        IMP_RES_TAC Action_no_tau_is_Label \\
        art [LABEL_def] \\
        COND_CASES_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          EQ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.2.1.1 (of 2) *)
            DISCH_TAC \\
            IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.1.1 (of 2) *)
              IMP_RES_TAC TRANS_PREFIX \\
              take [`SUC m`, `x'`] \\
              art [LESS_EQ_REFL, COMPL_COMPL_LAB],
              (* goal 2.2.1.1.2 (of 2) *)
              STRIP_ASSUME_TAC
               (MATCH_MP
                 (EQ_IMP_LR (ASSUME ``!(u :'a Action) P f v Q.
                                  TRANS (SYNC u P f m) v Q =
                                  (?j l.
                                    j <= m /\ (u = label l) /\
                                    (PREF_ACT (f j) = label (COMPL l)) /\
                                    (v = tau) /\ (Q = par P (PREF_PROC (f j))))``))
                 (ASSUME ``TRANS (SYNC (label x') P f m) v Q``)) \\
              IMP_RES_TAC LESS_EQ_LESS_EQ_SUC \\
              take [`j`, `l`] \\
              art [] ],
            (* goal 2.2.1.2 (of 2) *)
            STRIP_TAC \\
            IMP_RES_TAC LESS_OR_EQ >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.2.1 (of 2) *)
              MATCH_MP_TAC SUM2 \\
              PURE_ONCE_ASM_REWRITE_TAC [] \\
              IMP_RES_TAC LESS_SUC_LESS_EQ \\
              take [`j`, `l`] \\
              art [],
              (* goal 2.2.1.2.2 (of 2) *)
              MATCH_MP_TAC SUM1 \\
              art
                [REWRITE_RULE [ASSUME ``j = SUC m``]
                   (ASSUME ``Q = par P (PREF_PROC ((f: num -> 'a CCS) j))``),
                 PREFIX] ] ],
          (* goal 2.2.2 (of 2) *)
          art [] \\
          EQ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.2.2.1 (of 2) *)
            STRIP_TAC \\
            IMP_RES_TAC LESS_EQ_LESS_EQ_SUC \\
            take [`j`, `l`] >> art [],
            (* goal 2.2.2.2 (of 2) *)
            STRIP_TAC \\
            IMP_RES_TAC LESS_OR_EQ >| (* 2 sub-goals here *)
            [ (* goal 2.2.2.2.1 (of 2) *)
              IMP_RES_TAC LESS_SUC_LESS_EQ \\
              take [`j`, `l`] \\
              art [],
              (* goal 2.2.2.2.2 (of 2) *)
              ASSUME_TAC
                (REWRITE_RULE
                  [ASSUME ``j = SUC m``,
                   ASSUME ``PREF_ACT ((f :num -> 'a CCS) (SUC m)) = label x``]
                  (ASSUME ``PREF_ACT ((f: num -> 'a CCS) j) = label (COMPL l)``)) \\
              IMP_RES_TAC Action_11 \\
              CHECK_ASSUME_TAC
                (REWRITE_RULE [ASSUME ``x = COMPL (l :'a Label)``, COMPL_COMPL_LAB,
                               ASSUME ``x' :'a Label = l``]
                              (ASSUME ``~(x' = COMPL (x :'a Label))``)) ] ] ] ] ]
QED

(* SYNC_TRANS_THM =
 |- ∀v u m f Q P.
     SYNC u P f m --v-> Q ⇒
     ∃j l.
       j ≤ m ∧ (u = label l) ∧ (PREF_ACT (f j) = label (COMPL l)) ∧
       (v = τ) ∧ (Q = P || PREF_PROC (f j))
 *)
val SYNC_TRANS_THM = save_thm (
   "SYNC_TRANS_THM", EQ_IMP_LR SYNC_TRANS_THM_EQ);

val ALL_SYNC_TRANS_THM_EQ = store_thm (
   "ALL_SYNC_TRANS_THM_EQ",
  ``!n m f f' u E.
         TRANS (ALL_SYNC f n f' m) u E =
         (?k k' l.
           k <= n /\ k' <= m /\
           (PREF_ACT (f k) = label l) /\
           (PREF_ACT (f' k') = label (COMPL l)) /\
           (u = tau) /\
           (E = par (PREF_PROC (f k)) (PREF_PROC (f' k'))))``,
    Induct_on `n` (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      rpt GEN_TAC \\
      REWRITE_TAC [LESS_EQ_0, ALL_SYNC_BASE, SYNC_TRANS_THM_EQ] \\
      EQ_TAC >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        STRIP_TAC \\
        take [`0`, `j`, `l`]  >> art [],
        (* goal 1.2 (of 2) *)
        STRIP_TAC \\
        ASSUME_TAC
          (REWRITE_RULE [ASSUME ``k = (0 :num)``]
                (ASSUME ``PREF_ACT ((f: num -> 'a CCS) k) = label l``)) \\
        ASSUME_TAC
          (REWRITE_RULE [ASSUME ``k = (0 :num)``]
                (ASSUME ``E = par (PREF_PROC ((f: num -> 'a CCS) k))
                                  (PREF_PROC ((f': num -> 'a CCS) k'))``)) \\
        take [`k'`, `l`]  >> art [] ],
      (* goal 2 (of 2), inductive case *)
      rpt GEN_TAC \\
      REWRITE_TAC [ALL_SYNC_INDUCT, TRANS_SUM_EQ] \\
      EQ_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        STRIP_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          STRIP_ASSUME_TAC
           (MATCH_MP
             (EQ_IMP_LR
               (ASSUME ``!m f f' u E.
                      TRANS (ALL_SYNC f n f' m) u E =
                      (?k k' l.
                        k <= n /\ k' <= m /\
                        (PREF_ACT (f k) = label l) /\
                        (PREF_ACT (f' k') = label (COMPL l)) /\
                        (u = tau) /\
                        (E = par (PREF_PROC (f k)) (PREF_PROC (f' k'))))``))
             (ASSUME ``TRANS (ALL_SYNC f n f' m) u E``)) \\
          IMP_RES_TAC LESS_EQ_LESS_EQ_SUC \\
          take [`k`, `k'`, `l`] >> art [],
          (* goal 2.1.2 (of 2) *)
          IMP_RES_TAC SYNC_TRANS_THM \\
          take [`SUC n`, `j`, `l`] >> art [LESS_EQ_REFL] ],
        (* goal 2.2 (of 2) *)
        STRIP_TAC \\
        IMP_RES_TAC (Q.SPECL [`k`, `SUC n`] LESS_OR_EQ) >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          DISJ1_TAC \\
          PURE_ONCE_ASM_REWRITE_TAC [] \\
          IMP_RES_TAC LESS_SUC_LESS_EQ \\
          take [`k`, `k'`, `l`] >> art [],
          (* goal 2.2.2 (of 2) *)
          DISJ2_TAC >> art [SYNC_TRANS_THM_EQ] \\
          ASSUME_TAC
            (REWRITE_RULE [ASSUME ``k = SUC n``]
                (ASSUME ``PREF_ACT ((f: num -> 'a CCS) k) = label l``)) \\
          ASSUME_TAC
            (REWRITE_RULE [ASSUME ``k = SUC n``]
                (ASSUME ``E = par (PREF_PROC ((f: num -> 'a CCS) k))
                                  (PREF_PROC ((f': num -> 'a CCS) k'))``)) \\
          take [`k'`, `l`] >> art [] ] ] ]);

(* ALL_SYNC_TRANS_THM =
 |- ∀u n m f' f E.
     ALL_SYNC f n f' m --u-> E ⇒
     ∃k k' l.
       k ≤ n ∧ k' ≤ m ∧ (PREF_ACT (f k) = label l) ∧
       (PREF_ACT (f' k') = label (COMPL l)) ∧ (u = τ) ∧
       (E = PREF_PROC (f k) || PREF_PROC (f' k')):
 *)
val ALL_SYNC_TRANS_THM = save_thm (
   "ALL_SYNC_TRANS_THM",
    EQ_IMP_LR ALL_SYNC_TRANS_THM_EQ);

(* The expansion law for strong equivalence:
 |- ∀f n f' m.
     (∀i. i ≤ n ⇒ Is_Prefix (f i)) ∧ (∀j. j ≤ m ⇒ Is_Prefix (f' j)) ⇒
     SIGMA f n || SIGMA f' m
     ∼
     SIGMA (λi. PREF_ACT (f i)..(PREF_PROC (f i) || SIGMA f' m)) n +
     SIGMA (λj. PREF_ACT (f' j)..(SIGMA f n || PREF_PROC (f' j))) m +
     ALL_SYNC f n f' m:
 *)
val STRONG_EXPANSION_LAW = store_thm (
   "STRONG_EXPANSION_LAW",
      ``!f n f' m.
         (!i. i <= n ==> Is_Prefix (f i)) /\ (!j. j <= m ==> Is_Prefix (f' j)) ==>
         STRONG_EQUIV
         (par (SIGMA f n) (SIGMA f' m))
         (sum
          (sum
           (SIGMA (\i. prefix (PREF_ACT (f i))
                              (par (PREF_PROC (f i)) (SIGMA f' m))) n)
           (SIGMA (\j. prefix (PREF_ACT (f' j))
                              (par (SIGMA f n) (PREF_PROC (f' j)))) m))
          (ALL_SYNC f n f' m))``,
    rpt STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
      ``\x y.
        (x = y) \/
        (?f1 n1 f2 m2.
         (!i. i <= n1 ==> Is_Prefix(f1 i)) /\
         (!j. j <= m2 ==> Is_Prefix(f2 j)) /\
         (x = par (SIGMA f1 n1) (SIGMA f2 m2)) /\
         (y = sum
              (sum
               (SIGMA (\i. prefix (PREF_ACT (f1 i))
                                  (par (PREF_PROC (f1 i)) (SIGMA f2 m2))) n1)
               (SIGMA (\j. prefix (PREF_ACT(f2 j))
                                  (par (SIGMA f1 n1) (PREF_PROC (f2 j)))) m2))
              (ALL_SYNC f1 n1 f2 m2)))``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC >> DISJ2_TAC \\
      take [`f`, `n`, `f'`, `m`] >> art [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC >> rpt STRIP_TAC >| (* 4 sub-goals here *)
      [ (* goal 1 (of 4) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E :'a CCS = E'``]
                                 (ASSUME ``TRANS E u E1``)) \\
        Q.EXISTS_TAC `E1`  >> art [],
        (* goal 2 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [],
        (* goal 3 (of 4) *)
        Q.EXISTS_TAC `E1`  >> art [] \\
        ASSUME_TAC
         (REWRITE_RULE [ASSUME ``E = par (SIGMA f1 n1) (SIGMA f2 m2)``]
                       (ASSUME ``TRANS E u E1``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 3.1 (of 3) *)
          MATCH_MP_TAC SUM1 \\
          MATCH_MP_TAC SUM1 \\
          PURE_ONCE_REWRITE_TAC [SIGMA_TRANS_THM_EQ] \\
          BETA_TAC \\
          IMP_RES_TAC SIGMA_TRANS_THM \\
          EXISTS_TAC ``k: num`` \\
          STRIP_ASSUME_TAC
            (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(i: num). i <= n1 ==> Is_Prefix (f1 i)``)
                          (ASSUME ``(k: num) <= n1``))) \\
          ASSUME_TAC
            (REWRITE_RULE [ASSUME ``(f1: num -> 'a CCS) k = prefix u' E''``]
                          (ASSUME ``TRANS ((f1: num -> 'a CCS) k) u E1'``)) \\
          IMP_RES_TAC TRANS_PREFIX >> art [PREF_ACT_def, PREF_PROC_def, PREFIX],
          (* goal 3.2 (of 3) *)
          MATCH_MP_TAC SUM1 \\
          MATCH_MP_TAC SUM2 \\
          PURE_ONCE_REWRITE_TAC [SIGMA_TRANS_THM_EQ] \\
          BETA_TAC \\
          IMP_RES_TAC SIGMA_TRANS_THM \\
          EXISTS_TAC ``k: num`` \\
          STRIP_ASSUME_TAC
            (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(j :num). j <= m2 ==> Is_Prefix (f2 j)``)
                          (ASSUME ``(k :num) <= m2``))) \\
          ASSUME_TAC
            (REWRITE_RULE [ASSUME ``(f2: num -> 'a CCS) k = prefix u' E''``]
                (ASSUME ``TRANS ((f2: num -> 'a CCS) k) u E1'``)) \\
          IMP_RES_TAC TRANS_PREFIX >> art [PREF_ACT_def, PREF_PROC_def, PREFIX],
          (* goal 3.3 (of 3) *)
          MATCH_MP_TAC SUM2 >> art [ALL_SYNC_TRANS_THM_EQ] \\
          IMP_RES_TAC SIGMA_TRANS_THM \\
          STRIP_ASSUME_TAC
            (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(j :num). j <= m2 ==> Is_Prefix (f2 j)``)
                                    (ASSUME ``(k :num) <= m2``))) \\
          STRIP_ASSUME_TAC
            (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(i :num). i <= n1 ==> Is_Prefix (f1 i)``)
                          (ASSUME ``(k' :num) <= n1``))) \\
          ASSUME_TAC
            (REWRITE_RULE [ASSUME ``(f2: num -> 'a CCS) k = prefix u' E''``]
                (ASSUME ``TRANS ((f2: num -> 'a CCS) k) (label (COMPL l)) E2``)) \\
          ASSUME_TAC
            (REWRITE_RULE [ASSUME ``(f1: num -> 'a CCS) k' = prefix u'' E'''``]
                (ASSUME ``TRANS ((f1: num -> 'a CCS) k') (label l) E1'``)) \\
          IMP_RES_TAC TRANS_PREFIX \\
          take [`k'`, `k`, `l`] >> art [PREF_ACT_def, PREF_PROC_def] ],
        (* goal 4 (of 4) *)
        Q.EXISTS_TAC `E2` >> art [] \\
        ASSUME_TAC
         (REWRITE_RULE
          [ASSUME ``E' = sum (sum (SIGMA
                                   (\i:num. prefix (PREF_ACT (f1 i))
                                              (par (PREF_PROC (f1 i)) (SIGMA f2 m2))) n1)
                                  (SIGMA
                                   (\j:num. prefix (PREF_ACT (f2 j))
                                              (par (SIGMA f1 n1) (PREF_PROC (f2 j)))) m2))
                             (ALL_SYNC f1 n1 f2 m2)``]
          (ASSUME ``TRANS E' u E2``)) \\
        IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
        [ (* goal 4.1 (of 2) *)
          IMP_RES_TAC
            (SPECL [``SIGMA (\i:num. prefix (PREF_ACT (f1 i))
                                       (par (PREF_PROC (f1 i)) (SIGMA f2 m2))) n1``,
                    ``SIGMA (\j:num. prefix (PREF_ACT (f2 j))
                                       (par (SIGMA f1 n1) (PREF_PROC (f2 j)))) m2``,
                    ``u :'a Action``,
                    ``E2 :'a CCS``] TRANS_SUM) >| (* 2 subgoals *)
          [ (* goal 4.1.1 (of 2) *)
            IMP_RES_TAC SIGMA_TRANS_THM \\
            ASSUME_TAC
             (BETA_RULE
               (ASSUME ``TRANS ((\i: num. prefix (PREF_ACT (f1 i))
                                            (par (PREF_PROC (f1 i)) (SIGMA f2 m2))) k)
                               u E2``)) \\
            IMP_RES_TAC TRANS_PREFIX \\
            STRIP_ASSUME_TAC
             (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(i: num). i <= n1 ==> Is_Prefix (f1 i)``)
                          (ASSUME ``(k: num) <= n1``))) >> art [] \\
            MATCH_MP_TAC PAR1 \\
            REWRITE_TAC [SIGMA_TRANS_THM_EQ] \\
            EXISTS_TAC ``k: num`` \\
            ASM_REWRITE_TAC [PREF_ACT_def, PREF_PROC_def, PREFIX],
            (* goal 4.1.2 (of 2) *)
            IMP_RES_TAC SIGMA_TRANS_THM \\
            ASSUME_TAC
             (BETA_RULE
               (ASSUME ``TRANS ((\j: num. prefix (PREF_ACT (f2 j))
                                            (par (SIGMA f1 n1) (PREF_PROC (f2 j)))) k)
                               u E2``)) \\
            IMP_RES_TAC TRANS_PREFIX \\
            STRIP_ASSUME_TAC
             (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(j :num). j <= m2 ==> Is_Prefix (f2 j)``)
                          (ASSUME ``(k :num) <= m2``))) >> art [] \\
            MATCH_MP_TAC PAR2 \\
            REWRITE_TAC [SIGMA_TRANS_THM_EQ] \\
            EXISTS_TAC ``k: num`` \\
            ASM_REWRITE_TAC [PREF_ACT_def, PREF_PROC_def, PREFIX] ],
          (* goal 4.2 (of 2) *)
          IMP_RES_TAC ALL_SYNC_TRANS_THM >> art [] \\
          MATCH_MP_TAC PAR3 \\
          Q.EXISTS_TAC `l` \\
          REWRITE_TAC [SIGMA_TRANS_THM_EQ] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 4.2.1 (of 2) *)
            EXISTS_TAC ``k: num`` \\
            STRIP_ASSUME_TAC
             (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(i: num). i <= n1 ==> Is_Prefix (f1 i)``)
                          (ASSUME ``(k :num) <= n1``))) \\
            ASSUME_TAC
             (REWRITE_RULE [ASSUME ``(f1: num -> 'a CCS) k = prefix u' E''``,
                            PREF_ACT_def]
                (ASSUME ``PREF_ACT ((f1: num -> 'a CCS) k) = label l``)) \\
            ASM_REWRITE_TAC [PREF_PROC_def, PREFIX],
            (* goal 4.2.2 (of 2) *)
            EXISTS_TAC ``k': num`` \\
            STRIP_ASSUME_TAC
             (REWRITE_RULE [Is_Prefix_def]
                (MATCH_MP (ASSUME ``!(j :num). j <= m2 ==> Is_Prefix (f2 j)``)
                          (ASSUME ``(k' :num) <= m2``))) \\
            ASSUME_TAC
             (REWRITE_RULE [ASSUME ``(f2: num -> 'a CCS) k' = prefix u' E''``,
                            PREF_ACT_def]
                (ASSUME ``PREF_ACT ((f2: num -> 'a CCS) k') = label (COMPL l)``)) \\
            ASM_REWRITE_TAC [PREF_PROC_def, PREFIX] ] ] ] ]);

val _ = export_theory ();
val _ = html_theory "StrongLaws";

(* Bibliography:

 [1] Milner, Robin. Communication and concurrency. Prentice hall, 1989.
 [2] Gorrieri, R., Versari, C.: Introduction to Concurrency Theory. Springer (2015).

 *)
