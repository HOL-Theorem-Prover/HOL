(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open CCSLib CCSTheory StrongEQTheory StrongEQLib StrongLawsTheory
     WeakEQTheory WeakEQLib WeakLawsTheory ObsCongrTheory ObsCongrLib;

val _ = new_theory "ObsCongrLaws";

(******************************************************************************)
(*                                                                            *)
(*         Basic laws of observation congruence for binary summation          *)
(*               through strong equivalence                                   *)
(*                                                                            *)
(******************************************************************************)

(* Prove OBS_SUM_IDENT_R: |- !E. OBS_CONGR (sum E nil) E *)
val OBS_SUM_IDENT_R = save_thm (
   "OBS_SUM_IDENT_R",
    STRONG_IMP_OBS_CONGR_RULE STRONG_SUM_IDENT_R);

(* Prove OBS_SUM_IDENT_L: |- !E. OBS_CONGR (sum nil E) E *)
val OBS_SUM_IDENT_L = save_thm (
   "OBS_SUM_IDENT_L",
    STRONG_IMP_OBS_CONGR_RULE STRONG_SUM_IDENT_L);

(* Prove OBS_SUM_IDEMP: |- !E. OBS_CONGR (sum E E) E *)
val OBS_SUM_IDEMP = save_thm (
   "OBS_SUM_IDEMP",
    STRONG_IMP_OBS_CONGR_RULE STRONG_SUM_IDEMP);

(* Prove OBS_SUM_COMM: |- !E E'. OBS_CONGR (sum E E') (sum E' E) *)
val OBS_SUM_COMM = save_thm (
   "OBS_SUM_COMM",
    STRONG_IMP_OBS_CONGR_RULE STRONG_SUM_COMM);

(* Prove OBS_SUM_ASSOC_R:
   |- !E E' E''. OBS_CONGR (sum (sum E E') E'') (sum E (sum E' E''))
 *)
val OBS_SUM_ASSOC_R = save_thm (
   "OBS_SUM_ASSOC_R",
    STRONG_IMP_OBS_CONGR_RULE STRONG_SUM_ASSOC_R);

(* Prove OBS_SUM_ASSOC_L:
   |- !E E' E''. OBS_CONGR (sum E (sum E' E'')) (sum (sum E E') E'')
 *)
val OBS_SUM_ASSOC_L = save_thm (
   "OBS_SUM_ASSOC_L",
    STRONG_IMP_OBS_CONGR_RULE STRONG_SUM_ASSOC_L);

(******************************************************************************)
(*                                                                            *)
(*           Basic laws of observation congruence for the parallel            *)
(*                 operator through strong equivalence                        *)
(*                                                                            *)
(******************************************************************************)

(* Prove OBS_PAR_IDENT_R: |- !E. OBS_CONGR (par E nil) E *)
val OBS_PAR_IDENT_R = save_thm (
   "OBS_PAR_IDENT_R",
    STRONG_IMP_OBS_CONGR_RULE STRONG_PAR_IDENT_R);

(* Prove OBS_PAR_IDENT_L: |- !E. OBS_CONGR (par nil E) E *)
val OBS_PAR_IDENT_L = save_thm (
   "OBS_PAR_IDENT_L",
    STRONG_IMP_OBS_CONGR_RULE STRONG_PAR_IDENT_L);

(* Prove OBS_PAR_COMM: |- !E E'. OBS_CONGR (par E E') (par E' E) *)
val OBS_PAR_COMM = save_thm (
   "OBS_PAR_COMM",
    STRONG_IMP_OBS_CONGR_RULE STRONG_PAR_COMM);

(* Prove OBS_PAR_ASSOC:
   |- !E E' E''. OBS_CONGR (par (par E E') E'') (par E (par E' E''))
 *)
val OBS_PAR_ASSOC = save_thm (
   "OBS_PAR_ASSOC",
    STRONG_IMP_OBS_CONGR_RULE STRONG_PAR_ASSOC);

(* Prove OBS_PAR_PREF_TAU:
   |- !u E E'.
       OBS_CONGR (par (prefix u E) (prefix tau E'))
                 (sum (prefix u (par E (prefix tau E')))
                      (prefix tau (par (prefix u E) E')))
 *)
val OBS_PAR_PREF_TAU = save_thm (
   "OBS_PAR_PREF_TAU",
    STRONG_IMP_OBS_CONGR_RULE STRONG_PAR_PREF_TAU);

(* Prove OBS_PAR_TAU_PREF:
   |- !E u E'.
       OBS_CONGR (par (prefix tau E) (prefix u E'))
                 (sum (prefix tau (par E (prefix u E')))
                      (prefix u (par (prefix tau E) E')))
 *)
val OBS_PAR_TAU_PREF = save_thm (
   "OBS_PAR_TAU_PREF",
    STRONG_IMP_OBS_CONGR_RULE STRONG_PAR_TAU_PREF);

(* Prove OBS_PAR_TAU_TAU:
   |- !E E'.
       OBS_CONGR (par (prefix tau E) (prefix tau E'))
                 (sum (prefix tau (par E (prefix tau E')))
                      (prefix tau (par (prefix tau E) E')))
 *)
val OBS_PAR_TAU_TAU = save_thm (
   "OBS_PAR_TAU_TAU", Q.SPEC `tau` OBS_PAR_PREF_TAU);

(* Prove OBS_PAR_PREF_NO_SYNCR:
   |- !l l'.
       ~(l = COMPL l') ==>
       (!E E'.
         OBS_CONGR (par (prefix (label l) E) (prefix (label l') E'))
                   (sum (prefix (label l) (par E (prefix (label l') E')))
                        (prefix (label l') (par (prefix (label l) E) E'))))
 *)
val OBS_PAR_PREF_NO_SYNCR = save_thm (
   "OBS_PAR_PREF_NO_SYNCR",
    STRIP_FORALL_RULE ((DISCH ``~((l :'a Label) = COMPL l')``) o
                       (STRIP_FORALL_RULE (MATCH_MP STRONG_IMP_OBS_CONGR)) o
                       UNDISCH)
                      STRONG_PAR_PREF_NO_SYNCR);

(* Prove OBS_PAR_PREF_SYNCR:
   |- !l l'.
       (l = COMPL l') ==>
       (!E E'.
         OBS_CONGR (par (prefix (label l) E) (prefix (label l') E'))
                   (sum
                    (sum (prefix (label l) (par E (prefix (label l') E')))
                         (prefix (label l') (par (prefix (label l) E) E')))
                    (prefix tau (par E E'))))
 *)
val OBS_PAR_PREF_SYNCR = save_thm (
   "OBS_PAR_PREF_SYNCR",
    STRIP_FORALL_RULE ((DISCH ``((l :'a Label) = COMPL l')``) o
                       (STRIP_FORALL_RULE (MATCH_MP STRONG_IMP_OBS_CONGR)) o
                       UNDISCH)
                      STRONG_PAR_PREF_SYNCR);

(* The expansion law for observation congruence:
  |- !f n f' m.
      (!i. i <= n ==> Is_Prefix (f i)) /\ (!j. j <= m ==> Is_Prefix (f' j))
   ==>
      OBS_CONGR
      (par (SIGMA f n) (SIGMA f' m))
      (sum
       (sum
        (SIGMA (\i. prefix (PREF_ACT (f i)) (par (PREF_PROC (f i)) (SIGMA f' m))) n)
        (SIGMA (\j. prefix (PREF_ACT (f' j)) (par (SIGMA f n) (PREF_PROC (f' j)))) m))
       (ALL_SYNC f n f' m))
 *)
val OBS_EXPANSION_LAW = save_thm (
   "OBS_EXPANSION_LAW",
    STRIP_FORALL_RULE (DISCH_ALL o (MATCH_MP STRONG_IMP_OBS_CONGR) o UNDISCH)
                      STRONG_EXPANSION_LAW);

(******************************************************************************)
(*                                                                            *)
(*          Basic laws of observation congruence for the restriction          *)
(*                operator through strong equivalence                         *)
(*                                                                            *)
(******************************************************************************)

(* Prove OBS_RESTR_NIL: |- !L. OBS_CONGR (restr L nil) nil *)
val OBS_RESTR_NIL = save_thm (
   "OBS_RESTR_NIL",
    STRONG_IMP_OBS_CONGR_RULE STRONG_RESTR_NIL);

(* Prove OBS_RESTR_SUM:
   |- !E E' L. OBS_CONGR (restr L (sum E E')) (sum (restr L E) (restr L E'))
 *)
val OBS_RESTR_SUM = save_thm (
   "OBS_RESTR_SUM",
    STRONG_IMP_OBS_CONGR_RULE STRONG_RESTR_SUM);

(* Prove OBS_RESTR_PREFIX_TAU:
   |- !E L. OBS_CONGR (restr (prefix tau E) L) (prefix tau (restr E L))
 *)
val OBS_RESTR_PREFIX_TAU = save_thm (
   "OBS_RESTR_PREFIX_TAU",
    STRONG_IMP_OBS_CONGR_RULE STRONG_RESTR_PREFIX_TAU);

(* Prove OBS_RESTR_PR_LAB_NIL:
   |- !l L.
       l IN L \/ (COMPL l) IN L ==>
       (!E. OBS_CONGR (restr L (prefix (label l) E)) nil)
 *)
val OBS_RESTR_PR_LAB_NIL = save_thm (
   "OBS_RESTR_PR_LAB_NIL",
   ((Q.GENL [`l`, `L`]) o
    (DISCH ``(l :'a Label) IN L \/ (COMPL l) IN L``) o
    (Q.GEN `E`) o
    UNDISCH)
       (IMP_TRANS
           (DISCH ``(l :'a Label) IN L \/ (COMPL l) IN L``
            (Q.SPEC `E`
             (UNDISCH
              (Q.SPECL [`l`, `L`] STRONG_RESTR_PR_LAB_NIL))))
           (SPECL [``restr (L :'a Label set) (prefix (label l) E)``, ``nil``]
                  STRONG_IMP_OBS_CONGR)));

(* Prove OBS_RESTR_PREFIX_LABEL:
   |- !l L.
       ~l IN L /\ ~(COMPL l) IN L ==>
       (!E. OBS_CONGR (restr (prefix (label l) E) L) (prefix (label l) (restr E L)))
 *)
val OBS_RESTR_PREFIX_LABEL = save_thm (
   "OBS_RESTR_PREFIX_LABEL",
  ((Q.GENL [`l`, `L`]) o
   (DISCH ``~((l :'a Label) IN L) /\ ~((COMPL l) IN L)``) o
   (Q.GEN `E`) o
   UNDISCH)
      (IMP_TRANS
           (DISCH ``~((l :'a Label) IN L) /\ ~((COMPL l) IN L)``
            (Q.SPEC `E`
             (UNDISCH
              (Q.SPECL [`l`, `L`] STRONG_RESTR_PREFIX_LABEL))))
           (SPECL [``restr (L :'a Label set) (prefix (label l) E)``,
                   ``prefix (label (l :'a Label)) (restr L E)``]
                  STRONG_IMP_OBS_CONGR)));

(******************************************************************************)
(*                                                                            *)
(*           Basic laws of observation congruence for the recursion           *)
(*                 operator through strong equivalence                        *)
(*                                                                            *)
(******************************************************************************)

(* The unfolding law:
   OBS_UNFOLDING: |- !X E. OBS_CONGR (rec X E) (CCS_Subst E (rec X E) X)
 *)
val OBS_UNFOLDING = save_thm (
   "OBS_UNFOLDING",
    STRONG_IMP_OBS_CONGR_RULE STRONG_UNFOLDING);

(* Prove the theorem OBS_PREF_REC_EQUIV:
   |- !u s v.
       OBS_CONGR
       (prefix u (rec s (prefix v (prefix u (var s)))))
       (rec s (prefix u (prefix v (var s))))
 *)
val OBS_PREF_REC_EQUIV = save_thm (
   "OBS_PREF_REC_EQUIV",
    STRONG_IMP_OBS_CONGR_RULE STRONG_PREF_REC_EQUIV);

(******************************************************************************)
(*                                                                            *)
(*         Basic laws of observation congruence for the relabelling           *)
(*               operator through strong equivalence                          *)
(*                                                                            *)
(******************************************************************************)

(* Prove OBS_RELAB_NIL: |- !rf. OBS_CONGR (relab nil rf) nil *)
val OBS_RELAB_NIL = save_thm (
   "OBS_RELAB_NIL",
    STRONG_IMP_OBS_CONGR_RULE STRONG_RELAB_NIL);

(* Prove OBS_RELAB_SUM:
   |- !E E' rf. OBS_CONGR (relab (sum E E') rf) (sum (relab E rf) (relab E' rf))
 *)
val OBS_RELAB_SUM = save_thm (
   "OBS_RELAB_SUM",
    STRONG_IMP_OBS_CONGR_RULE STRONG_RELAB_SUM);

(* Prove OBS_RELAB_PREFIX:
   |- !u E labl.
       OBS_CONGR (relab (prefix u E) (RELAB labl))
                 (prefix (relabel (RELAB labl) u) (relab E (RELAB labl)))
 *)
val OBS_RELAB_PREFIX = save_thm (
   "OBS_RELAB_PREFIX",
    STRONG_IMP_OBS_CONGR_RULE STRONG_RELAB_PREFIX);

(******************************************************************************)
(*                                                                            *)
(*      tau-laws for observation congruence (and the same tau-laws            *)
(*       for observation equivalence derived through the congruence)          *)
(*                                                                            *)
(******************************************************************************)

(* Prove TAU1:
   |- !u E. OBS_CONGR (prefix u (prefix tau E)) (prefix u E)
 *)
val TAU1 = store_thm ("TAU1",
  ``!(u :'a Action) E. OBS_CONGR (prefix u (prefix tau E)) (prefix u E)``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E` \\
      ASM_REWRITE_TAC [WEAK_TRANS, TAU_WEAK] \\
      EXISTS_TAC ``prefix (u :'a Action) E`` \\
      Q.EXISTS_TAC `E` \\
      ASM_REWRITE_TAC [EPS_REFL, PREFIX],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      EXISTS_TAC ``prefix (tau :'a Action) E2`` \\
      ASM_REWRITE_TAC [WEAK_TRANS, TAU_WEAK] \\
      EXISTS_TAC ``prefix (u :'a Action) (prefix tau E2)`` \\
      EXISTS_TAC ``prefix (tau :'a Action) E2`` \\
      ASM_REWRITE_TAC [EPS_REFL, PREFIX] ]);

(* Prove WEAK_TAU1:
   |- !u E. WEAK_EQUIV (prefix u (prefix tau E)) (prefix u E)
 *)
val WEAK_TAU1 = save_thm ("WEAK_TAU1",
    OBS_CONGR_IMP_WEAK_EQUIV_RULE TAU1);

(* Prove TAU2:
   |- !E. OBS_CONGR (sum E (prefix tau E)) (prefix tau E)
 *)
val TAU2 = store_thm ("TAU2",
  ``!E. OBS_CONGR (sum E (prefix tau E)) (prefix tau E)``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [WEAK_TRANS, WEAK_EQUIV_REFL] \\
        take [`E`, `E1`] \\
        ASM_REWRITE_TAC [EPS_REFL] \\
        MATCH_MP_TAC ONE_TAU \\
        ASM_REWRITE_TAC [PREFIX],
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [WEAK_EQUIV_REFL] \\
        IMP_RES_TAC TRANS_IMP_WEAK_TRANS ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E2` \\
      REWRITE_TAC [WEAK_TRANS, WEAK_EQUIV_REFL] \\
      take [`sum E (prefix tau E)`, `E2`] \\
      REWRITE_TAC [EPS_REFL] \\
      MATCH_MP_TAC SUM2 \\
      PURE_ONCE_ASM_REWRITE_TAC [] ]);

(* Prove WEAK_TAU2:
   |- !E. WEAK_EQUIV (sum E (prefix tau E)) (prefix tau E)
 *)
val WEAK_TAU2 = save_thm ("WEAK_TAU2",
    OBS_CONGR_IMP_WEAK_EQUIV_RULE TAU2);

(* Prove TAU3:
   |- !u E E'.
       OBS_CONGR (sum (prefix u (sum E (prefix tau E'))) (prefix u E'))
                 (prefix u (sum E (prefix tau E')))
 *)
val TAU3 = store_thm ("TAU3",
  ``!(u :'a Action) E E'.
        OBS_CONGR (sum (prefix u (sum E (prefix tau E'))) (prefix u E'))
                  (prefix u (sum E (prefix tau E')))``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        Q.EXISTS_TAC `E1` \\
        REWRITE_TAC [WEAK_EQUIV_REFL] \\
        IMP_RES_TAC TRANS_IMP_WEAK_TRANS,
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC TRANS_PREFIX \\
        Q.EXISTS_TAC `E1` \\
        ASM_REWRITE_TAC [WEAK_TRANS, WEAK_EQUIV_REFL] \\
        take [`prefix (u :'a Action) (sum E (prefix tau E'))`,
              `sum E (prefix tau E')`] \\
        REWRITE_TAC [EPS_REFL, PREFIX] \\
        MATCH_MP_TAC ONE_TAU \\
        MATCH_MP_TAC SUM2 \\
        ASM_REWRITE_TAC [PREFIX] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E2` \\
      REWRITE_TAC [WEAK_TRANS, WEAK_EQUIV_REFL] \\
      take [`sum (prefix u (sum E (prefix tau E'))) (prefix u E')`, `E2`] \\
      REWRITE_TAC [EPS_REFL] \\
      MATCH_MP_TAC SUM1 \\
      PURE_ONCE_ASM_REWRITE_TAC [] ]);

(* Prove WEAK_TAU3:
   |- !u E E'.
       WEAK_EQUIV (sum (prefix u (sum E (prefix tau E'))) (prefix u E'))
                 (prefix u (sum E (prefix tau E')))
 *)
val WEAK_TAU3 = save_thm ("WEAK_TAU3",
    OBS_CONGR_IMP_WEAK_EQUIV_RULE TAU3);

val _ = export_theory ();
val _ = html_theory "ObsCongrLaws";

(* last updated: Jun 20, 2017 *)
