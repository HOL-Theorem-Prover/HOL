(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory prim_recTheory arithmeticTheory relationTheory;

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory
     WeakEQTheory WeakEQLib;

val _ = new_theory "WeakLaws";

(******************************************************************************)
(*                                                                            *)
(*  Basic laws of observation equivalence for the binary summation operator   *)
(*              derived through strong equivalence                            *)
(*                                                                            *)
(******************************************************************************)

(* Prove WEAK_SUM_IDENT_R: |- !E. WEAK_EQUIV (sum E nil) E *)
val WEAK_SUM_IDENT_R = save_thm (
   "WEAK_SUM_IDENT_R",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_SUM_IDENT_R);

(* Prove WEAK_SUM_IDENT_L: |- !E. WEAK_EQUIV (sum nil E) E *)
val WEAK_SUM_IDENT_L = save_thm (
   "WEAK_SUM_IDENT_L",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_SUM_IDENT_L);

(* Prove WEAK_SUM_IDEMP: |- !E. WEAK_EQUIV (sum E E) E *)
val WEAK_SUM_IDEMP = save_thm (
   "WEAK_SUM_IDEMP",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_SUM_IDEMP);

(* Prove WEAK_SUM_COMM: |- !E E'. WEAK_EQUIV (sum E E') (sum E' E) *)
val WEAK_SUM_COMM = save_thm (
   "WEAK_SUM_COMM",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_SUM_COMM);

(* Observation equivalence of stable agents is substitutive under the binary
   summation operator on the left:
   |- !E E'. WEAK_EQUIV E E' /\ STABLE E /\ STABLE E' ==>
             (!E''. WEAK_EQUIV (sum E'' E) (sum E'' E'))
 *)
val WEAK_EQUIV_SUBST_SUM_L = save_thm (
   "WEAK_EQUIV_SUBST_SUM_L",
    Q.GENL [`E`, `E'`]
     (DISCH_ALL
      (Q.GEN `E''`
       (OE_TRANS
         (Q.SPECL [`E''`, `E`] WEAK_SUM_COMM)
         (OE_TRANS
           (SPEC_ALL (UNDISCH (SPEC_ALL WEAK_EQUIV_SUBST_SUM_R)))
           (Q.SPECL [`E'`, `E''`] WEAK_SUM_COMM))))));

(* Prove WEAK_SUM_ASSOC_R:
   |- !E E' E''. WEAK_EQUIV (sum (sum E E') E'') (sum E (sum E' E''))
 *)
val WEAK_SUM_ASSOC_R = save_thm (
   "WEAK_SUM_ASSOC_R",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_SUM_ASSOC_R);

(* Prove WEAK_SUM_ASSOC_L:
   |- !E E' E''. WEAK_EQUIV (sum E (sum E' E'')) (sum (sum E E') E'')
 *)
val WEAK_SUM_ASSOC_L = save_thm (
   "WEAK_SUM_ASSOC_L",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_SUM_ASSOC_L);

(******************************************************************************)
(*                                                                            *)
(*           Basic laws of observation equivalence for the parallel           *)
(*             operator derived through strong equivalence                    *)
(*                                                                            *)
(******************************************************************************)

(* Prove WEAK_PAR_IDENT_R: |- !E. WEAK_EQUIV (par E nil) E
 *)
val WEAK_PAR_IDENT_R = save_thm (
   "WEAK_PAR_IDENT_R",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_PAR_IDENT_R);

(* Prove WEAK_PAR_IDENT_L: |- !E. WEAK_EQUIV (par nil E) E
 *)
val WEAK_PAR_IDENT_L = save_thm (
   "WEAK_PAR_IDENT_L",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_PAR_IDENT_L);

(* Prove WEAK_PAR_COMM: |- !E E'. WEAK_EQUIV (par E E') (par E' E)
 *)
val WEAK_PAR_COMM = save_thm (
   "WEAK_PAR_COMM",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_PAR_COMM);

(* Prove WEAK_PAR_ASSOC:
   |- !E E' E''. WEAK_EQUIV (par (par E E') E'') (par E (par E' E''))
 *)
val WEAK_PAR_ASSOC = save_thm (
   "WEAK_PAR_ASSOC",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_PAR_ASSOC);

(* Prove WEAK_PAR_PREF_TAU:
   |- !u E E'.
       WEAK_EQUIV (par (prefix u E) (prefix tau E'))
                 (sum (prefix u (par E (prefix tau E')))
                      (prefix tau (par (prefix u E) E')))
 *)
val WEAK_PAR_PREF_TAU = save_thm (
   "WEAK_PAR_PREF_TAU",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_PAR_PREF_TAU);

(* Prove WEAK_PAR_TAU_PREF:
   |- !E u E'.
       WEAK_EQUIV (par (prefix tau E) (prefix u E'))
                 (sum (prefix tau (par E (prefix u E')))
                      (prefix u (par (prefix tau E) E')))
 *)
val WEAK_PAR_TAU_PREF = save_thm (
   "WEAK_PAR_TAU_PREF",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_PAR_TAU_PREF);

(* Prove WEAK_PAR_TAU_TAU:
   |- !E E'.
       WEAK_EQUIV (par (prefix tau E) (prefix tau E'))
                 (sum (prefix tau (par E (prefix tau E')))
                      (prefix tau (par (prefix tau E) E')))
 *)
val WEAK_PAR_TAU_TAU = save_thm (
   "WEAK_PAR_TAU_TAU", Q.SPEC `tau` WEAK_PAR_PREF_TAU);

(* Prove WEAK_PAR_PREF_NO_SYNCR:
   |- !l l'.
       ~(l = COMPL l') ==>
       (!E E'.
         WEAK_EQUIV (par (prefix (label l) E) (prefix (label l') E'))
                   (sum (prefix (label l) (par E (prefix (label l') E')))
                        (prefix (label l') (par (prefix (label l) E) E'))))
 *)
val WEAK_PAR_PREF_NO_SYNCR = save_thm (
   "WEAK_PAR_PREF_NO_SYNCR",
    STRIP_FORALL_RULE ((DISCH ``~((l :'a Label) = COMPL l')``) o
                       (STRONG_IMP_WEAK_EQUIV_RULE) o
                       UNDISCH)
                      STRONG_PAR_PREF_NO_SYNCR);

(* Prove WEAK_PAR_PREF_SYNCR:
   |- !l l'.
       (l = COMPL l') ==>
       (!E E'.
         WEAK_EQUIV (par (prefix (label l) E) (prefix (label l') E'))
                   (sum
                    (sum (prefix (label l) (par E (prefix (label l') E')))
                         (prefix (label l') (par (prefix (label l) E) E')))
                    (prefix tau (par E E'))))
 *)
val WEAK_PAR_PREF_SYNCR = save_thm (
   "WEAK_PAR_PREF_SYNCR",
    STRIP_FORALL_RULE ((DISCH ``((l :'a Label) = COMPL l')``) o
                       (STRONG_IMP_WEAK_EQUIV_RULE) o
                       UNDISCH)
                      STRONG_PAR_PREF_SYNCR);

(* The expansion law for observation equivalence:
  |- !f n f' m.
      (!i. i <= n ==> Is_Prefix (f i)) /\ (!j. j <= m ==> Is_Prefix (f' j))
   ==>
      WEAK_EQUIV
      (par (SIGMA f n) (SIGMA f' m))
      (sum
       (sum
        (SIGMA (\i. prefix (PREF_ACT (f i)) (par (PREF_PROC (f i)) (SIGMA f' m))) n)
        (SIGMA (\j. prefix (PREF_ACT (f' j)) (par (SIGMA f n) (PREF_PROC (f' j)))) m))
       (ALL_SYNC f n f' m))
 *)
val WEAK_EXPANSION_LAW = save_thm (
   "WEAK_EXPANSION_LAW",
    STRIP_FORALL_RULE (DISCH_ALL o (MATCH_MP STRONG_IMP_WEAK_EQUIV) o UNDISCH)
                      STRONG_EXPANSION_LAW);

(******************************************************************************)
(*                                                                            *)
(*      Basic laws of observation equivalence for the restriction             *)
(*            operator derived through strong equivalence                     *)
(*                                                                            *)
(******************************************************************************)

(* Prove WEAK_RESTR_NIL: |- !L. WEAK_EQUIV (restr nil L) nil *)
val WEAK_RESTR_NIL = save_thm (
   "WEAK_RESTR_NIL",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_RESTR_NIL);

(* Prove WEAK_RESTR_SUM:
   |- !E E' L. WEAK_EQUIV (restr (sum E E') L) (sum (restr E L) (restr E' L))
 *)
val WEAK_RESTR_SUM = save_thm (
   "WEAK_RESTR_SUM",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_RESTR_SUM);

(* Prove WEAK_RESTR_PREFIX_TAU:
   |- !E L. WEAK_EQUIV (restr (prefix tau E) L) (prefix tau (restr E L))
 *)
val WEAK_RESTR_PREFIX_TAU = save_thm (
   "WEAK_RESTR_PREFIX_TAU",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_RESTR_PREFIX_TAU);

(* Prove WEAK_RESTR_PR_LAB_NIL:
   |- !l L. l IN L \/ (COMPL l) IN L ==>
            (!E. WEAK_EQUIV (restr (prefix (label l) E) L) nil)
 *)
val WEAK_RESTR_PR_LAB_NIL = save_thm (
   "WEAK_RESTR_PR_LAB_NIL",
    GEN_ALL
       (DISCH ``(l :'a Label) IN L \/ (COMPL l) IN L``
        (Q.GEN `E`
         (UNDISCH
          (IMP_TRANS
           (DISCH ``(l :'a Label) IN L \/ (COMPL l) IN L``
            (Q.SPEC `E`
             (UNDISCH
              (Q.SPECL [`l`, `L`] STRONG_RESTR_PR_LAB_NIL))))
           (SPECL [``restr (L :'a Label set) (prefix (label l) E)``, ``nil``]
                    STRONG_IMP_WEAK_EQUIV))))));

(* Prove WEAK_RESTR_PREFIX_LABEL:
   |- !l L.
       ~l IN L /\ ~(COMPL l) IN L ==>
       (!E. WEAK_EQUIV (restr (prefix (label l) E) L) (prefix (label l) (restr E L)))
 *)
val WEAK_RESTR_PREFIX_LABEL = save_thm (
   "WEAK_RESTR_PREFIX_LABEL",
    GEN_ALL
       (DISCH ``~((l :'a Label) IN L) /\ ~((COMPL l) IN L)``
        (Q.GEN `E`
         (UNDISCH
          (IMP_TRANS
           (DISCH ``~((l :'a Label) IN L) /\ ~((COMPL l) IN L)``
            (Q.SPEC `E`
             (UNDISCH
              (Q.SPECL [`l`, `L`] STRONG_RESTR_PREFIX_LABEL))))
           (SPECL [``restr (L :'a Label set) (prefix (label l) E)``,
                   ``prefix (label (l :'a Label)) (restr L E)``]
                  STRONG_IMP_WEAK_EQUIV))))));

(******************************************************************************)
(*                                                                            *)
(*        Basic laws of observation equivalence for the relabelling           *)
(*              operator derived through strong equivalence                   *)
(*                                                                            *)
(******************************************************************************)

(* Prove WEAK_RELAB_NIL: |- !rf. WEAK_EQUIV (relab nil rf) nil *)
val WEAK_RELAB_NIL = save_thm (
   "WEAK_RELAB_NIL",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_RELAB_NIL);

(* Prove WEAK_RELAB_SUM:
   |- !E E' rf. WEAK_EQUIV (relab (sum E E') rf) (sum (relab E rf) (relab E' rf))
 *)
val WEAK_RELAB_SUM = save_thm (
   "WEAK_RELAB_SUM",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_RELAB_SUM);

(* Prove WEAK_RELAB_PREFIX:
   |- !u E labl.
       WEAK_EQUIV (relab (prefix u E) (RELAB labl))
                 (prefix (relabel (Apply_Relab labl) u) (relab E (RELAB labl)))
 *)
val WEAK_RELAB_PREFIX = save_thm (
   "WEAK_RELAB_PREFIX",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_RELAB_PREFIX);

(******************************************************************************)
(*                                                                            *)
(*       Basic laws of observation equivalence for the recursion              *)
(*               operator through strong equivalence                          *)
(*                                                                            *)
(******************************************************************************)

(* The unfolding law:
   WEAK_UNFOLDING: |- !X E. WEAK_EQUIV (rec X E) (CCS_Subst E (rec X E) X)
 *)
val WEAK_UNFOLDING = save_thm (
   "WEAK_UNFOLDING",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_UNFOLDING);

(* Prove the theorem WEAK_PREF_REC_EQUIV:
   |- !u s v.
       WEAK_EQUIV
       (prefix u (rec s (prefix v (prefix u (var s)))))
       (rec s (prefix u (prefix v (var s))))
 *)
val WEAK_PREF_REC_EQUIV = save_thm (
   "WEAK_PREF_REC_EQUIV",
    STRONG_IMP_WEAK_EQUIV_RULE STRONG_PREF_REC_EQUIV);

(******************************************************************************)
(*                                                                            *)
(*         the tau-law "tau.E = E" for observation equivalence                *)
(*                                                                            *)
(******************************************************************************)

(* Prove TAU_WEAK:  |- !E. WEAK_EQUIV (prefix tau E) E *)
val TAU_WEAK = store_thm ("TAU_WEAK",
  ``!E. WEAK_EQUIV (prefix tau E) E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [WEAK_PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >| [ (* goal 1 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      IMP_RES_TAC Action_distinct_label,
      (* goal 2 (of 4) *)
      Q.EXISTS_TAC `E2` \\
      REWRITE_TAC [WEAK_TRANS, WEAK_EQUIV_REFL] \\
      take [`E`, `E2`] \\
      ASM_REWRITE_TAC [EPS_REFL] \\
      MATCH_MP_TAC ONE_TAU \\
      REWRITE_TAC [PREFIX],
      (* goal 3 (of 4) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E1` \\
      ASM_REWRITE_TAC [EPS_REFL, WEAK_EQUIV_REFL],
      (* goal 4 (of 4) *)
      Q.EXISTS_TAC `E2` \\
      REWRITE_TAC [WEAK_EQUIV_REFL] \\
      MATCH_MP_TAC EPS_TRANS \\
      Q.EXISTS_TAC `E` \\
      IMP_RES_TAC ONE_TAU >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC ONE_TAU \\
      REWRITE_TAC [PREFIX] ]);

val _ = export_theory ();
val _ = html_theory "WeakLaws";

(* last updated: Jun 20, 2017 *)
