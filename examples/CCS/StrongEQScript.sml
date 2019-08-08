(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna, Italy (Author: Chun Tian)
 * Copyright 2018-2019  Fondazione Bruno Kessler, Italy (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory relationTheory bisimulationTheory listTheory;
open CCSLib CCSTheory;

val _ = new_theory "StrongEQ";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*    Operational definition of strong equivalence for CCS (strong_sem.ml)    *)
(*                                                                            *)
(******************************************************************************)

(* Type abbreviations *)
val _ = type_abbrev_pp ("simulation", ``:('a, 'b) CCS -> ('a, 'b) CCS -> bool``);

(* new definition based on relationTheory.BISIM *)
val STRONG_BISIM_def = Define
   `STRONG_BISIM (R :('a, 'b) simulation) = BISIM TRANS R`;

(* original definition of STRONG_BISIM, now becomes a theorem *)
Theorem STRONG_BISIM :
    STRONG_BISIM (Bsm :('a, 'b) simulation) =
    !E E'. Bsm E E' ==>
        !u.
           (!E1. TRANS E u E1 ==>
                 ?E2. TRANS E' u E2 /\ Bsm E1 E2) /\
           (!E2. TRANS E' u E2 ==>
                 ?E1. TRANS E u E1 /\ Bsm E1 E2)
Proof
    RW_TAC std_ss [STRONG_BISIM_def, BISIM_def]
 >> METIS_TAC []
QED

(* The identity relation is a strong bisimulation. *)
Theorem IDENTITY_STRONG_BISIM :
    STRONG_BISIM Id
Proof
    REWRITE_TAC [STRONG_BISIM_def, BISIM_ID]
QED

(* The converse of a strong bisimulation is a strong bisimulation. *)
Theorem CONVERSE_STRONG_BISIM :
    !Bsm. STRONG_BISIM Bsm ==> STRONG_BISIM (inv Bsm)
Proof
    REWRITE_TAC [STRONG_BISIM_def, BISIM_INV]
QED

(* The composition of two strong bisimulations is a strong bisimulation. *)
Theorem COMP_STRONG_BISIM :
    !Bsm1 Bsm2. STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==>
                STRONG_BISIM (Bsm2 O Bsm1)
Proof
    REWRITE_TAC [STRONG_BISIM_def, BISIM_O]
QED

(* The union of two strong bisimulations is a strong bisimulation. *)
Theorem UNION_STRONG_BISIM :
    !Bsm1 Bsm2. STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==>
                STRONG_BISIM (Bsm1 RUNION Bsm2)
Proof
    REWRITE_TAC [STRONG_BISIM_def, BISIM_RUNION]
QED

(* The (strong) bisimilarity, now based on BISIM_REL *)
val STRONG_EQUIV_def = Define `STRONG_EQUIV = BISIM_REL TRANS`;

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Infix (NONASSOC, 450),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK (UTF8.chr 0x223C), BreakSpace (1,0)],
                   term_name = "STRONG_EQUIV" };

val _ = TeX_notation { hol = UTF8.chr 0x223C,
                       TeX = ("\\HOLTokenStrongEQ", 1) };

(* |- !p q.
         (!l.
              (!p'. p --l-> p' ==> ?q'. q --l-> q' /\ STRONG_EQUIV p' q') /\
              !q'. q --l-> q' ==> ?p'. p --l-> p' /\ STRONG_EQUIV p' q') ==>
         STRONG_EQUIV p q
 *)
val STRONG_EQUIV_rules = save_thm
  ("STRONG_EQUIV_rules",
    REWRITE_RULE [SYM STRONG_EQUIV_def] (Q.ISPEC `TRANS` BISIM_REL_rules));

(* |- !BISIM_REL'.
         (!a0 a1.
              BISIM_REL' a0 a1 ==>
              !l.
                  (!p'. a0 --l-> p' ==> ?q'. a1 --l-> q' /\ BISIM_REL' p' q') /\
                  !q'. a1 --l-> q' ==> ?p'. a0 --l-> p' /\ BISIM_REL' p' q') ==>
         !a0 a1. BISIM_REL' a0 a1 ==> STRONG_EQUIV a0 a1
 *)
val STRONG_EQUIV_coind = save_thm
  ("STRONG_EQUIV_coind",
    REWRITE_RULE [SYM STRONG_EQUIV_def] (Q.ISPEC `TRANS` BISIM_REL_coind));

(* |- !a0 a1.
         STRONG_EQUIV a0 a1 <=>
         !l.
             (!p'. a0 --l-> p' ==> ?q'. a1 --l-> q' /\ STRONG_EQUIV p' q') /\
             !q'. a1 --l-> q' ==> ?p'. a0 --l-> p' /\ STRONG_EQUIV p' q'
 *)
val STRONG_EQUIV_cases = save_thm
  ("STRONG_EQUIV_cases",
    REWRITE_RULE [SYM STRONG_EQUIV_def] (Q.ISPEC `TRANS` BISIM_REL_cases));

Theorem STRONG_EQUIV_IS_STRONG_BISIM :
    STRONG_BISIM STRONG_EQUIV
Proof
    REWRITE_TAC [STRONG_BISIM_def, STRONG_EQUIV_def, BISIM_REL_IS_BISIM]
QED

(* Alternative definition of STRONG_EQUIV *)
Theorem STRONG_EQUIV :
    !E E'. STRONG_EQUIV E E' = ?Bsm. Bsm E E' /\ STRONG_BISIM Bsm
Proof
    METIS_TAC [STRONG_EQUIV_def, STRONG_BISIM_def, BISIM_REL_def]
QED

Theorem STRONG_EQUIV_equivalence :
    equivalence STRONG_EQUIV
Proof
    REWRITE_TAC [STRONG_EQUIV_def, BISIM_REL_IS_EQUIV_REL]
QED

Theorem STRONG_EQUIV_REFL :
    !E. STRONG_EQUIV E E
Proof
    PROVE_TAC [REWRITE_RULE [equivalence_def, reflexive_def]
                            STRONG_EQUIV_equivalence]
QED

Theorem STRONG_EQUIV_SYM :
    !E E'. STRONG_EQUIV E E' ==> STRONG_EQUIV E' E
Proof
    PROVE_TAC [REWRITE_RULE [equivalence_def, symmetric_def]
                            STRONG_EQUIV_equivalence]
QED

Theorem STRONG_EQUIV_TRANS :
    !E E' E''. STRONG_EQUIV E E' /\ STRONG_EQUIV E' E'' ==> STRONG_EQUIV E E''
Proof
    PROVE_TAC [REWRITE_RULE [equivalence_def, transitive_def]
                            STRONG_EQUIV_equivalence]
QED

val STRONG_BISIM_SUBSET_STRONG_EQUIV = store_thm (
   "STRONG_BISIM_SUBSET_STRONG_EQUIV",
  ``!Bsm. STRONG_BISIM Bsm ==> Bsm RSUBSET STRONG_EQUIV``,
    PROVE_TAC [RSUBSET, STRONG_EQUIV]);

(* Syntactic equivalence implies strong equivalence. *)
val EQUAL_IMP_STRONG_EQUIV = store_thm (
   "EQUAL_IMP_STRONG_EQUIV", ``!E E'. (E = E') ==> STRONG_EQUIV E E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [STRONG_EQUIV_REFL]);

(* Prop. 4, page 91: strong equivalence satisfies property [*] *)
Theorem PROPERTY_STAR :
    !E E'. STRONG_EQUIV E E' <=>
           !u. (!E1. TRANS E  u E1 ==> ?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2) /\
               (!E2. TRANS E' u E2 ==> ?E1. TRANS E  u E1 /\ STRONG_EQUIV E1 E2)
Proof
   METIS_TAC [STRONG_EQUIV_cases]
QED

(* Half versions of PROPERTY_STAR *)
val PROPERTY_STAR_LEFT = store_thm (
   "PROPERTY_STAR_LEFT",
  ``!E E'. STRONG_EQUIV E E' ==>
        !u E1. TRANS E u E1 ==> ?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2``,
    PROVE_TAC [PROPERTY_STAR]);

val PROPERTY_STAR_RIGHT = store_thm (
   "PROPERTY_STAR_RIGHT",
  ``!E E'. STRONG_EQUIV E E' ==>
        !u E2. TRANS E' u E2 ==> ?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2``,
    PROVE_TAC [PROPERTY_STAR]);

(* Strong equivalence is substitutive under prefix operator. *)
val STRONG_EQUIV_SUBST_PREFIX = store_thm (
   "STRONG_EQUIV_SUBST_PREFIX",
      ``!E E'.
         STRONG_EQUIV E E' ==> !u. STRONG_EQUIV (prefix u E) (prefix u E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC
      [SPECL [``prefix (u :'b Action) E``, ``prefix (u :'b Action) E'``] PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ EXISTS_TAC ``E' :('a, 'b) CCS``,
      EXISTS_TAC ``E :('a, 'b) CCS``]
 >> IMP_RES_TAC TRANS_PREFIX
 >> ASM_REWRITE_TAC [PREFIX]);

(* Strong equivalence is preserved by binary summation. *)
val STRONG_EQUIV_PRESD_BY_SUM = store_thm (
   "STRONG_EQUIV_PRESD_BY_SUM",
      ``!E1 E1' E2 E2'.
         STRONG_EQUIV E1 E1' /\ STRONG_EQUIV E2 E2' ==>
         STRONG_EQUIV (sum E1 E2) (sum E1' E2')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 *)
      IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals here *)
      RES_TAC \\
      EXISTS_TAC ``E2'' :('a, 'b) CCS`` \\
      ASM_REWRITE_TAC []
      >| [ MATCH_MP_TAC SUM1, MATCH_MP_TAC SUM2 ] \\
      ASM_REWRITE_TAC [],
      (* goal 2 *)
      IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals here *)
      RES_TAC \\
      EXISTS_TAC ``E1'' :('a, 'b) CCS`` \\
      ASM_REWRITE_TAC []
      >| [ MATCH_MP_TAC SUM1, MATCH_MP_TAC SUM2] \\
      ASM_REWRITE_TAC [] ]);

(* Strong equivalence is substitutive under summation operator on the right.
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (sum E E'') (sum E' E''))
 *)
val STRONG_EQUIV_SUBST_SUM_R = save_thm (
   "STRONG_EQUIV_SUBST_SUM_R",
   (GEN_ALL o
    DISCH_ALL o
    GEN_ALL o
    UNDISCH o
    (REWRITE_RULE [STRONG_EQUIV_REFL]) o
    DISCH_ALL)
       (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM
                 (CONJ (ASSUME ``STRONG_EQUIV E E'``)
                       (ASSUME ``STRONG_EQUIV E'' E''``))));

(* Strong equivalence is substitutive under summation operator on the left.
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (sum E'' E) (sum E'' E'))
 *)
val STRONG_EQUIV_SUBST_SUM_L = save_thm (
   "STRONG_EQUIV_SUBST_SUM_L",
   (GEN_ALL o
    DISCH_ALL o
    GEN_ALL o
    UNDISCH o
    (REWRITE_RULE [STRONG_EQUIV_REFL]) o
    DISCH_ALL)
       (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM
                 (CONJ (ASSUME ``STRONG_EQUIV E'' E''``)
                       (ASSUME ``STRONG_EQUIV E E'``))));

(* Strong equivalence is preserved by parallel composition. *)
val STRONG_EQUIV_PRESD_BY_PAR = store_thm (
   "STRONG_EQUIV_PRESD_BY_PAR",
      ``!E1 E1' E2 E2'.
         STRONG_EQUIV E1 E1' /\ STRONG_EQUIV E2 E2' ==>
         STRONG_EQUIV (par E1 E2) (par E1' E2')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC
       ``\x y.
         (?F1 F2 F3 F4.
           (x = par F1 F3) /\ (y = par F2 F4) /\
           STRONG_EQUIV F1 F2 /\ STRONG_EQUIV F3 F4)``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E1`, `E1'`, `E2`, `E2'`] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E = par F1 F3``]
                                 (ASSUME ``TRANS E u E1''``)) \\
        IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
        [ (* goal 2.1.1 (of 3) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F1 F2``)) \\
          EXISTS_TAC ``par E2'' F4`` \\
          ASM_REWRITE_TAC [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1.1 (of 2) *)
            MATCH_MP_TAC PAR1 \\
            PURE_ONCE_ASM_REWRITE_TAC [],
            (* goal 2.1.1.2 (of 2) *)
            take [`E1'''`, `E2''`, `F3`, `F4`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.1.2 (of 3) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F3 F4``)) \\
          EXISTS_TAC ``par F2 E2''`` \\
          ASM_REWRITE_TAC [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            MATCH_MP_TAC PAR2 >> PURE_ONCE_ASM_REWRITE_TAC [],
            (* goal 2.1.2.2 (of 2) *)
            take [`F1`, `F2`, `E1'''`, `E2''`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.1.3 (of 3) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F1 F2``)) \\
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV F3 F4``)) \\
          EXISTS_TAC ``par E2''' E2''''`` \\
          ASM_REWRITE_TAC [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.3.1 (of 2) *)
            MATCH_MP_TAC PAR3 \\
            EXISTS_TAC ``l: 'b Label`` \\
            ASM_REWRITE_TAC [],
            (* goal 2.1.3.2 (of 2) *)
            take [`E1'''`, `E2'''`, `E2''`, `E2''''`] \\
            ASM_REWRITE_TAC [] ] ],
         (* goal 2.2 (of 2) *)
         ASSUME_TAC
           (REWRITE_RULE [ASSUME ``E' = par F2 F4``]
                         (ASSUME ``TRANS E' u E2''``)) \\
         IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
         [ (* goal 2.2.1 (of 3) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F1 F2``)) \\
           EXISTS_TAC ``par E1''' F3`` \\
           ASM_REWRITE_TAC [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.1.1 (of 2) *)
             MATCH_MP_TAC PAR1 \\
             PURE_ONCE_ASM_REWRITE_TAC [],
             (* goal 2.2.1.2 (of 2) *)
             take [`E1'''`, `E1''`, `F3`, `F4`] \\
             ASM_REWRITE_TAC [] ],
           (* goal 2.2.2 (of 3) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F3 F4``)) \\
           EXISTS_TAC ``par F1 E1'''`` \\
           ASM_REWRITE_TAC [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.2.1 (of 2) *)
             MATCH_MP_TAC PAR2 \\
             PURE_ONCE_ASM_REWRITE_TAC [],
             (* goal 2.2.2.2 (of 2) *)
             take [`F1`, `F2`, `E1'''`, `E1''`] \\
             ASM_REWRITE_TAC [] ],
           (* goal 2.2.3 (of 3) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F1 F2``)) \\
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV F3 F4``)) \\
           EXISTS_TAC ``par E1''' E1''''`` \\
           ASM_REWRITE_TAC [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.3.1 (of 2) *)
             MATCH_MP_TAC PAR3 \\
             EXISTS_TAC ``l: 'b Label`` \\
             ASM_REWRITE_TAC [],
             (* goal 2.2.3.2 (of 2) *)
             take [`E1'''`, `E1''`, `E1''''`, `E2'''`] \\
             ASM_REWRITE_TAC [] ] ] ] ]);

(* Strong equivalence is substitutive under parallel operator on the right:
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (par E E'') (par E' E''))
 *)
val STRONG_EQUIV_SUBST_PAR_R = save_thm (
   "STRONG_EQUIV_SUBST_PAR_R",
    Q_GENL [`E`, `E'`]
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_PAR
             (CONJ (ASSUME ``STRONG_EQUIV E E'``)
                   (ASSUME ``STRONG_EQUIV E'' E''``)))))))));

(* Strong equivalence is substitutive under parallel operator on the left:
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (par E'' E) (par E'' E'))
 *)
val STRONG_EQUIV_SUBST_PAR_L = save_thm (
   "STRONG_EQUIV_SUBST_PAR_L",
    Q_GENL [`E`, `E'`]
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_PAR
             (CONJ (ASSUME ``STRONG_EQUIV E'' E''``)
                   (ASSUME ``STRONG_EQUIV E E'``)))))))));

(* Strong equivalence is substitutive under restriction operator. *)
val STRONG_EQUIV_SUBST_RESTR = store_thm (
   "STRONG_EQUIV_SUBST_RESTR",
      ``!E E'.
         STRONG_EQUIV E E' ==>
         (!L. STRONG_EQUIV (restr L E) (restr L E'))``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\x y. ?E1 E2 L'. (x = restr L' E1) /\ (y = restr L' E2) /\
                                  STRONG_EQUIV E1 E2``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`, `L`] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = restr L' E1``]
                                 (ASSUME ``TRANS E'' u E1'``)) \\
        IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV E1 E2``)) \\
          EXISTS_TAC ``restr (L' :'b Label set) E2'`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC RESTR \\
            REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = tau``]
                                      (ASSUME ``TRANS E2 u E2'``)],
            (* goal 2.1.1.2 (of 2) *)
            take [`E''''`, `E2'`, `L'`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.1.2 (of 2) *)
          IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                         (ASSUME ``STRONG_EQUIV E1 E2``)) \\
          EXISTS_TAC ``restr (L' :'b Label set) E2'`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC RESTR \\
            EXISTS_TAC ``l: 'b Label`` \\
            ASM_REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = label l``]
                                          (ASSUME ``TRANS E2 u E2'``)],
            (* goal 2.1.2.2 (of 2) *)
            take [`E''''`, `E2'`, `L'`] \\
            ASM_REWRITE_TAC [] ] ],
          (* goal 2.2 (of 2) *)
          ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = restr L' E2``]
                                   (ASSUME ``TRANS E''' u E2'``)) \\
          IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
          [ (* goal 2.2.1 (of 2) *)
            IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                           (ASSUME ``STRONG_EQUIV E1 E2``)) \\
            EXISTS_TAC ``restr (L' :'b Label set) E1'`` \\
            CONJ_TAC >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.1 (of 2) *)
              ASM_REWRITE_TAC [] \\
              MATCH_MP_TAC RESTR \\
              REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = tau``]
                                        (ASSUME ``TRANS E1 u E1'``)],
              (* goal 2.2.1.2 (of 2) *)
              take [`E1'`, `E''''`, `L'`] \\
              ASM_REWRITE_TAC [] ],
           (* goal 2.2.2 (of 2) *)
           IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                          (ASSUME ``STRONG_EQUIV E1 E2``)) \\
           EXISTS_TAC ``restr (L' :'b Label set) E1'`` \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.2.1 (of 2) *)
             ASM_REWRITE_TAC [] \\
             MATCH_MP_TAC RESTR \\
             EXISTS_TAC ``l: 'b Label`` \\
             ASM_REWRITE_TAC [REWRITE_RULE [ASSUME ``(u :'b Action) = label l``]
                                           (ASSUME ``TRANS E1 u E1'``)],
             (* goal 2.2.2.2 (of 2) *)
             take [`E1'`, `E''''`, `L'`] \\
             ASM_REWRITE_TAC [] ] ] ] ]);

(* Strong equivalence is substitutive under relabelling operator. *)
val STRONG_EQUIV_SUBST_RELAB = store_thm (
   "STRONG_EQUIV_SUBST_RELAB",
      ``!E E'.
         STRONG_EQUIV E E' ==>
         (!rf. STRONG_EQUIV (relab E rf) (relab E' rf))``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\x y. ?E1 E2 rf'. (x = relab E1 rf') /\ (y = relab E2 rf') /\
                                   STRONG_EQUIV E1 E2``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      BETA_TAC \\
      take [`E`, `E'`, `rf`] \\
      ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      PURE_ONCE_REWRITE_TAC [STRONG_BISIM] \\
      BETA_TAC \\
      REPEAT STRIP_TAC >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E'' = relab E1 rf'``]
                                 (ASSUME ``TRANS E'' u E1'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                       (ASSUME ``STRONG_EQUIV E1 E2``)) \\
        EXISTS_TAC ``relab E2' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC RELABELING \\
          PURE_ONCE_ASM_REWRITE_TAC [],
          (* goal 2.1.2 (of 2) *)
          take [`E''''`, `E2'`, `rf'`] \\
          ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
                                 (ASSUME ``TRANS E''' u E2'``)) \\
        IMP_RES_TAC TRANS_RELAB \\
        IMP_RES_TAC (ONCE_REWRITE_RULE [PROPERTY_STAR]
                                       (ASSUME ``STRONG_EQUIV E1 E2``)) \\
        EXISTS_TAC ``relab E1' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC RELABELING \\
          PURE_ONCE_ASM_REWRITE_TAC [],
          (* goal 2.2.2 (of 2) *)
          take [`E1'`, `E''''`, `rf'`] \\
          ASM_REWRITE_TAC [] ] ] ]);

val _ = export_theory ();
val _ = html_theory "StrongEQ";
