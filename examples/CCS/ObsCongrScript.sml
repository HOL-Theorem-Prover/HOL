(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open pred_setTheory relationTheory;

open CCSLib CCSTheory StrongEQTheory StrongLawsTheory
     WeakEQTheory WeakEQLib WeakLawsTheory;

val _ = new_theory "ObsCongr";
val _ = temp_loose_equality ();

(******************************************************************************)
(*                                                                            *)
(*          Operational definition of observation congruence for CCS          *)
(*                  and related properties                                    *)
(*                                                                            *)
(******************************************************************************)

(* Define the observation congruence over CCS agents expressions. *)
val OBS_CONGR = new_definition ("OBS_CONGR",
  ``OBS_CONGR (E :'a CCS) (E' :'a CCS) =
       (!(u :'a Action).
         (!E1. TRANS E u E1 ==>
               ?E2. WEAK_TRANS E' u E2 /\ WEAK_EQUIV E1 E2) /\
         (!E2. TRANS E' u E2 ==>
               ?E1. WEAK_TRANS E  u E1 /\ WEAK_EQUIV E1 E2))``);

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Infix (NONASSOC, 450),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK (UTF8.chr 0x2248 ^ UTF8.chr 0x1D9C),
                                  BreakSpace (1,0)],
                   term_name = "OBS_CONGR" }

val _ = TeX_notation { hol = UTF8.chr 0x2248 ^ UTF8.chr 0x1D9C,
                       TeX = ("\\HOLTokenObsCongr", 1) };

val OBS_CONGR_TRANS_LEFT = store_thm (
   "OBS_CONGR_TRANS_LEFT",
  ``!E E'. OBS_CONGR (E :'a CCS) (E' :'a CCS) ==>
           !u E1. TRANS E u E1 ==>
                  ?E2. WEAK_TRANS E' u E2 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [OBS_CONGR]);

val OBS_CONGR_TRANS_RIGHT = store_thm (
   "OBS_CONGR_TRANS_RIGHT",
  ``!E E'. OBS_CONGR (E :'a CCS) (E' :'a CCS) ==>
           !u E2. TRANS E' u E2 ==>
                  ?E1. WEAK_TRANS E  u E1 /\ WEAK_EQUIV E1 E2``,
    PROVE_TAC [OBS_CONGR]);

(* Prove that observation congruence implies observation equivalence. *)
val OBS_CONGR_IMP_WEAK_EQUIV = store_thm (
   "OBS_CONGR_IMP_WEAK_EQUIV", ``!E E'. OBS_CONGR E E' ==> WEAK_EQUIV E E'``,
    REPEAT GEN_TAC
 >> ONCE_REWRITE_TAC [OBS_CONGR, WEAK_PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 4 sub-goals here, sharing initial & end tactical *)
 >> RES_TAC
 >| [ Q.EXISTS_TAC `E2`,
      Q.EXISTS_TAC `E1`,
      IMP_RES_TAC WEAK_TRANS_IMP_EPS >> Q.EXISTS_TAC `E2`,
      IMP_RES_TAC WEAK_TRANS_IMP_EPS >> Q.EXISTS_TAC `E1` ]
 >> ASM_REWRITE_TAC []);

val WEAK_EQUIV_STABLE_IMP_CONGR = store_thm (
   "WEAK_EQUIV_STABLE_IMP_CONGR",
  ``!E E'. WEAK_EQUIV E E' /\ STABLE E /\ STABLE E' ==> OBS_CONGR E E'``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [STABLE, OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC Action_no_tau_is_Label \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u :'a Action) = label x``]
                               (ASSUME ``TRANS E u E1``)) \\
      IMP_RES_TAC
        (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                      (ASSUME ``WEAK_EQUIV E E'``))) \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      RES_TAC THEN IMP_RES_TAC Action_no_tau_is_Label \\
      ASSUME_TAC (REWRITE_RULE [ASSUME ``(u :'a Action) = label x``]
                               (ASSUME ``TRANS E' u E2``)) \\
      IMP_RES_TAC
        (CONJUNCT1 (ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                      (ASSUME ``WEAK_EQUIV E E'``))) \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ]);

(******************************************************************************)
(*                                                                            *)
(*             Observation congruence is an equivalence relation              *)
(*                                                                            *)
(******************************************************************************)

(* Observation congruence is a reflexive relation. *)
val OBS_CONGR_REFL = store_thm (
   "OBS_CONGR_REFL", ``!E. OBS_CONGR E E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here, sharing begin & end tacticals *)
 >> IMP_RES_TAC TRANS_IMP_WEAK_TRANS
 >| [ (* goal 1 (of 2) *) Q.EXISTS_TAC `E1`,
      (* goal 2 (of 2) *) Q.EXISTS_TAC `E2` ]
 >> ASM_REWRITE_TAC [WEAK_EQUIV_REFL]);

(* Observation congruence is a symmetric relation. *)
val OBS_CONGR_SYM = store_thm (
   "OBS_CONGR_SYM", ``!E E'. OBS_CONGR E E' ==> OBS_CONGR E' E``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here, sharing begin & end tacticals *)
 >> RES_TAC
 >> IMP_RES_TAC WEAK_EQUIV_SYM
 >| [ (* goal 1 (of 2) *) Q.EXISTS_TAC `E1'`,
      (* goal 1 (of 2) *) Q.EXISTS_TAC `E2'` ]
 >> ASM_REWRITE_TAC []);

(* Syntactic equivalence implies observation congruence. *)
val EQUAL_IMP_OBS_CONGR = store_thm (
   "EQUAL_IMP_OBS_CONGR", ``!E E'. (E = E') ==> OBS_CONGR E E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [OBS_CONGR_REFL]);

val OBS_CONGR_EPS = store_thm ((* NEW *)
   "OBS_CONGR_EPS",
  ``!E E'. OBS_CONGR E E' ==>
          (!E1. EPS E E1 ==> ?E2. EPS E' E2 /\ WEAK_EQUIV E1 E2)``,
    rpt GEN_TAC
 >> DISCH_TAC
 >> MATCH_MP_TAC WEAK_EQUIV_EPS
 >> IMP_RES_TAC OBS_CONGR_IMP_WEAK_EQUIV);

(* Lemma: in any case, `WEAK_TRANS E u E1` implies at least one real transition,
   it then leads to `WEAK_TRANS E' u E2` on the other side.

   Case 1 (u = tau):        |    Case 2 (u = label L)
============================================================
     !E     ~~c   !E'       |       !E    ~~c   !E'
   ||   |       ||   ||     |    ||   ||      ||   ||
   ||   |       ||   ||     |    ||   eps     eps  ||
   ||  tau      tau  ||     |    ||   ||      ||   ||
   ||   |       ||   ||     |    ||   \/      \/   ||
   ||   |       ||   ||     |    ||  ?E1' ~~ ?E2' (lemma 1)
   ||   \/      \/   ||     |    ||   |       ||   ||
  tau  ?E1' ~~ ?E2   tau    |    L    L       L    L
   ||   ||      ||   ||     |    ||   |       ||   ||
   ||   ||      ||   ||     |    ||   \/      \/   ||
   ||   eps     eps  ||     |    ||  ?E2  ~~ ?E2'' ||
   ||   ||      ||   ||     |    ||   ||      ||   ||
   ||   ||      ||   ||     |    ||  eps      eps  ||
   ||   ||      ||   ||     |    ||   ||      ||   ||
   \/   \/      \/   \/     |    \/   \/      \/   \/
     !E1    ~~    ?E2'      |      !E1    ~~   ?E2'''
 *)
val OBS_CONGR_WEAK_TRANS = store_thm ((* NEW *)
   "OBS_CONGR_WEAK_TRANS",
  ``!E E'. OBS_CONGR E E' ==>
        (!u E1. WEAK_TRANS E u E1 ==> ?E2. WEAK_TRANS E' u E2 /\ WEAK_EQUIV E1 E2)``,
    REPEAT STRIP_TAC
 >> Cases_on `u` (* 2 sub-goals here *)
 >| [ (* case 1 (of 2): u = tau *)
      IMP_RES_TAC WEAK_TRANS_TAU_IMP_TRANS_TAU \\
      IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E E'``)) \\
      IMP_RES_TAC (REWRITE_RULE [WEAK_EQUIV_IS_WEAK_BISIM]
                       (Q.SPECL [`WEAK_EQUIV`, `E2`]
                                (MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E1' E1``)))) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      ASSUME_TAC (Q.SPEC `E'` EPS_REFL) \\
      IMP_RES_TAC EPS_WEAK_EPS,
      (* case 2 (of 2): ~(u = tau) *)
      IMP_RES_TAC WEAK_TRANS \\
      IMP_RES_TAC (MATCH_MP OBS_CONGR_EPS (* lemma 1 used here *)
                            (ASSUME ``OBS_CONGR E E'``)) \\
      IMP_RES_TAC (CONJUNCT1
                       (PURE_ONCE_REWRITE_RULE [WEAK_PROPERTY_STAR]
                                               (ASSUME ``WEAK_EQUIV E1' E2'``))) \\
      IMP_RES_TAC (REWRITE_RULE [WEAK_EQUIV_IS_WEAK_BISIM]
                       (Q.SPECL [`WEAK_EQUIV`, `E2''`]
                                (MATCH_MP EPS_TRANS_AUX (ASSUME ``EPS E2 E1``)))) \\
      Q.EXISTS_TAC `E2'''` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC EPS_WEAK_EPS ]);

(* Observation congruence is a transitive relation.

               +-------- ~~ ------+  --->  (sub-goal 1)
               |                  |             ||
              !E1  ~~   ?E2  ~~  ?E3 (lemma 2)  ||
               /\        /\       /\            ||
               |         ||       ||            ||
              !u         u        u             \/
               |         ||       ||
               E   ~~c   E'  ~~c  E''   ==>   E ~~c E'' (goal)
            ||  ||     |  ||      |
            ||   u     u  ||      |             /\
            u   ||     |   u     !u             ||
            ||  \/     \/ ||      |             ||
            || ?E1 ~~ !E2 ||      |             ||
            \/            \/      \/            ||
 (lemma 2) ?E1'    ~~    ?E2' ~~ !E3            ||
            |                     |             ||
            +--------- ~~ --------+  --->  (sub-goal 2)
 *)
val OBS_CONGR_TRANS = store_thm ((* NEW *)
   "OBS_CONGR_TRANS",
  ``!E E' E''. OBS_CONGR E E' /\ OBS_CONGR E' E'' ==> OBS_CONGR E E''``,
    REPEAT STRIP_TAC
 >> REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E E'``)) \\
      IMP_RES_TAC (MATCH_MP OBS_CONGR_WEAK_TRANS (* lemma 2 used here *)
                            (ASSUME ``OBS_CONGR E' E''``)) \\
      Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC [] \\
      IMP_RES_TAC WEAK_EQUIV_TRANS,
      (* goal 2 (of 2) *)
      IMP_RES_TAC OBS_CONGR_SYM \\
      IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E'' E'``)) \\
      IMP_RES_TAC (MATCH_MP OBS_CONGR_WEAK_TRANS (* lemma 2 used here *)
                            (ASSUME ``OBS_CONGR E' E``)) \\
      Q.EXISTS_TAC `E2''` >> ASM_REWRITE_TAC [] \\
      MATCH_MP_TAC WEAK_EQUIV_SYM \\
      IMP_RES_TAC WEAK_EQUIV_TRANS ]);

val OBS_CONGR_equivalence = store_thm ((* NEW *)
   "OBS_CONGR_equivalence", ``equivalence OBS_CONGR``,
    REWRITE_TAC [equivalence_def]
 >> REPEAT STRIP_TAC (* 3 sub-goals here *)
 >| [ (* goal 1 (of 3) *)
      REWRITE_TAC [reflexive_def, OBS_CONGR_REFL],
      (* goal 2 (of 3) *)
      REWRITE_TAC [symmetric_def] \\
      REPEAT GEN_TAC \\
      EQ_TAC >> REWRITE_TAC [OBS_CONGR_SYM],
      (* goal 3 (of 3) *)
      REWRITE_TAC [transitive_def, OBS_CONGR_TRANS] ]);

(******************************************************************************)
(*                                                                            *)
(*            Substitutive properties of observation congruence               *)
(*                                                                            *)
(******************************************************************************)

(* Proposition 6 (Milner's book, page 154). *)
val PROP6 = store_thm ("PROP6",
  ``!E E'. WEAK_EQUIV E E' ==> !u. OBS_CONGR (prefix u E) (prefix u E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E'` \\
      ASM_REWRITE_TAC [WEAK_TRANS] \\
      EXISTS_TAC ``prefix (u :'a Action) E'`` \\
      Q.EXISTS_TAC `E'` \\
      ASM_REWRITE_TAC [EPS_REFL, PREFIX],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PREFIX \\
      Q.EXISTS_TAC `E` \\
      ASM_REWRITE_TAC [WEAK_TRANS] \\
      EXISTS_TAC ``prefix (u :'a Action) E`` \\
      Q.EXISTS_TAC `E` \\
      ASM_REWRITE_TAC [EPS_REFL, PREFIX] ]);

(* Observation congruence is substitutive under the prefix operator. *)
val OBS_CONGR_SUBST_PREFIX = store_thm (
   "OBS_CONGR_SUBST_PREFIX",
  ``!E E'. OBS_CONGR E E' ==> !u. OBS_CONGR (prefix u E) (prefix u E')``,
    REPEAT STRIP_TAC
 >> IMP_RES_TAC OBS_CONGR_IMP_WEAK_EQUIV
 >> IMP_RES_TAC PROP6
 >> ASM_REWRITE_TAC []);

(* Observation congruence is substitutive under binary summation. *)
val OBS_CONGR_PRESD_BY_SUM = store_thm (
   "OBS_CONGR_PRESD_BY_SUM",
  ``!E1 E1' E2 E2'. OBS_CONGR E1 E1' /\ OBS_CONGR E2 E2' ==>
                    OBS_CONGR (sum E1 E2) (sum E1' E2')``,
    rpt STRIP_TAC
 >> REWRITE_TAC [OBS_CONGR]
 >> rpt STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        IMP_RES_TAC OBS_CONGR_TRANS_LEFT \\
        Q.EXISTS_TAC `E2''` >> art [] \\
        MATCH_MP_TAC WEAK_SUM1 >> art [],
        (* goal 1.2 (of 2) *)
        IMP_RES_TAC OBS_CONGR_TRANS_LEFT \\
        Q.EXISTS_TAC `E2''` >> art [] \\
        MATCH_MP_TAC WEAK_SUM2 >> art [] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_SUM >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        IMP_RES_TAC OBS_CONGR_TRANS_RIGHT \\
        Q.EXISTS_TAC `E1''` >> art [] \\
        MATCH_MP_TAC WEAK_SUM1 >> art [],
        (* goal 2.2 (of 2) *)
        IMP_RES_TAC OBS_CONGR_TRANS_RIGHT \\
        Q.EXISTS_TAC `E1''` >> art [] \\
        MATCH_MP_TAC WEAK_SUM2 >> art [] ] ]);

(* Observation congruence is substitutive under binary summation on the left:
   !E E'. OBS_CONGR E E' ==> !E''. OBS_CONGR (sum E'' E) (sum E'' E')
 *)
val OBS_CONGR_SUBST_SUM_L = save_thm (
   "OBS_CONGR_SUBST_SUM_L",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_CONGR E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_CONGR_PRESD_BY_SUM
                   (CONJ (Q.SPEC `E''` OBS_CONGR_REFL)
                         (ASSUME ``OBS_CONGR E E'``))))));

(* Observation congruence is substitutive under binary summation on the right:
   !E E'. OBS_CONGR E E' ==> !E''. OBS_CONGR (sum E E'') (sum E' E'')
 *)
val OBS_CONGR_SUBST_SUM_R = save_thm (
   "OBS_CONGR_SUBST_SUM_R",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_CONGR E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_CONGR_PRESD_BY_SUM
                   (CONJ (ASSUME ``OBS_CONGR E E'``)
                         (Q.SPEC `E''` OBS_CONGR_REFL))))));

(* Observation congruence is preserved by parallel composition. *)
val OBS_CONGR_PRESD_BY_PAR = store_thm (
   "OBS_CONGR_PRESD_BY_PAR",
  ``!E1 E1' E2 E2'. OBS_CONGR E1 E1' /\ OBS_CONGR E2 E2' ==>
                    OBS_CONGR (par E1 E2) (par E1' E2')``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 1.1 (of 3) *)
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                                  (ASSUME ``OBS_CONGR E1 E1'``)) \\
        ASSUME_TAC (CONJUNCT1
                     (Q.SPEC `E2'`
                        (MATCH_MP WEAK_PAR (ASSUME ``WEAK_TRANS E1' u E2''``)))) \\
        EXISTS_TAC ``par E2'' E2'`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E2`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (ASSUME ``WEAK_EQUIV E1''' E2''``)))
                    (Q.SPEC `E2''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (MATCH_MP OBS_CONGR_IMP_WEAK_EQUIV
                                           (ASSUME ``OBS_CONGR E2 E2'``))))],
        (* goal 1.2 (of 3) *)
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                                  (ASSUME ``OBS_CONGR E2 E2'``)) \\
        ASSUME_TAC (CONJUNCT2
                     (Q.SPEC `E1'`
                        (MATCH_MP WEAK_PAR (ASSUME ``WEAK_TRANS E2' u E2''``)))) \\
        EXISTS_TAC ``par E1' E2''`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E1'''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (MATCH_MP OBS_CONGR_IMP_WEAK_EQUIV
                                           (ASSUME ``OBS_CONGR E1 E1'``))))
                    (Q.SPEC `E1'`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (ASSUME ``WEAK_EQUIV E1''' E2''``)))],
        (* goal 1.3 (of 3) *)
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E1 E1'``)) \\
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E2 E2'``)) \\
        EXISTS_TAC ``par E2''' E2''''`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E2''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (ASSUME ``WEAK_EQUIV E1''' E2'''``)))
                    (Q.SPEC `E2'''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (ASSUME ``WEAK_EQUIV E2'' E2''''``)))] \\
        PURE_ONCE_REWRITE_TAC [WEAK_TRANS] \\
        STRIP_ASSUME_TAC
          (REWRITE_RULE [WEAK_TRANS]
                        (ASSUME ``WEAK_TRANS E1' (label l) E2'''``)) \\
        STRIP_ASSUME_TAC
          (REWRITE_RULE [WEAK_TRANS]
                        (ASSUME ``WEAK_TRANS E2' (label (COMPL l)) E2''''``)) \\
        EXISTS_TAC ``par E1'''' E1'''''`` \\
        EXISTS_TAC ``par E2''''' E2''''''`` \\
        REWRITE_TAC
          [MATCH_MP EPS_PAR_PAR
                    (CONJ (ASSUME ``EPS E1' E1''''``)
                          (ASSUME ``EPS E2' E1'''''``)),
           MATCH_MP EPS_PAR_PAR
                    (CONJ (ASSUME ``EPS E2''''' E2'''``)
                          (ASSUME ``EPS E2'''''' E2''''``))] \\
        MATCH_MP_TAC PAR3 \\
        EXISTS_TAC ``l :'a Label`` >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_PAR >| (* 3 sub-goals here *)
      [ (* goal 2.1 (of 3) *)
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR] (ASSUME ``OBS_CONGR E1 E1'``)) \\
        ASSUME_TAC (CONJUNCT1
                     (Q.SPEC `E2`
                        (MATCH_MP WEAK_PAR (ASSUME ``WEAK_TRANS E1 u E1'''``)))) \\
        EXISTS_TAC ``par E1''' E2`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E2`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (ASSUME ``WEAK_EQUIV E1''' E1''``)))
                    (Q.SPEC `E1''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (MATCH_MP OBS_CONGR_IMP_WEAK_EQUIV
                                           (ASSUME ``OBS_CONGR E2 E2'``))))],
        (* goal 2.2 (of 3) *)
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                                  (ASSUME ``OBS_CONGR E2 E2'``)) \\
        ASSUME_TAC (CONJUNCT2
                     (Q.SPEC `E1`
                        (MATCH_MP WEAK_PAR (ASSUME ``WEAK_TRANS E2 u E1'''``)))) \\
        EXISTS_TAC ``par E1 E1'''`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E1'''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (MATCH_MP OBS_CONGR_IMP_WEAK_EQUIV
                                           (ASSUME ``OBS_CONGR E1 E1'``))))
                    (Q.SPEC `E1'`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (ASSUME ``WEAK_EQUIV E1''' E1''``)))],
        (* goal 2.3 (of 3) *)
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                                  (ASSUME ``OBS_CONGR E1 E1'``)) \\
        IMP_RES_TAC (REWRITE_RULE [OBS_CONGR]
                                  (ASSUME ``OBS_CONGR E2 E2'``)) \\
        EXISTS_TAC ``par E1''' E1''''`` \\
        ASM_REWRITE_TAC
          [OE_TRANS (Q.SPEC `E1''''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_R
                                 (ASSUME ``WEAK_EQUIV E1''' E1''``)))
                    (Q.SPEC `E1''`
                       (MATCH_MP WEAK_EQUIV_SUBST_PAR_L
                                 (ASSUME ``WEAK_EQUIV E1'''' E2'''``)))] \\
        PURE_ONCE_REWRITE_TAC [WEAK_TRANS] \\
        STRIP_ASSUME_TAC
          (REWRITE_RULE [WEAK_TRANS]
                        (ASSUME ``WEAK_TRANS E1 (label l) E1'''``)) \\
        STRIP_ASSUME_TAC
          (REWRITE_RULE [WEAK_TRANS]
                        (ASSUME ``WEAK_TRANS E2 (label (COMPL l)) E1''''``)) \\
        EXISTS_TAC ``par E1''''' E1''''''`` \\
        EXISTS_TAC ``par E2'''' E2'''''`` \\
        REWRITE_TAC
          [MATCH_MP EPS_PAR_PAR
                    (CONJ (ASSUME ``EPS E1 E1'''''``)
                          (ASSUME ``EPS E2 E1''''''``)),
           MATCH_MP EPS_PAR_PAR
                    (CONJ (ASSUME ``EPS E2'''' E1'''``)
                          (ASSUME ``EPS E2''''' E1''''``))] \\
        MATCH_MP_TAC PAR3 \\
        EXISTS_TAC ``l :'a Label`` >> ASM_REWRITE_TAC [] ] ]);

(* Observation congruence is substitutive under parallel operator on the left:
   !E E'. OBS_CONGR E E' ==> (!E''. OBS_CONGR (par E'' E) (par E'' E'))
 *)
val OBS_CONGR_SUBST_PAR_L = save_thm (
   "OBS_CONGR_SUBST_PAR_L",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_CONGR E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_CONGR_PRESD_BY_PAR
                   (CONJ (Q.SPEC `E''` OBS_CONGR_REFL)
                         (ASSUME ``OBS_CONGR E E'``))))));

(* Observation congruence is substitutive under parallel operator on the right:
   !E E'. OBS_CONGR E E' ==> (!E''. OBS_CONGR (par E E'') (par E' E''))
 *)
val OBS_CONGR_SUBST_PAR_R = save_thm (
   "OBS_CONGR_SUBST_PAR_R",
    Q.GENL [`E`, `E'`]
       (DISCH ``OBS_CONGR E E'``
        (Q.GEN `E''`
         (MATCH_MP OBS_CONGR_PRESD_BY_PAR
                   (CONJ (ASSUME ``OBS_CONGR E E'``)
                         (Q.SPEC `E''` OBS_CONGR_REFL))))));

(* Observation congruence is substitutive under the restriction operator. *)
val OBS_CONGR_SUBST_RESTR = store_thm (
   "OBS_CONGR_SUBST_RESTR",
  ``!E E'. OBS_CONGR E E' ==> !L. OBS_CONGR (restr L E) (restr L E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 1.1 (of 2) *)
        RES_TAC \\
        ASSUME_TAC
          (MATCH_MP WEAK_RESTR_tau
                    (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                                  (ASSUME ``WEAK_TRANS E' u E2``))) \\
        EXISTS_TAC ``restr (L :'a Label set) E2`` \\
        IMP_RES_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [],
        (* goal 1.2 (of 2) *)
        RES_TAC \\
        ASSUME_TAC
          (MATCH_MP WEAK_RESTR_label
                    (LIST_CONJ [ASSUME ``~((l :'a Label) IN L)``,
                                ASSUME ``~((COMPL (l :'a Label)) IN L)``,
                                REWRITE_RULE [ASSUME ``(u :'a Action) = label l``]
                                             (ASSUME ``WEAK_TRANS E' u E2``)])) \\
        EXISTS_TAC ``restr (L :'a Label set) E2`` \\
        IMP_RES_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
      [ (* goal 2.1 (of 2) *)
        RES_TAC \\
        ASSUME_TAC
          (MATCH_MP WEAK_RESTR_tau
                    (REWRITE_RULE [ASSUME ``(u :'a Action) = tau``]
                                  (ASSUME ``WEAK_TRANS E u E1``))) \\
        EXISTS_TAC ``restr (L :'a Label set) E1`` \\
        IMP_RES_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [],
        (* goal 2.2 (of 2) *)
        RES_TAC \\
        ASSUME_TAC
          (MATCH_MP WEAK_RESTR_label
                    (LIST_CONJ [ASSUME ``~((l :'a Label) IN L)``,
                                ASSUME ``~((COMPL (l :'a Label)) IN L)``,
                                REWRITE_RULE [ASSUME ``(u :'a Action) = label l``]
                                             (ASSUME ``WEAK_TRANS E u E1``)])) \\
        EXISTS_TAC ``restr (L :'a Label set) E1`` \\
        IMP_RES_TAC WEAK_EQUIV_SUBST_RESTR >> ASM_REWRITE_TAC [] ] ]);

(* Observation congruence is substitutive under the relabelling operator. *)
val OBS_CONGR_SUBST_RELAB = store_thm (
   "OBS_CONGR_SUBST_RELAB",
  ``!E E'. OBS_CONGR E E' ==> !rf. OBS_CONGR (relab E rf) (relab E' rf)``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here, sharing start&end tacticals *)
 >> IMP_RES_TAC TRANS_RELAB
 >> RES_TAC
 >| [ (* goal 1 (of 2) *)
      ASSUME_TAC (MATCH_MP WEAK_RELAB_rf
                           (ASSUME ``WEAK_TRANS E' u' E2``)) \\
      EXISTS_TAC ``relab E2 rf``,
      (* goal 2 (of 2) *)
      ASSUME_TAC (MATCH_MP WEAK_RELAB_rf
                           (ASSUME ``WEAK_TRANS E u' E1``)) \\
      EXISTS_TAC ``relab E1 rf`` ]
 >> IMP_RES_TAC WEAK_EQUIV_SUBST_RELAB
 >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*     Relationship between strong equivalence and observation congruence     *)
(*                                                                            *)
(******************************************************************************)

(* Prove that strong equivalence implies observation congruence. *)
val STRONG_IMP_OBS_CONGR = store_thm (
   "STRONG_IMP_OBS_CONGR", ``!E E'. STRONG_EQUIV E E' ==> OBS_CONGR E E'``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [PROPERTY_STAR, OBS_CONGR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
      IMP_RES_TAC STRONG_IMP_WEAK_EQUIV \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      RES_TAC \\
      IMP_RES_TAC TRANS_IMP_WEAK_TRANS \\
      IMP_RES_TAC STRONG_IMP_WEAK_EQUIV \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] ]);

(* `EPS E E1` implies zero or more tau transitions, and this leads to
   zero or at least one tau transition on the other side, which implies
   `EPS E' E2` in any case.

    (Base case)    |     (Induct case)
 ==========================================
    !E  ~~c !E'    |    !E  ~~c  !E'
     |       |     |    ||       ||   ||
     =       =     |    eps      eps  ||
     |       |     |    ||       ||   ||
     E  ~~  ?E'    |    \/       \/   ||
                   |    E1  ~~   ?E2  eps
                   |    |        ||   ||
                   |    tau      tau  ||
                   |    |        ||   ||
                   |    \/       \/   \/
                   |    E1'  ~~    ?E2'
 *)

val OBS_CONGR_EPS' = store_thm ((* NEW *)
   "OBS_CONGR_EPS'",
  ``!E E'. OBS_CONGR E E' ==>
           !E2. EPS E' E2 ==> ?E1. EPS E E1 /\ WEAK_EQUIV E1 E2``,
    rpt GEN_TAC >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP OBS_CONGR_SYM))
 >> IMP_RES_TAC OBS_CONGR_EPS
 >> POP_ASSUM MP_TAC
 >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC WEAK_EQUIV_SYM);

val OBS_CONGR_WEAK_TRANS' = store_thm ((* NEW *)
   "OBS_CONGR_WEAK_TRANS'",
  ``!E E'. OBS_CONGR E E' ==>
           !u E2. WEAK_TRANS E' u E2 ==> ?E1. WEAK_TRANS E u E1 /\ WEAK_EQUIV E1 E2``,
    REPEAT GEN_TAC
 >> DISCH_TAC
 >> POP_ASSUM (ASSUME_TAC o (MATCH_MP OBS_CONGR_SYM))
 >> IMP_RES_TAC OBS_CONGR_WEAK_TRANS
 >> POP_ASSUM MP_TAC
 >> rpt STRIP_TAC
 >> RES_TAC
 >> Q.EXISTS_TAC `E2'` >> ASM_REWRITE_TAC []
 >> IMP_RES_TAC WEAK_EQUIV_SYM);

(******************************************************************************)
(*                                                                            *)
(*              Proving OBS_CONGR by constructing a WEAK_BISIM !              *)
(*                                                                            *)
(******************************************************************************)

(* This beautiful result is learnt from Prof. Davide Sangiorgi *)
val OBS_CONGR_BY_WEAK_BISIM = store_thm (
   "OBS_CONGR_BY_WEAK_BISIM",
  ``!Wbsm. WEAK_BISIM Wbsm ==>
      !E E'.
        (!u.
         (!E1. TRANS E u E1 ==>
               (?E2. WEAK_TRANS E' u E2 /\ Wbsm E1 E2)) /\
         (!E2. TRANS E' u E2 ==>
               (?E1. WEAK_TRANS E  u E1 /\ Wbsm E1 E2))) ==> OBS_CONGR E E'``,
    rpt STRIP_TAC
 >> REWRITE_TAC [OBS_CONGR]
 >> REWRITE_TAC [WEAK_EQUIV]
 >> GEN_TAC
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      rpt STRIP_TAC >> RES_TAC \\
      Q.EXISTS_TAC `E2` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `Wbsm` >> ASM_REWRITE_TAC [],
      (* goal 2 (of 2) *)
      rpt STRIP_TAC >> RES_TAC \\
      Q.EXISTS_TAC `E1` >> ASM_REWRITE_TAC [] \\
      Q.EXISTS_TAC `Wbsm` >> ASM_REWRITE_TAC [] ]);

val _ = export_theory ();
val _ = html_theory "ObsCongr";

(* last updated: Jun 20, 2017 *)
