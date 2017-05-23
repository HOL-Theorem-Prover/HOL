(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

open HolKernel Parse boolLib bossLib;

open stringTheory pred_setTheory pairTheory relationTheory;
open CCSLib CCSTheory;

val _ = new_theory "StrongEQ";

(******************************************************************************)
(*                                                                            *)
(*    Operational definition of strong equivalence for CCS (strong_sem.ml)    *)
(*                                                                            *)
(******************************************************************************)

(* Define the strong bisimulation relation on CCS processes. *)
val STRONG_BISIM = new_definition (
   "STRONG_BISIM",
  ``STRONG_BISIM (Bsm: CCS -> CCS -> bool) =
       (!E E'.
          Bsm E E' ==>
          (!u.
           (!E1. TRANS E u E1 ==> 
                 ?E2. TRANS E' u E2 /\ Bsm E1 E2) /\
           (!E2. TRANS E' u E2 ==> 
                 ?E1. TRANS E u E1 /\ Bsm E1 E2)))``);

(* The identity relation is a strong bisimulation. *)
val IDENTITY_STRONG_BISIM = store_thm (
   "IDENTITY_STRONG_BISIM",
  ``STRONG_BISIM (\x y. x = y)``,
    PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 2 sub-goals *)
 >| [ (* goal 1 *)
      ASSUME_TAC (REWRITE_RULE [ASSUME ``E: CCS = E'``]
			       (ASSUME ``TRANS E u E1``)) \\
      EXISTS_TAC ``E1: CCS`` \\
      ASM_REWRITE_TAC [] ,
      (* goal 2 *)
      PURE_ONCE_ASM_REWRITE_TAC [] \\
      EXISTS_TAC ``E2: CCS`` \\
      ASM_REWRITE_TAC [] ]);

(* The converse of a strong bisimulation is a strong bisimulation. *)
val CONVERSE_STRONG_BISIM = store_thm (
   "CONVERSE_STRONG_BISIM",
  ``!Bsm. STRONG_BISIM Bsm ==> STRONG_BISIM (\x y. Bsm y x)``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >> RES_TAC (* enrich assumptions *)
 >| [ EXISTS_TAC ``E1': CCS``,
      EXISTS_TAC ``E2': CCS`` ]
 >> ASM_REWRITE_TAC []);

(* The composition of two strong bisimulations is a strong bisimulation. *)
val COMP_STRONG_BISIM = store_thm (
   "COMP_STRONG_BISIM",
      ``!Bsm1 Bsm2. 
         STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==>
         STRONG_BISIM (\x z. ?y. Bsm1 x y /\ Bsm2 y z)``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> BETA_TAC
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      IMP_RES_TAC 
        (MP (SPECL [``E: CCS``, ``y: CCS``]
            (ASSUME 
             ``!E E'.
               Bsm1 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm1 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm1 E1 E2)))``))
          (ASSUME ``(Bsm1: CCS -> CCS -> bool) E y``)) \\
      IMP_RES_TAC 
        (MP (SPECL [``y: CCS``, ``E': CCS``] 
            (ASSUME 
             ``!E E'.
               Bsm2 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm2 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm2 E1 E2)))``))
          (ASSUME ``(Bsm2: CCS -> CCS -> bool) y E'``)) \\
      EXISTS_TAC ``E2': CCS`` >> ASM_REWRITE_TAC [] \\
      EXISTS_TAC ``E2: CCS`` >> ASM_REWRITE_TAC [] ,
      (* goal 2 (of 2) *)
      IMP_RES_TAC
        (MP (SPECL [``y: CCS``, ``E': CCS``]
            (ASSUME 
             ``!E E'.
               Bsm2 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm2 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm2 E1 E2)))``))
          (ASSUME ``(Bsm2: CCS -> CCS -> bool) y E'``)) \\
      IMP_RES_TAC
        (MP (SPECL [``E: CCS``, ``y: CCS``]
            (ASSUME 
             ``!E E'.
               Bsm1 E E' ==>
               (!u.
                (!E1. TRANS E u E1 ==> (?E2. TRANS E' u E2 /\ Bsm1 E1 E2)) /\
                (!E2. TRANS E' u E2 ==> (?E1. TRANS E u E1 /\ Bsm1 E1 E2)))``))
          (ASSUME ``(Bsm1: CCS -> CCS -> bool) E y``)) \\
      EXISTS_TAC ``E1': CCS`` >> ASM_REWRITE_TAC [] \\
      EXISTS_TAC ``E1: CCS`` >> ASM_REWRITE_TAC [] ]);

(* The union of two strong bisimulations is a strong bisimulation. *)
val UNION_STRONG_BISIM = store_thm (
   "UNION_STRONG_BISIM",
      ``!Bsm1 Bsm2. 
         STRONG_BISIM Bsm1 /\ STRONG_BISIM Bsm2 ==>  
         STRONG_BISIM (\x y. Bsm1 x y \/ Bsm2 x y)``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> BETA_TAC 
 >> REPEAT STRIP_TAC (* 4 sub-goals here *)
 >> RES_TAC
 >| [ EXISTS_TAC ``E2: CCS``,
      EXISTS_TAC ``E1: CCS``,
      EXISTS_TAC ``E2: CCS``,
      EXISTS_TAC ``E1: CCS``]
 >> ASM_REWRITE_TAC []);

(* Define the strong equivalence relation for CCS processes.

   Two states E and E' are bisimilar (or bisimulation equivalent, denoted E ~ E',
   if there exists a bisimulation R such that (E, E') IN R.
 *)
val STRONG_EQUIV = new_definition (
   "STRONG_EQUIV",
  ``STRONG_EQUIV E E' = (?Bsm. Bsm E E' /\ STRONG_BISIM Bsm)``);

val _ = set_mapped_fixity { fixity = Infix (NONASSOC, 450),
			    tok = "~~", term_name = "STRONG_EQUIV" };

val _ = Unicode.unicode_version { u = UTF8.chr 0x223C, tmnm = "STRONG_EQUIV"};
val _ = TeX_notation { hol = UTF8.chr 0x223C,
                       TeX = ("\\HOLTokenStrongEquiv", 1) }

(* Strong equivalence is a reflexive relation. *)
val STRONG_EQUIV_REFL = store_thm (
   "STRONG_EQUIV_REFL", ``!E. STRONG_EQUIV E E``,
    GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``\x y: CCS. x = y``
 >> BETA_TAC
 >> REWRITE_TAC [IDENTITY_STRONG_BISIM]);

(* Strong equivalence is a symmetric relation. *)
val STRONG_EQUIV_SYM = store_thm (
   "STRONG_EQUIV_SYM",
  ``!E E'. STRONG_EQUIV E E' ==> STRONG_EQUIV E' E``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> REPEAT STRIP_TAC
 >> EXISTS_TAC ``\x y. (Bsm: CCS -> CCS -> bool) y x``
 >> BETA_TAC
 >> IMP_RES_TAC CONVERSE_STRONG_BISIM
 >> ASM_REWRITE_TAC [] );

(* Strong equivalence is a transitive relation. *)
val STRONG_EQUIV_TRANS = store_thm (
   "STRONG_EQUIV_TRANS",
      ``!E E' E''. 
         STRONG_EQUIV E E' /\ STRONG_EQUIV E' E'' ==> STRONG_EQUIV E E''``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> REPEAT STRIP_TAC
 >> EXISTS_TAC ``\x z. ?y. (Bsm: CCS -> CCS -> bool) x y /\
                           (Bsm': CCS -> CCS -> bool) y z``
 >> CONJ_TAC (* 2 sub-goals here *)
 >| [ BETA_TAC \\
      EXISTS_TAC ``E': CCS`` \\
      ASM_REWRITE_TAC [], 
      IMP_RES_TAC COMP_STRONG_BISIM ]);

(* Syntactic equivalence implies strong equivalence. *)
val EQUAL_IMP_STRONG_EQUIV = store_thm (
   "EQUAL_IMP_STRONG_EQUIV",
      ``!E E'. (E = E') ==> STRONG_EQUIV E E'``,
    REPEAT STRIP_TAC
 >> PURE_ASM_REWRITE_TAC [STRONG_EQUIV_REFL]);

(* Definition 3, page 91 in Milner's book. *)
val STRONG_EQUIV' = new_definition (
   "STRONG_EQUIV'",
  ``STRONG_EQUIV' E E' =
        (!u.
         (!E1. TRANS E u E1 ==> 
               (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
         (!E2. TRANS E' u E2 ==> 
               (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2)))``); 

(* Strong equivalence implies the new relation. *)
val STR_EQUIV_IMP_STR_EQUIV' = store_thm (
   "STR_EQUIV_IMP_STR_EQUIV'",
      ``!E E'. STRONG_EQUIV E E' ==> STRONG_EQUIV' E E'``,
    REPEAT GEN_TAC
 >> REWRITE_TAC [STRONG_EQUIV', STRONG_EQUIV]
 >> REPEAT STRIP_TAC (* 2 sub-goals *)
 >> IMP_RES_TAC
      (MP (SPEC_ALL
           (EQ_MP (SPEC ``Bsm: CCS -> CCS -> bool`` STRONG_BISIM)
                  (ASSUME ``STRONG_BISIM Bsm``)))
          (ASSUME ``(Bsm: CCS -> CCS -> bool) E E'``))
 >| [ EXISTS_TAC ``E2: CCS``,
      EXISTS_TAC ``E1: CCS`` ]
 >> ASM_REWRITE_TAC []
 >> EXISTS_TAC ``Bsm: CCS -> CCS -> bool``
 >> ASM_REWRITE_TAC [] ); 

(* Lemma 3, page 91 in Milner's book
   the new relation STRONG_EQUIV' is a strong bisimulation. *)
val STRONG_EQUIV_IS_STRONG_BISIM = store_thm (
   "STRONG_EQUIV_IS_STRONG_BISIM",
  ``STRONG_BISIM STRONG_EQUIV'``,
    PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >> IMP_RES_TAC 
       (EQ_MP (SPECL [``E: CCS``, ``E': CCS``] STRONG_EQUIV')
              (ASSUME ``STRONG_EQUIV' E E'``))
 >| [ EXISTS_TAC ``E2: CCS``,
      EXISTS_TAC ``E1: CCS`` ]
 >> IMP_RES_TAC STR_EQUIV_IMP_STR_EQUIV'
 >> ASM_REWRITE_TAC []);

(* The new relation implies strong equivalence. *)
val STR_EQUIV'_IMP_STR_EQUIV = store_thm (
   "STR_EQUIV'_IMP_STR_EQUIV",
      ``!E E'. STRONG_EQUIV' E E' ==> STRONG_EQUIV E E'``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``STRONG_EQUIV'``
 >> ASM_REWRITE_TAC [STRONG_EQUIV_IS_STRONG_BISIM]);

(* equivalence theorems used for rewriting *)
val STR_EQUIV'_TO_STR_EQUIV = store_thm (
   "STR_EQUIV'_TO_STR_EQUIV",
      ``!E E'. STRONG_EQUIV' E E' = STRONG_EQUIV E E'``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ REWRITE_TAC [STR_EQUIV'_IMP_STR_EQUIV],
      REWRITE_TAC [STR_EQUIV_IMP_STR_EQUIV'] ]);

(* the other direction *)
val STR_EQUIV_TO_STR_EQUIV' = save_thm (
   "STR_EQUIV_TO_STR_EQUIV'", GSYM STR_EQUIV'_TO_STR_EQUIV);

(* Prop. 4, page 91: strong equivalence satisfies property [*] *)
val PROPERTY_STAR = store_thm (
   "PROPERTY_STAR",
      ``!E E'. STRONG_EQUIV E E' =
         (!u.
           (!E1. TRANS E u E1 ==>
                 (?E2. TRANS E' u E2 /\ STRONG_EQUIV E1 E2)) /\
           (!E2. TRANS E' u E2 ==>
                 (?E1. TRANS E u E1 /\ STRONG_EQUIV E1 E2)))``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ PURE_ONCE_REWRITE_TAC 
        [ONCE_REWRITE_RULE [STRONG_EQUIV'] STR_EQUIV_IMP_STR_EQUIV'],
      PURE_ONCE_REWRITE_TAC 
        [ONCE_REWRITE_RULE [STRONG_EQUIV'] STR_EQUIV'_IMP_STR_EQUIV] ]);

val PROPERTY_STAR_LR = save_thm (
   "PROPERTY_STAR_LR", EQ_IMP_LR PROPERTY_STAR);

(* Strong equivalence is substitutive under prefix operator. *)
val STRONG_EQUIV_SUBST_PREFIX = store_thm (
   "STRONG_EQUIV_SUBST_PREFIX",
      ``!E E'. 
         STRONG_EQUIV E E' ==> !u. STRONG_EQUIV (prefix u E) (prefix u E')``,
    REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC 
      [SPECL [``prefix u E``, ``prefix u E'``] PROPERTY_STAR]
 >> REPEAT STRIP_TAC (* 2 sub-goals here *)
 >| [ EXISTS_TAC ``E': CCS``,
      EXISTS_TAC ``E: CCS``]
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
      EXISTS_TAC ``E2'': CCS`` \\
      ASM_REWRITE_TAC []
      >| [ MATCH_MP_TAC SUM1, MATCH_MP_TAC SUM2 ] \\
      ASM_REWRITE_TAC [],
      (* goal 2 *)
      IMP_RES_TAC TRANS_SUM \\ (* 2 sub-goals here *)
      RES_TAC \\
      EXISTS_TAC ``E1'': CCS`` \\
      ASM_REWRITE_TAC []
      >| [ MATCH_MP_TAC SUM1, MATCH_MP_TAC SUM2] \\
      ASM_REWRITE_TAC [] ]);

(* Strong equivalence is substitutive under summation operator on the right.
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (sum E E'') (sum E' E''))
 *)
val STRONG_EQUIV_SUBST_SUM_R = save_thm (
   "STRONG_EQUIV_SUBST_SUM_R",
      GEN_ALL
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM 
             (CONJ (ASSUME ``STRONG_EQUIV E E'``)
                   (ASSUME ``STRONG_EQUIV E'' E''``)))))))));

(* Strong equivalence is substitutive under summation operator on the left.
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (sum E'' E) (sum E'' E'))
 *)
val STRONG_EQUIV_SUBST_SUM_L = save_thm (
   "STRONG_EQUIV_SUBST_SUM_L",
      GEN_ALL
       (DISCH_ALL
        (GEN_ALL
         (UNDISCH
          (REWRITE_RULE [STRONG_EQUIV_REFL]
           (DISCH_ALL
            (MATCH_MP STRONG_EQUIV_PRESD_BY_SUM 
             (CONJ (ASSUME ``STRONG_EQUIV E'' E''``)
                   (ASSUME ``STRONG_EQUIV E E'``)))))))));

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
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
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
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
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
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME ``STRONG_EQUIV F1 F2``)) \\
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                       (ASSUME ``STRONG_EQUIV F3 F4``)) \\
          EXISTS_TAC ``par E2''' E2''''`` \\
          ASM_REWRITE_TAC [] \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.3.1 (of 2) *)
            MATCH_MP_TAC PAR3 \\
            EXISTS_TAC ``l: Label`` \\
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
           IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
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
           IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
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
           IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR
                        (ASSUME ``STRONG_EQUIV F1 F2``)) \\
           IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR 
                        (ASSUME ``STRONG_EQUIV F3 F4``)) \\
           EXISTS_TAC ``par E1''' E1''''`` \\
           ASM_REWRITE_TAC [] \\
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.3.1 (of 2) *)
             MATCH_MP_TAC PAR3 \\
             EXISTS_TAC ``l: Label`` \\
             ASM_REWRITE_TAC [],
             (* goal 2.2.3.2 (of 2) *)
             take [`E1'''`, `E1''`, `E1''''`, `E2'''`] \\ 
             ASM_REWRITE_TAC [] ] ] ] ]);

(* Strong equivalence is substitutive under parallel operator on the right:
   |- !E E'. STRONG_EQUIV E E' ==> (!E''. STRONG_EQUIV (par E E'') (par E' E''))
 *)
val STRONG_EQUIV_SUBST_PAR_R = save_thm (
   "STRONG_EQUIV_SUBST_PAR_R",
      GEN_ALL
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
      GEN_ALL
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
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                       (ASSUME ``STRONG_EQUIV E1 E2``)) \\ 
          EXISTS_TAC ``restr L' E2'`` \\
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.1.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC RESTR \\
            REWRITE_TAC [REWRITE_RULE [ASSUME ``u = tau``]
                               (ASSUME ``TRANS E2 u E2'``)],
            (* goal 2.1.1.2 (of 2) *)
            take [`E''''`, `E2'`, `L'`] \\
            ASM_REWRITE_TAC [] ],
          (* goal 2.1.2 (of 2) *)
          IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
                       (ASSUME ``STRONG_EQUIV E1 E2``)) \\
          EXISTS_TAC ``restr L' E2'`` \\ 
          CONJ_TAC >| (* 2 sub-goals here *)
          [ (* goal 2.1.2.1 (of 2) *)
            ASM_REWRITE_TAC [] \\
            MATCH_MP_TAC RESTR \\
            EXISTS_TAC ``l: Label`` \\
            ASM_REWRITE_TAC [REWRITE_RULE [ASSUME ``u = label l``]
                                   (ASSUME ``TRANS E2 u E2'``)],
            (* goal 2.1.2.2 (of 2) *)
            take [`E''''`, `E2'`, `L'`] \\
            ASM_REWRITE_TAC [] ] ],  
          (* goal 2.2 (of 2) *)
          ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = restr L' E2``]
				   (ASSUME ``TRANS E''' u E2'``)) \\ 
          IMP_RES_TAC TRANS_RESTR >| (* 2 sub-goals here *)
          [ (* goal 2.2.1 (of 2) *)
            IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR
				  (ASSUME ``STRONG_EQUIV E1 E2``)) \\ 
            EXISTS_TAC ``restr L' E1'`` \\ 
            CONJ_TAC >| (* 2 sub-goals here *)
            [ (* goal 2.2.1.1 (of 2) *)
              ASM_REWRITE_TAC [] \\
              MATCH_MP_TAC RESTR \\
              REWRITE_TAC [REWRITE_RULE [ASSUME ``u = tau``]
					(ASSUME ``TRANS E1 u E1'``)],
              (* goal 2.2.1.2 (of 2) *)
              take [`E1'`, `E''''`, `L'`] \\
              ASM_REWRITE_TAC [] ],  
           (* goal 2.2.2 (of 2) *)
           IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
				 (ASSUME ``STRONG_EQUIV E1 E2``)) \\ 
           EXISTS_TAC ``restr L' E1'`` \\ 
           CONJ_TAC >| (* 2 sub-goals here *)
           [ (* goal 2.2.2.1 (of 2) *)
             ASM_REWRITE_TAC [] \\
             MATCH_MP_TAC RESTR \\
             EXISTS_TAC ``l: Label`` \\
             ASM_REWRITE_TAC [REWRITE_RULE [ASSUME ``u = label l``]
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
        IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR
			      (ASSUME ``STRONG_EQUIV E1 E2``)) \\
        EXISTS_TAC ``relab E2' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.1.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC RELAB \\
          PURE_ONCE_ASM_REWRITE_TAC [],
          (* goal 2.1.2 (of 2) *)
          take [`E''''`, `E2'`, `rf'`] \\
          ASM_REWRITE_TAC [] ],
        (* goal 2.2 (of 2) *)
        ASSUME_TAC (REWRITE_RULE [ASSUME ``E''' = relab E2 rf'``]
				 (ASSUME ``TRANS E''' u E2'``)) \\
        IMP_RES_TAC TRANS_RELAB \\ 
        IMP_RES_TAC (MATCH_MP PROPERTY_STAR_LR  
			      (ASSUME ``STRONG_EQUIV E1 E2``)) \\
        EXISTS_TAC ``relab E1' rf'`` \\
        CONJ_TAC >| (* 2 sub-goals here *)
        [ (* goal 2.2.1 (of 2) *)
          ASM_REWRITE_TAC [] \\
          MATCH_MP_TAC RELAB \\
          PURE_ONCE_ASM_REWRITE_TAC [],
          (* goal 2.2.2 (of 2) *)
          take [`E1'`, `E''''`, `rf'`] \\
          ASM_REWRITE_TAC [] ] ] ]);

(******************************************************************************)
(*                                                                            *)
(*   A new definition of STRONG_EQUIV based on HOL's coinductive relation     *)
(*                                                                            *)
(******************************************************************************)

(* Obsevations:
   1. STRONG_EQ_cases ==> STRONG_EQ_rules (by EQ_IMP_LR)
   2. STRONG_EQ_cases is the same as PROPERTY_STAR
   3. STRONG_EQ_coind is new (the co-induction principle)
 *)
val (STRONG_EQ_rules, STRONG_EQ_coind, STRONG_EQ_cases) = Hol_coreln `
    (!E E'.
       (!u.
         (!E1. TRANS E u E1 ==> 
               (?E2. TRANS E' u E2 /\ STRONG_EQ E1 E2)) /\
         (!E2. TRANS E' u E2 ==> 
               (?E1. TRANS E u E1 /\ STRONG_EQ E1 E2))) ==> STRONG_EQ E E')`;

(* Strong equivalence implies the new relation. *)
val STR_EQUIV_IMP_STR_EQ = store_thm (
   "STR_EQUIV_IMP_STR_EQ",
      ``!E E'. STRONG_EQUIV E E' ==> STRONG_EQ E E'``,
    HO_MATCH_MP_TAC STRONG_EQ_coind (* co-induction principle used here! *)
 >> REPEAT GEN_TAC
 >> PURE_ONCE_REWRITE_TAC [GSYM PROPERTY_STAR]
 >> RW_TAC bool_ss []);

val STR_EQ_IS_STR_BISIM = store_thm (
   "STR_EQ_IS_STR_BISIM",
  ``STRONG_BISIM STRONG_EQ``,
    PURE_ONCE_REWRITE_TAC [STRONG_BISIM]
 >> PURE_ONCE_REWRITE_TAC [GSYM STRONG_EQ_cases]
 >> RW_TAC bool_ss []);

(* The new relation implies strong equivalence. *)
val STR_EQ_IMP_STR_EQUIV = store_thm (
   "STR_EQ_IMP_STR_EQUIV",
      ``!E E'. STRONG_EQ E E' ==> STRONG_EQUIV E E'``,
    REPEAT STRIP_TAC
 >> PURE_ONCE_REWRITE_TAC [STRONG_EQUIV]
 >> EXISTS_TAC ``STRONG_EQ``
 >> ASM_REWRITE_TAC [STR_EQ_IS_STR_BISIM]);

(* Now we have equivalence theorem used for rewriting:
   |- ∀E E'. STRONG_EQ E E' ⇔ E ~~ E'
 *)
val STR_EQ_TO_STR_EQUIV = store_thm (
   "STR_EQ_TO_STR_EQUIV",
      ``!E E'. STRONG_EQ E E' = STRONG_EQUIV E E'``,
    REPEAT GEN_TAC
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ REWRITE_TAC [STR_EQ_IMP_STR_EQUIV],
      REWRITE_TAC [STR_EQUIV_IMP_STR_EQ] ]);

(* The other direction:
   |- ∀E E'. E ~~ E' ⇔ STRONG_EQ E E'
 *)
val STR_EQUIV_TO_STR_EQ = save_thm (
   "STR_EQUIV_TO_STR_EQ", GSYM STR_EQ_TO_STR_EQUIV);

(* The co-induction principle for STRONG_EQUIV, generated from STRONG_EQ_coind *)
val STRONG_EQUIV_coind = store_thm (
   "STRONG_EQUIV_coind",
  ``!R.
     (!E E'.
        R E E' ==>
        (!u.
          (!E1. TRANS E u E1 ==> ?E2. TRANS E' u E2 /\ R E1 E2) /\
          (!E2. TRANS E' u E2 ==> ?E1. TRANS E u E1 /\ R E1 E2))) ==>
      !E E'. R E E' ==> STRONG_EQUIV E E'``,
    REWRITE_TAC [STR_EQUIV_TO_STR_EQ]
 >> GEN_TAC
 >> DISCH_TAC
 >> HO_MATCH_MP_TAC STRONG_EQ_coind
 >> ASM_REWRITE_TAC []);

(******************************************************************************)
(*                                                                            *)
(*                Additional theorems of STRONG_EQUIV                         *)
(*                                                                            *)
(******************************************************************************)

val BIGUNION_BISIM_def = Define `
    BIGUNION_BISIM = CURRY (BIGUNION { UNCURRY R | STRONG_BISIM R })`;

(* STRONG_EQUIV is the union of all STRONG_BISIMs *)
val STRONG_EQUIV_IS_BIGUNION_BISIM = store_thm (
   "STRONG_EQUIV_IS_BIGUNION_BISIM",
  ``!E E'. STRONG_EQUIV E E' = BIGUNION_BISIM E E'``,
    REWRITE_TAC [BIGUNION_BISIM_def]
 >> REPEAT GEN_TAC
 >> REWRITE_TAC [CURRY_DEF]
 >> ONCE_REWRITE_RHS_TAC [GSYM SPECIFICATION]
 >> REWRITE_TAC [IN_BIGUNION]
 >> REWRITE_TAC [GSPECIFICATION]
 >> BETA_TAC
 >> REWRITE_TAC [PAIR_EQ]
 >> REWRITE_TAC [SPECIFICATION]
 >> REWRITE_TAC [STRONG_EQUIV]
 >> EQ_TAC (* 2 sub-goals here *)
 >| [ (* goal 1 (of 2) *)
      REPEAT STRIP_TAC \\
      EXISTS_TAC ``UNCURRY (Bsm :CCS -> CCS -> bool)`` \\
      REWRITE_TAC [UNCURRY] \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ ASM_REWRITE_TAC [],
        EXISTS_TAC ``(Bsm :CCS -> CCS -> bool)`` \\
        ASM_REWRITE_TAC [] ],
      (* goal 2 (of 2) *)
      REPEAT STRIP_TAC \\
      EXISTS_TAC ``x :CCS -> CCS -> bool`` \\
      CONJ_TAC >| (* 2 sub-goals here *)
      [ PAT_X_ASSUM ``(s :CCS # CCS -> bool) ((E :CCS), (E' :CCS))`` MP_TAC \\
        ASM_REWRITE_TAC [UNCURRY],
        ASM_REWRITE_TAC [] ] ]);

val STRONG_EQUIV_IS_BIGUNION_BISIM' = store_thm (
   "STRONG_EQUIV_IS_BIGUNION_BISIM'",
  ``STRONG_EQUIV = BIGUNION_BISIM``,
    REWRITE_TAC [FUN_EQ_THM, STRONG_EQUIV_IS_BIGUNION_BISIM]);

(* forward way: |- STRONG_EQUIV = BIGUNION_BISIM *)
val STRONG_EQUIV_IS_BIGUNION_BISIM'' = save_thm (
   "STRONG_EQUIV_IS_BIGUNION_BISIM''",
    EXT (GEN ``E: CCS``
	  (EXT (SPEC ``E: CCS`` STRONG_EQUIV_IS_BIGUNION_BISIM))));

val STRONG_EQUIV_EQ_BIGUNION_BISIM = store_thm (
   "STRONG_EQUIV_EQ_BIGUNION_BISIM",
  ``STRONG_EQUIV = CURRY (BIGUNION { UNCURRY R | STRONG_BISIM R })``,
    REWRITE_TAC [STRONG_EQUIV_IS_BIGUNION_BISIM'',
		 BIGUNION_BISIM_def]);

(* Define the strong bisimulation relation up to STRONG_EQUIV *)
val STRONG_BISIM_UPTO = new_definition (
   "STRONG_BISIM_UPTO",
  ``STRONG_BISIM_UPTO (Bsm: CCS -> CCS -> bool) =
       (!E E'.
          Bsm E E' ==>
          (!u.
           (!E1. TRANS E u E1 ==> 
                 ?E2. TRANS E' u E2 /\ (STRONG_EQUIV O Bsm O STRONG_EQUIV) E1 E2) /\
           (!E2. TRANS E' u E2 ==> 
                 ?E1. TRANS E u E1 /\ (STRONG_EQUIV O Bsm O STRONG_EQUIV) E1 E2)))``);

val _ = export_theory ();
val _ = DB.html_theory "StrongEQ";

(* last updated: May 14, 2017 *)
